"""Charged, bounded spatial reference buffers for causal dependency tasks.

Buffers contain dyadic pieces and finite endpoints, never one slot per temporal
stage. One scheduler owns the inventory; completed tasks release their buffers.
"""

from __future__ import annotations

from collections.abc import Iterable, Iterator
from sys import getsizeof
from typing import Any, Protocol

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict, LedgerList


class SpatialReferenceBuffer:
    __slots__ = ("workspace", "identity", "capacity", "used", "closed", "backing_bytes")

    def __init__(
        self, workspace: CausalSpatialWorkspace, identity: int, capacity: int
    ) -> None:
        self.workspace, self.identity = workspace, identity
        self.capacity = capacity
        self.used, self.closed = 0, False
        self.backing_bytes = getsizeof(self) + capacity * getsizeof((0, 0))

    def __len__(self) -> int:
        return self.used

    def __getitem__(self, index: int) -> Any:
        if self.closed:
            raise ValueError("closed spatial workspace buffer")
        if not 0 <= index < self.used:
            raise IndexError(index)
        return self.workspace._refs[self.identity, index]

    def __iter__(self) -> Iterator[Any]:
        for index in range(self.used):
            yield self[index]

    def append(self, value: Any) -> None:
        if self.closed or self.used == self.capacity:
            raise ValueError("closed or exhausted spatial workspace buffer")
        self.workspace._refs[self.identity, self.used] = value
        self.used += 1
        self.workspace.ledger.bump("tile_causal_spatial_buffer_appends")

    def reverse(self) -> None:
        if self.closed:
            raise ValueError("closed spatial workspace buffer")
        for left in range(self.used // 2):
            right = self.used - left - 1
            refs = self.workspace._refs
            a, b = (self.identity, left), (self.identity, right)
            refs[a], refs[b] = refs[b], refs[a]
        self.workspace.ledger.bump(
            "tile_causal_spatial_buffer_reversal_visits", self.used
        )

    def close(self) -> None:
        self.workspace.release(self)


class CausalSpatialWorkspace:
    """One inventory for all live spatial buffers, including unused capacity."""

    def __init__(self, ledger: ResourceLedger, prefix: str) -> None:
        self.ledger = ledger
        self.owner = ledger.register(
            prefix + "-spatial-workspace", "causal_spatial_workspace"
        )
        self.buffer_owner = ledger.register(
            prefix + "-spatial-buffers", "causal_spatial_workspace"
        )
        self._buffers: LedgerDict[int, SpatialReferenceBuffer] = ledger.make_dict(
            self.buffer_owner,
            nodes_per_entry=1,
        )
        self._refs: LedgerDict[tuple[int, int], Any] = ledger.make_dict(self.owner)
        self._next = 0
        self.slots = self._object_bytes = 0

    def __len__(self) -> int:
        return self.slots

    @property
    def backing_bytes(self) -> int:
        return (
            self._object_bytes
            + getsizeof(self._refs._data)
            + getsizeof(self._buffers._data)
        )

    def payloads(self) -> Iterator[object]:
        yield from self._refs.values()

    def allocate(self, capacity: int) -> SpatialReferenceBuffer:
        if type(capacity) is not int or capacity < 0:
            raise ValueError(
                "spatial reference capacity requires a nonnegative integer"
            )
        self.ledger.reserve_many(((self.owner, capacity, 0), (self.buffer_owner, 1, 1)))
        old_tables = (getsizeof(self._refs._data), getsizeof(self._buffers._data))
        identity = self._next
        self._next += 1
        try:
            buffer = SpatialReferenceBuffer(self, identity, capacity)
            self._buffers[identity] = buffer
            for index in range(capacity):
                self._refs[identity, index] = None
        except BaseException:
            for index in range(capacity):
                self._refs.pop((identity, index), None)
            self._buffers.pop(identity, None)
            self.ledger.release(self.owner, entries=capacity)
            self.ledger.release(self.buffer_owner, entries=1, nodes=1)
            raise
        self.slots += capacity
        self._object_bytes += buffer.backing_bytes
        self.ledger.note_store_mutation()
        self.ledger.bump("tile_causal_spatial_buffer_allocations")
        new_tables = (getsizeof(self._refs._data), getsizeof(self._buffers._data))
        self.ledger.bump(
            "tile_causal_spatial_buffer_allocated_bytes",
            buffer.backing_bytes
            + sum(
                new
                for old, new in zip(old_tables, new_tables, strict=True)
                if new != old
            ),
        )
        for name, value in (("slots", self.slots), ("bytes", self.backing_bytes)):
            counter = "tile_causal_spatial_buffer_peak_" + name
            self.ledger.bump(
                counter, max(0, value - self.ledger.counters.get(counter, 0))
            )
        return buffer

    def release(self, buffer: SpatialReferenceBuffer) -> None:
        if buffer.workspace is not self:
            raise ValueError("foreign spatial workspace buffer")
        if buffer.closed:
            return
        if self._buffers.get(buffer.identity) is not buffer:
            raise ValueError("stale spatial workspace buffer")
        charge = buffer.capacity
        del self._buffers[buffer.identity]
        self.slots -= charge
        self._object_bytes -= buffer.backing_bytes
        for index in range(buffer.capacity):
            del self._refs[buffer.identity, index]
        buffer.used, buffer.closed = 0, True
        if not self._buffers:
            self._buffers.clear()
            self._refs.clear()
        self.ledger.release(self.owner, entries=charge)
        self.ledger.release(self.buffer_owner, entries=1, nodes=1)
        self.ledger.note_store_mutation()

    def clear(self) -> None:
        while self._buffers:
            self.release(next(iter(self._buffers.values())))


class CausalTaskWorkspace:
    """Query-scoped memo and active dependency set under one scheduler owner.

    Canonical results have their own lifetime. These entries are released at the
    end of the observation, including exceptional exits and held width scopes.
    """

    def __init__(self, ledger: ResourceLedger, prefix: str) -> None:
        self.ledger = ledger
        self.memo_owner = ledger.register(
            prefix + "-task-memo", "causal_task_workspace"
        )
        self.active_owner = ledger.register(
            prefix + "-task-active", "causal_task_workspace"
        )
        self.memo: LedgerDict[tuple[str, tuple[Any, ...]], Any] = ledger.make_dict(
            self.memo_owner
        )
        self.active: LedgerDict[tuple[str, tuple[Any, ...]], bool] = ledger.make_dict(
            self.active_owner
        )
        self.frames = CausalFrameStack(ledger, prefix)
        self.values = CausalResultStack(ledger, prefix)
        self.directed_frames = CausalFrameStack(ledger, prefix + "-directed")
        self.directed_values = CausalValueStack(ledger, prefix + "-directed")

    def begin(self, key: tuple[str, tuple[Any, ...]]) -> None:
        if key in self.active:
            raise ValueError("causal task dependency contains a cycle")
        self.ledger.reserve(self.active_owner, entries=1)
        try:
            self.active[key] = True
        except BaseException:
            self.ledger.release(self.active_owner, entries=1)
            raise

    def finish(self, key: tuple[str, tuple[Any, ...]], value: Any) -> None:
        if key not in self.active or key in self.memo:
            raise ValueError("causal task completion has no unique active dependency")
        self.ledger.reserve(self.memo_owner, entries=1)
        try:
            self.memo[key] = value
        except BaseException:
            self.ledger.release(self.memo_owner, entries=1)
            raise
        del self.active[key]
        self.ledger.release(self.active_owner, entries=1)

    def clear(self) -> None:
        for owner, store in (
            (self.memo_owner, self.memo),
            (self.active_owner, self.active),
        ):
            count = len(store)
            store.clear()
            self.ledger.release(owner, entries=count)
        self.frames.clear()
        self.values.clear()
        self.directed_frames.clear()
        self.directed_values.clear()


class CausalFrameStack:
    """Budgeted task stack with incremental direct payload-reference peaks.

    Reference counts are slots, not unique objects or bytes. Aliased tuple backing
    is deliberately not relabeled a unique allocation. Spatial arrays are charged
    by CausalSpatialWorkspace instead of being hidden inside a single frame slot.
    """

    def __init__(self, ledger: ResourceLedger, prefix: str) -> None:
        self.ledger = ledger
        self.owner = ledger.register(prefix + "-task-frames", "causal_task_workspace")
        self._frames: LedgerList[Any] = ledger.make_list(
            self.owner, nodes_per_entry=0, append_only=False
        )
        self.payload_references = 0

    def __len__(self) -> int:
        return len(self._frames)

    def append(self, frame: Any) -> None:
        references = len(frame.args) + len(frame.saved)
        self.ledger.reserve(self.owner, entries=1)
        try:
            self._frames.append(frame)
        except BaseException:
            self.ledger.release(self.owner, entries=1)
            raise
        self.payload_references += references
        self.ledger.bump("tile_causal_frame_publications")
        self.ledger.bump("tile_causal_frame_payload_reference_publications", references)
        for counter, value in (
            ("tile_causal_frame_peak_slots", len(self)),
            ("tile_causal_frame_payload_reference_peak", self.payload_references),
            (
                "tile_causal_frame_stack_backing_peak_bytes",
                getsizeof(self._frames._data),
            ),
        ):
            self.ledger.bump(
                counter, max(0, value - self.ledger.counters.get(counter, 0))
            )

    def extend(self, frames: Iterable[Any]) -> None:
        for frame in frames:
            self.append(frame)

    def pop(self) -> Any:
        frame = self._frames.pop()
        self.payload_references -= len(frame.args) + len(frame.saved)
        self.ledger.release(self.owner, entries=1)
        return frame

    def clear(self) -> None:
        count = len(self._frames)
        self._frames.clear()
        self.payload_references = 0
        self.ledger.release(self.owner, entries=count)


class CausalResults(Protocol):
    """Minimal result interface shared by scheduler tasks and isolated tests."""

    def append(self, value: Any) -> None: ...

    def pop(self) -> Any: ...


class CausalResultStack:
    """Charged transient result references; payload owners remain separate."""

    def __init__(self, ledger: ResourceLedger, prefix: str) -> None:
        self.ledger = ledger
        self.owner = ledger.register(prefix + "-result-values", "causal_task_workspace")
        self._values: LedgerList[Any] = ledger.make_list(
            self.owner, nodes_per_entry=0, append_only=False
        )

    def __len__(self) -> int:
        return len(self._values)

    def append(self, value: Any) -> None:
        self.ledger.reserve(self.owner, entries=1)
        try:
            self._values.append(value)
        except BaseException:
            self.ledger.release(self.owner, entries=1)
            raise
        self.ledger.bump("tile_causal_result_value_publications")
        for name, count in (
            ("slots", len(self)),
            ("backing_bytes", getsizeof(self._values._data)),
        ):
            counter = "tile_causal_result_value_peak_" + name
            self.ledger.bump(
                counter, max(0, count - self.ledger.counters.get(counter, 0))
            )

    def pop(self) -> Any:
        value = self._values.pop()
        self.ledger.release(self.owner, entries=1)
        return value

    def clear(self) -> None:
        count = len(self._values)
        self._values.clear()
        self.ledger.release(self.owner, entries=count)


class CausalValueStack:
    """Budgeted scalar results for the auxiliary directed-transfer stack."""

    def __init__(self, ledger: ResourceLedger, prefix: str) -> None:
        self.ledger = ledger
        self.owner = ledger.register(prefix + "-task-values", "causal_task_workspace")
        self._values: LedgerList[int] = ledger.make_list(
            self.owner,
            nodes_per_entry=0,
            append_only=False,
        )

    def __len__(self) -> int:
        return len(self._values)

    def append(self, value: int) -> None:
        if type(value) is not int:
            raise TypeError("causal directed value requires an exact integer")
        self.ledger.reserve(self.owner, entries=1)
        try:
            self._values.append(value)
        except BaseException:
            self.ledger.release(self.owner, entries=1)
            raise
        self.ledger.bump("tile_directed_transfer_value_publications")
        peak = self.ledger.counters.get("tile_directed_transfer_value_peak_slots", 0)
        if len(self) > peak:
            self.ledger.bump(
                "tile_directed_transfer_value_peak_slots", len(self) - peak
            )

    def pop(self) -> int:
        value = self._values.pop()
        self.ledger.release(self.owner, entries=1)
        return value

    def clear(self) -> None:
        count = len(self._values)
        self._values.clear()
        self.ledger.release(self.owner, entries=count)

"""Charged query workspace for iterative fused-interface traversal."""

from __future__ import annotations

from collections.abc import Iterator
from contextlib import contextmanager
from sys import getsizeof

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import resources as _resources_keys
from number_compiler.resources.metric_keys import shared as _shared_keys
from number_compiler.resources.stores import LedgerList


def fused_traversal_workspace_owner_names(
    prefix: str,
) -> tuple[str, str, str]:
    """Return the three distinct ledger names owned by one workspace."""
    if type(prefix) is not str:
        raise TypeError("fused traversal owner prefix must be a string")
    return (
        prefix + "-fused-workspace",
        prefix + "-fused-frames",
        prefix + "-fused-values",
    )


class FusedTraversalWorkspace:
    """Own visible O(depth) frame and result stacks for one fused query."""

    def __init__(self, ledger: ResourceLedger, prefix: str) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("fused traversal workspace requires one resource ledger")
        self.ledger = ledger
        owner_names = fused_traversal_workspace_owner_names(prefix)
        ledger.require_fresh_owner_names(owner_names)
        self.owner = ledger.register(owner_names[0], "fused_interface_workspace")
        self.frame_owner = ledger.register(owner_names[1], "fused_interface_workspace")
        self.value_owner = ledger.register(owner_names[2], "fused_interface_workspace")
        self.frames: LedgerList[object] = ledger.make_list(
            self.frame_owner, nodes_per_entry=0, append_only=False
        )
        self.values: LedgerList[object] = ledger.make_list(
            self.value_owner, nodes_per_entry=0, append_only=False
        )
        self.nodes = 0
        self.active = False
        self._disposed = False
        self.max_frames = 0
        self.max_values = 0
        ledger.register_container(
            self.owner,
            self,
            node_count=lambda: self.nodes,
            payloads=lambda: (),
        )

    def __len__(self) -> int:
        return 0

    def _check_open(self) -> None:
        if self._disposed:
            raise RuntimeError("fused traversal workspace has been disposed")

    def _append(self, owner: int, store: LedgerList[object], value: object) -> None:
        prior_size = len(store)
        self.ledger.reserve(owner, entries=1)
        try:
            store.append(value)
        except BaseException:
            if len(store) != prior_size:
                store._rollback_unpublished(prior_size)
            self.ledger.release(owner, entries=1)
            raise
        count = len(self.frames) + len(self.values)
        peak = self.ledger.counters.get(_shared_keys.TILE_FUSED_WORKSPACE_PEAK, 0)
        if count > peak:
            self.ledger.bump(_shared_keys.TILE_FUSED_WORKSPACE_PEAK, count - peak)
        backing = getsizeof(self.frames._data) + getsizeof(self.values._data)
        old_backing = self.ledger.counters.get(
            _resources_keys.TILE_FUSED_WORKSPACE_BACKING_PEAK_BYTES, 0
        )
        if backing > old_backing:
            self.ledger.bump(
                _resources_keys.TILE_FUSED_WORKSPACE_BACKING_PEAK_BYTES,
                backing - old_backing,
            )

    def append_frame(self, value: object) -> None:
        self._check_open()
        if not self.active:
            raise RuntimeError("fused traversal frame requires an active scope")
        if len(self.frames) >= self.max_frames:
            raise RuntimeError("fused traversal exceeded its frame bound")
        self._append(self.frame_owner, self.frames, value)

    def append_value(self, value: object) -> None:
        self._check_open()
        if not self.active:
            raise RuntimeError("fused traversal value requires an active scope")
        if len(self.values) >= self.max_values:
            raise RuntimeError("fused traversal exceeded its value bound")
        self._append(self.value_owner, self.values, value)

    def _pop(self, owner: int, store: LedgerList[object]) -> object:
        self._check_open()
        prior_size = len(store)
        value = store[-1]
        try:
            store.pop()
        except BaseException:
            if len(store) != prior_size:
                store.append(value)
            raise
        self.ledger.release(owner, entries=1)
        return value

    def pop_frame(self) -> object:
        return self._pop(self.frame_owner, self.frames)

    def pop_value(self) -> object:
        return self._pop(self.value_owner, self.values)

    @contextmanager
    def scope(self, level: int, port_count: int) -> Iterator[None]:
        self._check_open()
        if any(type(value) is not int for value in (level, port_count)):
            raise TypeError("fused traversal bounds require exact integers")
        if level < 0 or port_count < 0:
            raise ValueError("fused traversal bounds must be nonnegative")
        if self.active or self.nodes or self.frames or self.values:
            raise RuntimeError("fused traversal workspace is already active")
        # At depth d there are at most 2d+1 frames and d+1 result values.
        # A frame owns one list reference, three tuple fields, one ports tuple,
        # and that tuple's finite values.  A result owns its list reference and
        # ID.  The final term covers the two child contexts and one request key
        # that exist transiently while a parent is expanded or published.
        frame_slots = (2 * level + 1) * (port_count + 5)
        value_slots = 2 * (level + 1)
        transient_slots = 4 * port_count + 32
        nodes = frame_slots + value_slots + transient_slots
        self.ledger.reserve(self.owner, nodes=nodes)
        try:
            self.nodes, self.active = nodes, True
            self.max_frames, self.max_values = 2 * level + 1, level + 1
            peak = self.ledger.counters.get(
                _resources_keys.TILE_FUSED_WORKSPACE_RESERVED_REFERENCE_PEAK, 0
            )
            if nodes > peak:
                self.ledger.bump(
                    _resources_keys.TILE_FUSED_WORKSPACE_RESERVED_REFERENCE_PEAK,
                    nodes - peak,
                )
            yield
        finally:
            frame_count = len(self.frames)
            self.frames.clear()
            self.ledger.release(self.frame_owner, entries=frame_count)

            value_count = len(self.values)
            self.values.clear()
            self.ledger.release(self.value_owner, entries=value_count)
            self.active = False
            self.nodes = 0
            self.max_frames = self.max_values = 0
            self.ledger.release(self.owner, nodes=nodes)

    def dispose(self) -> None:
        """Close the three auditable owners after all scoped work is cleared."""
        if self._disposed:
            return
        if self.active or self.nodes:
            raise RuntimeError("cannot dispose an active fused traversal workspace")
        frame_count = len(self.frames)
        self.frames.clear()
        self.ledger.release(self.frame_owner, entries=frame_count)

        value_count = len(self.values)
        self.values.clear()
        self.ledger.release(self.value_owner, entries=value_count)
        self.ledger.mark_disposed(self.frame_owner)
        self.ledger.mark_disposed(self.value_owner)
        self.ledger.mark_disposed(self.owner)
        self._disposed = True


__all__ = ["FusedTraversalWorkspace", "fused_traversal_workspace_owner_names"]

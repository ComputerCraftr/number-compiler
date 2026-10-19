"""Charged transient task stacks owned by a causal scheduler."""

from __future__ import annotations

from collections.abc import Callable, Iterable
from typing import Generic, Protocol, TypeVar

from number_compiler.resources.causal_audit_contracts import CausalStackAuditSnapshot
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.lifecycle import clear_accounted_store
from number_compiler.resources.metric_keys import resources as _resources_keys
from number_compiler.resources.stores import LedgerList


class AccountedStore(Protocol):
    """Small common surface needed to release an accounted store."""

    nodes_per_entry: int

    def __len__(self) -> int: ...

    def clear(self) -> None: ...


def clear_owned_store(
    ledger: ResourceLedger,
    owner: int,
    store: AccountedStore,
    retry: StoreClearRetry,
    after_clear: Callable[[], object] | None = None,
) -> None:
    """Clear an exact store delta, retaining failed release work for retry."""

    def clear_store() -> None:
        try:
            store.clear()
        finally:
            if after_clear is not None:
                after_clear()

    def measure() -> tuple[int, int]:
        entries = len(store)
        return entries, entries * store.nodes_per_entry

    clear_accounted_store(
        ledger,
        owner,
        clear_store,
        measure,
        retry.pending,
        retry.record,
    )


class StoreClearRetry:
    """Per-store retry deltas; never inferred from unrelated owner charges."""

    __slots__ = ("pending",)

    def __init__(self) -> None:
        self.pending = (0, 0)

    def record(self, entries: int, nodes: int) -> None:
        self.pending = entries, nodes


class _FrameAccounting(Protocol):
    """Frame-owned count of direct argument and saved-value references."""

    def payload_reference_count(self) -> int: ...


FrameT = TypeVar("FrameT", bound=_FrameAccounting)
ResultValueT = TypeVar("ResultValueT")


class CausalFrameStack(Generic[FrameT]):
    """Budgeted task stack with incremental direct payload-reference peaks.

    Reference counts are slots, not unique objects or bytes. Aliased tuple backing
    is deliberately not relabeled a unique allocation. Spatial arrays are charged
    by CausalSpatialWorkspace instead of being hidden inside a single frame slot.
    """

    def __init__(self, ledger: ResourceLedger, prefix: str) -> None:
        self.ledger = ledger
        self.owner = ledger.register(prefix + "-task-frames", "causal_task_workspace")
        self._frames: LedgerList[FrameT] = ledger.make_list(
            self.owner, nodes_per_entry=0, append_only=False
        )
        self.payload_references = 0
        self._clear_retry = StoreClearRetry()

    def __len__(self) -> int:
        return len(self._frames)

    def audit_snapshot(self) -> CausalStackAuditSnapshot[FrameT]:
        """Return the retained frames and exact registered sequence wrapper."""
        return CausalStackAuditSnapshot(
            owner=self.owner,
            store=self._frames,
            values=self._frames.snapshot(),
            payload_references=self.payload_references,
        )

    def append(self, frame: FrameT) -> None:
        references = frame.payload_reference_count()
        self.ledger.reserve(self.owner, entries=1)
        try:
            self._frames.append(frame)
        except BaseException:
            self.ledger.release(self.owner, entries=1)
            raise
        self.payload_references += references
        self.ledger.bump(_resources_keys.TILE_CAUSAL_FRAME_PUBLICATIONS)
        self.ledger.bump(
            _resources_keys.TILE_CAUSAL_FRAME_PAYLOAD_REFERENCE_PUBLICATIONS,
            references,
        )
        for counter, value in (
            ("tile_causal_frame_peak_slots", len(self)),
            ("tile_causal_frame_payload_reference_peak", self.payload_references),
            (
                "tile_causal_frame_stack_backing_peak_bytes",
                self._frames.backing_bytes,
            ),
        ):
            self.ledger.bump(
                counter, max(0, value - self.ledger.counters.get(counter, 0))
            )

    def extend(self, frames: Iterable[FrameT]) -> None:
        for frame in frames:
            self.append(frame)

    def pop(self) -> FrameT:
        frame = self._frames.pop()
        self.payload_references -= frame.payload_reference_count()
        self.ledger.release(self.owner, entries=1)
        return frame

    def clear(self) -> None:
        def update_payload_references() -> None:
            self.payload_references = sum(
                frame.payload_reference_count() for frame in self._frames
            )

        clear_owned_store(
            self.ledger,
            self.owner,
            self._frames,
            self._clear_retry,
            update_payload_references,
        )


class CausalResults(Protocol[ResultValueT]):
    """Minimal result interface shared by scheduler tasks and isolated tests."""

    def append(self, value: ResultValueT, /) -> None: ...

    def pop(self) -> ResultValueT: ...


class CausalResultStack(Generic[ResultValueT]):
    """Charged transient result references; payload owners remain separate."""

    def __init__(self, ledger: ResourceLedger, prefix: str) -> None:
        self.ledger = ledger
        self.owner = ledger.register(prefix + "-result-values", "causal_task_workspace")
        self._values: LedgerList[ResultValueT] = ledger.make_list(
            self.owner, nodes_per_entry=0, append_only=False
        )
        self._clear_retry = StoreClearRetry()

    def __len__(self) -> int:
        return len(self._values)

    def audit_snapshot(self) -> CausalStackAuditSnapshot[ResultValueT]:
        """Return the retained results and exact registered sequence wrapper."""
        return CausalStackAuditSnapshot(
            owner=self.owner,
            store=self._values,
            values=self._values.snapshot(),
            payload_references=None,
        )

    def append(self, value: ResultValueT) -> None:
        self.ledger.reserve(self.owner, entries=1)
        try:
            self._values.append(value)
        except BaseException:
            self.ledger.release(self.owner, entries=1)
            raise
        self.ledger.bump(_resources_keys.TILE_CAUSAL_RESULT_VALUE_PUBLICATIONS)
        for name, count in (
            ("slots", len(self)),
            ("backing_bytes", self._values.backing_bytes),
        ):
            counter = "tile_causal_result_value_peak_" + name
            self.ledger.bump(
                counter, max(0, count - self.ledger.counters.get(counter, 0))
            )

    def pop(self) -> ResultValueT:
        value = self._values.pop()
        self.ledger.release(self.owner, entries=1)
        return value

    def clear(self) -> None:
        clear_owned_store(self.ledger, self.owner, self._values, self._clear_retry)


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
        self._clear_retry = StoreClearRetry()

    def __len__(self) -> int:
        return len(self._values)

    def audit_snapshot(self) -> CausalStackAuditSnapshot[int]:
        """Return directed-transfer scalar values and their registered store."""
        return CausalStackAuditSnapshot(
            owner=self.owner,
            store=self._values,
            values=self._values.snapshot(),
            payload_references=None,
        )

    def append(self, value: int) -> None:
        if type(value) is not int:
            raise TypeError("causal directed value requires an exact integer")
        self.ledger.reserve(self.owner, entries=1)
        try:
            self._values.append(value)
        except BaseException:
            self.ledger.release(self.owner, entries=1)
            raise
        self.ledger.bump(_resources_keys.TILE_DIRECTED_TRANSFER_VALUE_PUBLICATIONS)
        peak = self.ledger.counters.get(
            _resources_keys.TILE_DIRECTED_TRANSFER_VALUE_PEAK_SLOTS, 0
        )
        if len(self) > peak:
            self.ledger.bump(
                _resources_keys.TILE_DIRECTED_TRANSFER_VALUE_PEAK_SLOTS,
                len(self) - peak,
            )

    def pop(self) -> int:
        value = self._values.pop()
        self.ledger.release(self.owner, entries=1)
        return value

    def clear(self) -> None:
        clear_owned_store(self.ledger, self.owner, self._values, self._clear_retry)


__all__ = [
    "AccountedStore",
    "CausalFrameStack",
    "CausalResultStack",
    "CausalResults",
    "CausalValueStack",
    "StoreClearRetry",
    "clear_owned_store",
]

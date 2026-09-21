"""Charged, bounded spatial reference buffers for causal dependency tasks.

Buffers contain dyadic pieces and finite endpoints, never one slot per temporal
stage. One scheduler owns the inventory; completed tasks release their buffers.
"""

from __future__ import annotations

from collections.abc import Iterable, Iterator
from sys import getsizeof
from typing import TYPE_CHECKING, Any, Protocol

from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaHandle,
)
from number_compiler.arithmetic.polynomials.frobenius_sector import (
    FrobeniusSectorSourceBound,
    ReverseFrobeniusPlan,
)
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.actions.tile_action_algebra import PrimitiveTileAction
from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict, LedgerList

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )


_ACTION_ADMISSION_SEAL = object()
_ACTION_ADMISSION_SNAPSHOT_SIZE = 51
_ACTION_ADMISSION_NODES = 1 + _ACTION_ADMISSION_SNAPSHOT_SIZE


def _handle_snapshot(handle: ArenaHandle) -> tuple[object, object, object]:
    return id(handle.owner), handle.kind, handle.local_id


def _action_admission_snapshot(
    action: FieldCellActionID,
    record: PrimitiveTileAction,
) -> tuple[object, ...]:
    """Detach every action field consumed under run admission."""
    if type(record) is not PrimitiveTileAction:
        raise TypeError("causal action admission requires a primitive action record")
    if (
        type(action) is not FieldCellActionID
        or type(record.kernel) is not ActionProgramID
        or type(record.signature) is not PortSignatureID
        or type(record.cocycle) is not TemporalCocycle
    ):
        raise TypeError("causal action admission has another metadata sort")
    children = record.children
    child_fields: tuple[object, ...]
    if children is None:
        child_fields = (0, None, None, None, None, None, None)
    else:
        if type(children) is not tuple or len(children) != 2:
            raise TypeError("causal action admission requires binary children")
        if (
            type(children[0]) is not FieldCellActionID
            or type(children[1]) is not FieldCellActionID
        ):
            raise TypeError("causal action admission has another child sort")
        child_fields = (
            1,
            *_handle_snapshot(children[0]),
            *_handle_snapshot(children[1]),
        )
    plan = record.reverse_frobenius
    plan_fields: tuple[object, ...]
    if plan is None:
        plan_fields = (0,) * 26
    else:
        if type(plan) is not ReverseFrobeniusPlan:
            raise TypeError("causal action admission has another reverse plan sort")
        if type(plan.sectors) is not tuple:
            raise TypeError(
                "causal action admission requires immutable reverse sectors"
            )
        if len(plan.sectors) != 4:
            raise ValueError("causal action admission requires four reverse sectors")
        sector_fields: list[object] = []
        for sector in plan.sectors:
            if type(sector) is not FrobeniusSectorSourceBound:
                raise TypeError("causal action admission has another sector sort")
            sector_fields.extend(
                (
                    sector.classes,
                    sector.bits,
                    sector.steps,
                    sector.uniform_no_growth_lower_bound,
                    sector.valuation_lower_bound,
                )
            )
        plan_fields = (
            1,
            plan.maximum_classes,
            plan.bits,
            plan.steps,
            id(plan.growth_certificate),
            len(plan.sectors),
            *sector_fields,
        )
    snapshot = (
        *_handle_snapshot(action),
        *_handle_snapshot(record.kernel),
        *_handle_snapshot(record.signature),
        *child_fields,
        record.cocycle.physical_ticks,
        record.cocycle.event_weight,
        record.cocycle.frame_shift,
        record.repetitions,
        record.homogeneous,
        record.spatial_events_add,
        record.blank_left_tail,
        record.blank_right_tail,
        record.stable_blank_output,
        *plan_fields,
    )
    if len(snapshot) != _ACTION_ADMISSION_SNAPSHOT_SIZE:
        raise RuntimeError("causal action admission snapshot schema is inconsistent")
    return snapshot


def _action_admission_matches(
    retained: tuple[object, ...],
    current: tuple[object, ...],
) -> bool:
    """Compare snapshots without Python's bool/integer equality aliases."""
    return (
        tuple(map(type, retained)) == tuple(map(type, current)) and retained == current
    )


class CausalActionAdmission:
    """Unforgeable lease for one deeply admitted causal action DAG."""

    __slots__ = ("_run", "_seal", "_workspace")

    def __init__(self, workspace: CausalTaskWorkspace, run: object) -> None:
        self._workspace = workspace
        self._run = run
        self._seal = _ACTION_ADMISSION_SEAL


def admitted_action_metadata(
    admission: object,
    authority: object,
    action: FieldCellActionID,
) -> tuple[PortSignatureID, ActionProgramID, PrimitiveTileAction]:
    """Authenticate an action through its exact live causal-run admission."""
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )

    if type(admission) is not CausalActionAdmission:
        raise TypeError("causal action admission has another lease sort")
    if admission._seal is not _ACTION_ADMISSION_SEAL:
        raise ValueError("causal action admission seal is invalid")
    if type(authority) is not PrimitiveTileKernelAdapter:
        raise TypeError("causal action admission requires its primitive authority")
    return admission._workspace.admitted_action_metadata(admission, authority, action)


class _CausalRunLease:
    __slots__ = ()


class SpatialReferenceBuffer:
    __slots__ = ("backing_bytes", "capacity", "closed", "identity", "used", "workspace")

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
        self.action_pending_owner = ledger.register(
            prefix + "-action-pending", "causal_task_workspace"
        )
        self.action_admitted_owner = ledger.register(
            prefix + "-action-admitted", "causal_task_workspace"
        )
        self.action_pending: LedgerList[FieldCellActionID] = ledger.make_list(
            self.action_pending_owner, nodes_per_entry=1, append_only=False
        )
        self.action_admitted: LedgerDict[FieldCellActionID, tuple[object, ...]] = (
            ledger.make_dict(
                self.action_admitted_owner,
                nodes_per_entry=_ACTION_ADMISSION_NODES,
            )
        )
        self._action_admission_token: object | None = None
        self._issued_action_admission_token: object | None = None
        self._run_token: object | None = None
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

    def begin_run(self) -> object:
        if self._run_token is not None:
            raise RuntimeError("causal task workspace already has an active run")
        token = _CausalRunLease()
        self._run_token = token
        return token

    def end_run(self, token: object) -> None:
        if self._run_token is not token:
            raise RuntimeError("causal task run lease is not active")
        self._run_token = None

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

    def begin_action_admission(self, action: FieldCellActionID) -> object:
        if (
            self._action_admission_token is not None
            or self._issued_action_admission_token is not None
            or self.action_pending
            or self.action_admitted
        ):
            raise RuntimeError("causal action admission is already active")
        run = self._run_token
        if type(run) is not _CausalRunLease:
            raise RuntimeError("causal action admission requires an active run")
        token = CausalActionAdmission(self, run)
        self._action_admission_token = token
        self._issued_action_admission_token = token
        try:
            self.push_action(token, action)
        except BaseException:
            self._action_admission_token = None
            self._issued_action_admission_token = None
            raise
        return token

    def _require_action_admission(self, token: object) -> None:
        if not self.owns_action_admission(token):
            raise RuntimeError("causal action admission lease is not active")

    def valid_action_admission_state(self) -> bool:
        token = self._action_admission_token
        run = self._run_token
        return (run is None or type(run) is _CausalRunLease) and (
            (token is not None and self.owns_action_admission(token))
            or (
                token is None
                and self._issued_action_admission_token is None
                and not self.action_pending
                and not self.action_admitted
            )
        )

    def owns_action_admission(self, admission: object) -> bool:
        """Recognize only this workspace's exact live run admission lease."""
        return (
            type(admission) is CausalActionAdmission
            and admission._seal is _ACTION_ADMISSION_SEAL
            and admission._workspace is self
            and admission._run is self._run_token
            and admission is self._action_admission_token
            and admission is self._issued_action_admission_token
            and type(self._run_token) is _CausalRunLease
        )

    def push_action(self, token: object, action: FieldCellActionID) -> None:
        self._require_action_admission(token)
        self.ledger.reserve(self.action_pending_owner, entries=1, nodes=1)
        try:
            self.action_pending.append(action)
        except BaseException:
            self.ledger.release(self.action_pending_owner, entries=1, nodes=1)
            raise

    def pop_action(self, token: object) -> FieldCellActionID:
        self._require_action_admission(token)
        action = self.action_pending.pop()
        self.ledger.release(self.action_pending_owner, entries=1, nodes=1)
        return action

    def action_is_admitted(self, token: object, action: FieldCellActionID) -> bool:
        self._require_action_admission(token)
        return action in self.action_admitted

    def admit_action(
        self,
        token: object,
        action: FieldCellActionID,
        record: PrimitiveTileAction,
    ) -> None:
        self._require_action_admission(token)
        if action in self.action_admitted:
            return
        snapshot = _action_admission_snapshot(action, record)
        self.ledger.reserve(
            self.action_admitted_owner,
            entries=1,
            nodes=_ACTION_ADMISSION_NODES,
        )
        try:
            self.action_admitted[action] = snapshot
        except BaseException:
            self.ledger.release(
                self.action_admitted_owner,
                entries=1,
                nodes=_ACTION_ADMISSION_NODES,
            )
            raise

    def admitted_action_snapshot(
        self,
        token: object,
        action: FieldCellActionID,
    ) -> tuple[object, ...]:
        """Return a detached snapshot only for the exact active run lease."""
        self._require_action_admission(token)
        if type(token) is not CausalActionAdmission:
            raise TypeError("causal action admission has another lease sort")
        if (
            token._seal is not _ACTION_ADMISSION_SEAL
            or token._workspace is not self
            or token._run is not self._run_token
        ):
            raise ValueError("causal action admission belongs to another run")
        if type(action) is not FieldCellActionID:
            raise TypeError("causal action admission requires a field action ID")
        try:
            snapshot = self.action_admitted[action]
        except KeyError:
            raise ValueError("action is outside this run's admitted DAG") from None
        if (
            type(snapshot) is not tuple
            or len(snapshot) != _ACTION_ADMISSION_SNAPSHOT_SIZE
        ):
            raise ValueError("causal action admission snapshot is malformed")
        if not _action_admission_matches(snapshot[:3], _handle_snapshot(action)):
            raise ValueError("causal action admission handle changed")
        return snapshot

    def admitted_action_metadata(
        self,
        token: object,
        authority: PrimitiveTileKernelAdapter,
        action: FieldCellActionID,
    ) -> tuple[PortSignatureID, ActionProgramID, PrimitiveTileAction]:
        """Validate current structural metadata against its detached admission."""
        from number_compiler.hashlife.execution.tile_kernel import (
            PrimitiveTileKernelAdapter,
        )

        if type(authority) is not PrimitiveTileKernelAdapter:
            raise TypeError("causal action admission requires its primitive authority")
        if type(action) is not FieldCellActionID:
            raise TypeError("causal action admission requires a field action ID")
        action.validate(
            authority.owner, "field-cell-action", size=authority._next_action
        )
        snapshot = self.admitted_action_snapshot(token, action)
        self.ledger.bump("tile_causal_action_admitted_metadata_visits")
        try:
            record = authority._actions[action.local_id]
        except KeyError:
            raise ValueError("stale or unpublished primitive tile action") from None
        if type(record) is not PrimitiveTileAction:
            raise TypeError("primitive action store contains another record sort")
        signature = record.signature
        if not _action_admission_matches(
            snapshot,
            _action_admission_snapshot(action, record),
        ):
            raise ValueError("causal action metadata changed after admission")
        authority.quotients.interface(signature)
        return signature, record.kernel, record

    def validate_admitted_actions(
        self,
        token: object,
        authority: PrimitiveTileKernelAdapter,
    ) -> None:
        """Deeply revalidate the admitted DAG before a run exposes its result."""
        self._require_action_admission(token)
        actions = tuple(self.action_admitted)
        for action in actions:
            self.ledger.bump("tile_causal_action_final_validation_visits")
            authority.validate_action(action)
            self.admitted_action_metadata(token, authority, action)

    def _clear_action_admission(self) -> None:
        self._action_admission_token = None
        self._issued_action_admission_token = None
        for owner, store, nodes_per_entry in (
            (self.action_pending_owner, self.action_pending, 1),
            (
                self.action_admitted_owner,
                self.action_admitted,
                _ACTION_ADMISSION_NODES,
            ),
        ):
            count = len(store)
            store.clear()
            self.ledger.release(owner, entries=count, nodes=count * nodes_per_entry)

    def clear_action_admission(self, token: object) -> None:
        self._require_action_admission(token)
        self._clear_action_admission()

    def clear(self) -> None:
        self._clear_action_admission()
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

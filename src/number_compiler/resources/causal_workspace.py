"""Charged, bounded spatial reference buffers for causal dependency tasks.

Buffers contain dyadic pieces and finite endpoints, never one slot per temporal
stage. One scheduler owns the inventory; completed tasks release their buffers.
"""

from __future__ import annotations

from collections.abc import Iterator
from sys import getsizeof
from typing import TYPE_CHECKING, Generic, TypeGuard, TypeVar

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
from number_compiler.resources.causal_audit_contracts import (
    CausalSpatialWorkspaceAuditSnapshot,
    CausalTaskWorkspaceAuditSnapshot,
)
from number_compiler.resources.causal_stacks import (
    AccountedStore,
    CausalFrameStack,
    CausalResultStack,
    CausalValueStack,
    StoreClearRetry,
    clear_owned_store,
)
from number_compiler.resources.causal_types import (
    CausalMemoKey,
    CausalSpatialValue,
    CausalTaskValue,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.lifecycle import cleanup_all
from number_compiler.resources.metric_keys import resources as _resources_keys
from number_compiler.resources.stores import LedgerDict, LedgerList

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.causal_frames import CausalTaskFrame
    from number_compiler.hashlife.execution.tile_directed_transfer import (
        DirectedTransferFrame,
    )
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )
    from number_compiler.hashlife.tiles.reverse_threshold_summary import (
        ReverseThresholdFrame,
    )
SpatialValueT = TypeVar("SpatialValueT", bound=CausalSpatialValue)


_ACTION_ADMISSION_SEAL = object()
ACTION_ADMISSION_SNAPSHOT_SIZE = 51
_ACTION_ADMISSION_NODES = 1 + ACTION_ADMISSION_SNAPSHOT_SIZE


def _handle_snapshot(handle: ArenaHandle) -> tuple[object, object, object]:
    return id(handle.owner), handle.kind, handle.local_id


def action_admission_snapshot(
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
    if len(snapshot) != ACTION_ADMISSION_SNAPSHOT_SIZE:
        raise RuntimeError("causal action admission snapshot schema is inconsistent")
    return snapshot


def action_admission_matches(
    retained: tuple[object, ...],
    current: tuple[object, ...],
) -> bool:
    """Compare snapshots without Python's bool/integer equality aliases."""
    return (
        tuple(map(type, retained)) == tuple(map(type, current)) and retained == current
    )


class CausalActionAdmission:
    """Unforgeable lease for one deeply admitted causal action DAG."""

    __slots__ = ("_authority", "_run", "_seal", "_workspace")

    def __init__(
        self,
        workspace: CausalTaskWorkspace,
        run: _CausalRunLease,
        authority: PrimitiveTileKernelAdapter,
    ) -> None:
        self._workspace = workspace
        self._run = run
        self._authority = authority
        self._seal = _ACTION_ADMISSION_SEAL

    def belongs_to(
        self,
        workspace: CausalTaskWorkspace,
        run: _CausalRunLease | None,
        authority: PrimitiveTileKernelAdapter | None,
    ) -> bool:
        """Check this token's private issuance fields at their owner boundary."""
        try:
            return (
                self._seal is _ACTION_ADMISSION_SEAL
                and self._workspace is workspace
                and self._run is run
                and self._authority is authority
            )
        except AttributeError:
            return False

    def read_metadata(
        self,
        authority: PrimitiveTileKernelAdapter,
        action: FieldCellActionID,
    ) -> tuple[PortSignatureID, ActionProgramID, PrimitiveTileAction]:
        """Authenticate and read an action through this exact live admission."""
        if not self._workspace.owns_action_admission(self):
            raise RuntimeError("causal action admission lease is not active")
        return self._workspace.admitted_action_metadata(self, authority, action)

    def admitted_snapshot_for(
        self, authority: PrimitiveTileKernelAdapter, action: FieldCellActionID
    ) -> tuple[object, ...]:
        """Return the exact admitted row snapshot to its issuing authority."""
        if authority is not self._authority:
            raise ValueError("causal action admission belongs to another authority")
        if not self._workspace.owns_action_admission(self):
            raise RuntimeError("causal action admission lease is not active")
        return self._workspace.admitted_action_snapshot(self, action)


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
    if type(authority) is not PrimitiveTileKernelAdapter:
        raise TypeError("causal action admission requires its primitive authority")
    return admission.read_metadata(authority, action)


class _CausalRunLease:
    __slots__ = ()


class SpatialReferenceBuffer(Generic[SpatialValueT]):
    __slots__ = ("backing_bytes", "capacity", "closed", "identity", "used", "workspace")

    def __init__(
        self,
        workspace: CausalSpatialWorkspace[SpatialValueT],
        identity: int,
        capacity: int,
    ) -> None:
        self.workspace, self.identity = workspace, identity
        self.capacity = capacity
        self.used, self.closed = 0, False
        self.backing_bytes = getsizeof(self) + capacity * getsizeof((0, 0))

    def __len__(self) -> int:
        return self.used

    def __getitem__(self, index: int) -> SpatialValueT:
        if self.closed:
            raise ValueError("closed spatial workspace buffer")
        if not 0 <= index < self.used:
            raise IndexError(index)
        value = self.workspace.reference_at(self.identity, index)
        if value is None:
            raise RuntimeError("used spatial reference slot is uninitialized")
        return value

    def __iter__(self) -> Iterator[SpatialValueT]:
        for index in range(self.used):
            yield self[index]

    def append(self, value: SpatialValueT) -> None:
        if self.closed or self.used == self.capacity:
            raise ValueError("closed or exhausted spatial workspace buffer")
        key = (self.identity, self.used)
        try:
            self.workspace.write_reference(key, value)
        except BaseException:
            # _TrackedDict can raise from its post-mutation audit hook. Restore
            # the reserved empty slot even in that case, preserving capacity
            # accounting and the original publication error.
            try:
                self.workspace.restore_reference_after_failed_write(key, value)
            except BaseException:
                # The original insertion failure remains the public error.
                pass
            try:
                self.workspace.ledger.bump(
                    _resources_keys.TILE_CAUSAL_SPATIAL_BUFFER_APPEND_FAILURES
                )
            except BaseException:
                pass
            raise
        self.used += 1
        self.workspace.ledger.bump(_resources_keys.TILE_CAUSAL_SPATIAL_BUFFER_APPENDS)

    def reverse(self) -> None:
        if self.closed:
            raise ValueError("closed spatial workspace buffer")
        for left in range(self.used // 2):
            right = self.used - left - 1
            a, b = (self.identity, left), (self.identity, right)
            self.workspace.swap_references(a, b)
        self.workspace.ledger.bump(
            _resources_keys.TILE_CAUSAL_SPATIAL_BUFFER_REVERSAL_VISITS, self.used
        )

    def close(self) -> None:
        self.workspace.release(self)


class CausalSpatialWorkspace(Generic[SpatialValueT]):
    """One inventory for all live spatial buffers, including unused capacity."""

    def __init__(self, ledger: ResourceLedger, prefix: str) -> None:
        self.ledger = ledger
        self.owner = ledger.register(
            prefix + "-spatial-workspace", "causal_spatial_workspace"
        )
        self.buffer_owner = ledger.register(
            prefix + "-spatial-buffers", "causal_spatial_workspace"
        )
        self._buffers: LedgerDict[int, SpatialReferenceBuffer[SpatialValueT]] = (
            ledger.make_dict(
                self.buffer_owner,
                nodes_per_entry=1,
            )
        )
        self._refs: LedgerDict[tuple[int, int], SpatialValueT | None] = (
            ledger.make_dict(self.owner)
        )
        self._next = 0
        self.slots = self._object_bytes = 0

    def __len__(self) -> int:
        return self.slots

    @property
    def backing_bytes(self) -> int:
        return (
            self._object_bytes + self._refs.backing_bytes + self._buffers.backing_bytes
        )

    def reference_at(self, identity: int, index: int) -> SpatialValueT | None:
        """Read one reserved slot by its validated internal workspace key."""
        return self._refs[identity, index]

    def write_reference(
        self, key: tuple[int, int], value: SpatialValueT | None
    ) -> None:
        """Write one already-reserved spatial slot."""
        self._refs[key] = value

    def restore_reference_after_failed_write(
        self, key: tuple[int, int], attempted_value: SpatialValueT
    ) -> None:
        """Restore an uninitialized reserved slot after a failing audit hook."""
        self._refs.rollback_failed_write(key, attempted_value, None)

    def swap_references(self, left: tuple[int, int], right: tuple[int, int]) -> None:
        """Swap two admitted reference slots during an in-place reversal."""
        first, second = self._refs[left], self._refs[right]
        self._refs[left], self._refs[right] = second, first

    def owns_buffer(self, buffer: SpatialReferenceBuffer[SpatialValueT]) -> bool:
        """Authenticate a live buffer through the exact workspace issuer."""
        return (
            type(buffer) is SpatialReferenceBuffer
            and buffer.workspace is self
            and not buffer.closed
            and self._buffers.get(buffer.identity) is buffer
        )

    def payloads(self) -> Iterator[SpatialValueT]:
        for value in self._refs.values():
            if value is not None:
                yield value

    def allocate(self, capacity: int) -> SpatialReferenceBuffer[SpatialValueT]:
        if type(capacity) is not int or capacity < 0:
            raise ValueError(
                "spatial reference capacity requires a nonnegative integer"
            )
        self.ledger.reserve_many(((self.owner, capacity, 0), (self.buffer_owner, 1, 1)))
        old_tables = (self._refs.backing_bytes, self._buffers.backing_bytes)
        identity = self._next
        self._next += 1
        rollback_buffer: SpatialReferenceBuffer[SpatialValueT] | None = None
        try:
            buffer = SpatialReferenceBuffer(self, identity, capacity)
            rollback_buffer = buffer
            self._buffers[identity] = buffer
            for index in range(capacity):
                self._refs[identity, index] = None
            self.ledger.note_store_mutation()
        except BaseException:
            for index in range(capacity):
                self._refs.rollback_inserted_value((identity, index), None)
            if rollback_buffer is not None:
                self._buffers.rollback_inserted_value(identity, rollback_buffer)
            self.ledger.release(self.owner, entries=capacity)
            self.ledger.release(self.buffer_owner, entries=1, nodes=1)
            try:
                self.ledger.note_store_mutation()
            except BaseException:
                pass
            raise
        self.slots += capacity
        self._object_bytes += buffer.backing_bytes
        self.ledger.bump(_resources_keys.TILE_CAUSAL_SPATIAL_BUFFER_ALLOCATIONS)
        new_tables = (self._refs.backing_bytes, self._buffers.backing_bytes)
        self.ledger.bump(
            _resources_keys.TILE_CAUSAL_SPATIAL_BUFFER_ALLOCATED_BYTES,
            buffer.backing_bytes
            + sum(
                max(0, new - old)
                for old, new in zip(old_tables, new_tables, strict=True)
            ),
        )
        for name, value in (("slots", self.slots), ("bytes", self.backing_bytes)):
            counter = (
                _resources_keys.TILE_CAUSAL_SPATIAL_BUFFER_PEAK_SLOTS
                if name == "slots"
                else _resources_keys.TILE_CAUSAL_SPATIAL_BUFFER_PEAK_BYTES
            )
            self.ledger.bump(
                counter, max(0, value - self.ledger.counters.get(counter, 0))
            )
        return buffer

    def release(self, buffer: SpatialReferenceBuffer[SpatialValueT]) -> None:
        if buffer.workspace is not self:
            raise ValueError("foreign spatial workspace buffer")
        if buffer.closed:
            return
        if self._buffers.get(buffer.identity) is not buffer:
            raise ValueError("stale spatial workspace buffer")
        charge = buffer.capacity
        removed_references: list[tuple[tuple[int, int], SpatialValueT | None]] = []
        buffer_removed = False
        try:
            for index in range(buffer.capacity):
                key = (buffer.identity, index)
                value = self._refs[key]
                try:
                    del self._refs[key]
                except BaseException:
                    if key not in self._refs:
                        removed_references.append((key, value))
                    raise
                removed_references.append((key, value))
            try:
                del self._buffers[buffer.identity]
            except BaseException:
                buffer_removed = buffer.identity not in self._buffers
                raise
            buffer_removed = True
            self.ledger.reassign_many(
                (
                    (self.owner, charge, 0),
                    (self.buffer_owner, 1, 1),
                ),
                (),
            )
        except BaseException:
            if buffer_removed:
                try:
                    self._buffers.restore_deleted_value(buffer.identity, buffer)
                except BaseException:
                    pass
            for key, value in reversed(removed_references):
                try:
                    if key not in self._refs:
                        self._refs.restore_deleted_value(key, value)
                except BaseException:
                    pass
            raise
        self.slots -= charge
        self._object_bytes -= buffer.backing_bytes
        buffer.used, buffer.closed = 0, True

    def clear(self) -> None:
        while self._buffers:
            self.release(next(iter(self._buffers.values())))

    def audit_snapshot(self) -> CausalSpatialWorkspaceAuditSnapshot[SpatialValueT]:
        """Return exact retained entries and the ledger stores that own them."""
        return CausalSpatialWorkspaceAuditSnapshot(
            owner=self.owner,
            buffer_owner=self.buffer_owner,
            slots=self.slots,
            object_bytes=self._object_bytes,
            next_identity=self._next,
            buffers=tuple(self._buffers.items()),
            references=tuple(sorted(self._refs.items(), key=lambda item: item[0])),
            reference_store=self._refs,
            buffer_store=self._buffers,
        )


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
        self.memo: LedgerDict[CausalMemoKey, CausalTaskValue] = ledger.make_dict(
            self.memo_owner
        )
        self.active: LedgerDict[CausalMemoKey, bool] = ledger.make_dict(
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
        self._action_admission_token: CausalActionAdmission | None = None
        self._issued_action_admission_token: CausalActionAdmission | None = None
        self._action_authority: PrimitiveTileKernelAdapter | None = None
        self._action_admission_closing = False
        self._run_token: _CausalRunLease | None = None
        self.frames: CausalFrameStack[CausalTaskFrame] = CausalFrameStack(
            ledger, prefix
        )
        self.summary_frames: CausalFrameStack[ReverseThresholdFrame] = CausalFrameStack(
            ledger, prefix + "-reverse-threshold"
        )
        self.values: CausalResultStack[CausalTaskValue] = CausalResultStack(
            ledger, prefix
        )
        self.directed_frames: CausalFrameStack[DirectedTransferFrame] = (
            CausalFrameStack(ledger, prefix + "-directed")
        )
        self.directed_values = CausalValueStack(ledger, prefix + "-directed")
        self._memo_clear_retry = StoreClearRetry()
        self._active_clear_retry = StoreClearRetry()
        self._action_pending_clear_retry = StoreClearRetry()
        self._action_admitted_clear_retry = StoreClearRetry()

    def _clear_store(
        self,
        owner: int,
        store: AccountedStore,
    ) -> None:
        if owner == self.memo_owner and store is self.memo:
            retry = self._memo_clear_retry
        elif owner == self.active_owner and store is self.active:
            retry = self._active_clear_retry
        elif owner == self.action_pending_owner and store is self.action_pending:
            retry = self._action_pending_clear_retry
        elif owner == self.action_admitted_owner and store is self.action_admitted:
            retry = self._action_admitted_clear_retry
        else:
            raise ValueError("causal store cleanup received a foreign store")
        clear_owned_store(
            self.ledger,
            owner,
            store,
            retry,
        )

    def begin(self, key: CausalMemoKey) -> None:
        if key in self.active:
            raise ValueError("causal task dependency contains a cycle")
        self.ledger.reserve(self.active_owner, entries=1)
        try:
            self.active[key] = True
        except BaseException:
            try:
                self.active.rollback_inserted_value(key, True)
            except BaseException:
                pass
            self.ledger.release(self.active_owner, entries=1)
            raise

    def begin_run(self) -> _CausalRunLease:
        if self._run_token is not None:
            raise RuntimeError("causal task workspace already has an active run")
        token = _CausalRunLease()
        self._run_token = token
        return token

    def end_run(self, token: _CausalRunLease) -> None:
        if self._run_token is not token:
            raise RuntimeError("causal task run lease is not active")
        self._run_token = None

    def finish(self, key: CausalMemoKey, value: CausalTaskValue) -> None:
        if key not in self.active or key in self.memo:
            raise ValueError("causal task completion has no unique active dependency")
        self.ledger.reserve(self.memo_owner, entries=1)
        try:
            self.memo[key] = value
        except BaseException:
            try:
                self.memo.rollback_inserted_value(key, value)
            except BaseException:
                pass
            self.ledger.release(self.memo_owner, entries=1)
            raise
        try:
            del self.active[key]
        except BaseException:
            try:
                if key not in self.active:
                    self.active.restore_deleted_value(key, True)
            except BaseException:
                pass
            try:
                self.memo.rollback_inserted_value(key, value)
            except BaseException:
                pass
            self.ledger.release(self.memo_owner, entries=1)
            raise
        self.ledger.release(self.active_owner, entries=1)

    def begin_action_admission(
        self,
        action: FieldCellActionID,
        authority: PrimitiveTileKernelAdapter,
    ) -> CausalActionAdmission:
        if (
            self._action_admission_token is not None
            or self._issued_action_admission_token is not None
            or self._action_admission_closing
            or self.action_pending
            or self.action_admitted
        ):
            raise RuntimeError("causal action admission is already active")
        run = self._run_token
        if type(run) is not _CausalRunLease:
            raise RuntimeError("causal action admission requires an active run")
        token = CausalActionAdmission(self, run, authority)
        self._action_admission_token = token
        self._issued_action_admission_token = token
        self._action_authority = authority
        try:
            self.push_action(token, action)
        except BaseException:
            self._action_admission_token = None
            self._issued_action_admission_token = None
            self._action_authority = None
            raise
        return token

    def _require_action_admission(self, token: object) -> CausalActionAdmission:
        if not self.owns_action_admission(token):
            raise RuntimeError("causal action admission lease is not active")
        return token

    def matches_active_run(self, run: object | None) -> bool:
        """Check a detached audit token against this exact run owner."""
        return self._run_token is run and (run is None or type(run) is _CausalRunLease)

    def audit_snapshot(self) -> CausalTaskWorkspaceAuditSnapshot:
        """Return exact retained values and their ledger-owned containers."""
        return CausalTaskWorkspaceAuditSnapshot(
            workspace=self,
            memo_owner=self.memo_owner,
            active_owner=self.active_owner,
            action_pending_owner=self.action_pending_owner,
            action_admitted_owner=self.action_admitted_owner,
            memo_store=self.memo,
            active_store=self.active,
            pending_store=self.action_pending,
            admitted_store=self.action_admitted,
            memo_items=tuple(self.memo.items()),
            active_items=tuple(self.active.items()),
            pending_actions=self.action_pending.snapshot(),
            admitted_items=tuple(self.action_admitted.items()),
            action_admission=self._action_admission_token,
            issued_action_admission=self._issued_action_admission_token,
            run_token=self._run_token,
            admission_closing=self._action_admission_closing,
            frames=self.frames.audit_snapshot(),
            summary_frames=self.summary_frames.audit_snapshot(),
            values=self.values.audit_snapshot(),
            directed_frames=self.directed_frames.audit_snapshot(),
            directed_values=self.directed_values.audit_snapshot(),
        )

    def owns_action_admission(
        self, admission: object
    ) -> TypeGuard[CausalActionAdmission]:
        """Recognize only this workspace's exact live run admission lease."""
        return (
            type(admission) is CausalActionAdmission
            and admission.belongs_to(self, self._run_token, self._action_authority)
            and admission is self._action_admission_token
            and admission is self._issued_action_admission_token
            and not self._action_admission_closing
            and type(self._run_token) is _CausalRunLease
        )

    def push_action(
        self, token: CausalActionAdmission, action: FieldCellActionID
    ) -> None:
        self._require_action_admission(token)
        self.ledger.reserve(self.action_pending_owner, entries=1, nodes=1)
        try:
            self.action_pending.append(action)
        except BaseException:
            self.ledger.release(self.action_pending_owner, entries=1, nodes=1)
            raise

    def pop_action(self, token: CausalActionAdmission) -> FieldCellActionID:
        self._require_action_admission(token)
        action = self.action_pending.pop()
        self.ledger.release(self.action_pending_owner, entries=1, nodes=1)
        return action

    def action_is_admitted(
        self, token: CausalActionAdmission, action: FieldCellActionID
    ) -> bool:
        self._require_action_admission(token)
        return action in self.action_admitted

    def admit_action(
        self,
        token: CausalActionAdmission,
        action: FieldCellActionID,
        record: PrimitiveTileAction,
    ) -> None:
        self._require_action_admission(token)
        if action in self.action_admitted:
            return
        snapshot = action_admission_snapshot(action, record)
        self.ledger.reserve(
            self.action_admitted_owner,
            entries=1,
            nodes=_ACTION_ADMISSION_NODES,
        )
        try:
            self.action_admitted[action] = snapshot
        except BaseException:
            try:
                self.action_admitted.rollback_inserted_value(action, snapshot)
            except BaseException:
                pass
            self.ledger.release(
                self.action_admitted_owner,
                entries=1,
                nodes=_ACTION_ADMISSION_NODES,
            )
            raise

    def admitted_action_snapshot(
        self,
        token: CausalActionAdmission,
        action: FieldCellActionID,
    ) -> tuple[object, ...]:
        """Return a detached snapshot only for the exact active run lease."""
        token = self._require_action_admission(token)
        if type(action) is not FieldCellActionID:
            raise TypeError("causal action admission requires a field action ID")
        try:
            snapshot = self.action_admitted[action]
        except KeyError:
            raise ValueError("action is outside this run's admitted DAG") from None
        if (
            type(snapshot) is not tuple
            or len(snapshot) != ACTION_ADMISSION_SNAPSHOT_SIZE
        ):
            raise ValueError("causal action admission snapshot is malformed")
        if not action_admission_matches(snapshot[:3], _handle_snapshot(action)):
            raise ValueError("causal action admission handle changed")
        return snapshot

    def admitted_action_metadata(
        self,
        token: CausalActionAdmission,
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
        self._require_action_admission(token)
        self.ledger.bump(_resources_keys.TILE_CAUSAL_ACTION_ADMITTED_METADATA_VISITS)
        try:
            record = authority.admitted_action_record(action, token)
        except KeyError:
            raise ValueError("stale or unpublished primitive tile action") from None
        if type(record) is not PrimitiveTileAction:
            raise TypeError("primitive action store contains another record sort")
        signature = record.signature
        authority.quotients.interface(signature)
        return signature, record.kernel, record

    def validate_admitted_actions(
        self,
        token: CausalActionAdmission,
        authority: PrimitiveTileKernelAdapter,
    ) -> None:
        """Deeply revalidate the admitted DAG before a run exposes its result."""
        self._require_action_admission(token)
        actions = tuple(self.action_admitted)
        for action in actions:
            self.ledger.bump(_resources_keys.TILE_CAUSAL_ACTION_FINAL_VALIDATION_VISITS)
            authority.validate_action(action)
            self.admitted_action_metadata(token, authority, action)

    def _clear_action_admission(self) -> None:
        self._action_admission_closing = True
        cleanup_all(
            (
                lambda: self._clear_store(
                    self.action_pending_owner, self.action_pending
                ),
                lambda: self._clear_store(
                    self.action_admitted_owner, self.action_admitted
                ),
            )
        )
        self._action_admission_token = None
        self._issued_action_admission_token = None
        self._action_authority = None
        self._action_admission_closing = False

    def clear_action_admission(self, token: object) -> None:
        if self._action_admission_closing:
            if token is not self._issued_action_admission_token:
                raise RuntimeError("causal action admission lease is not active")
        else:
            self._require_action_admission(token)
        self._clear_action_admission()

    def clear(self) -> None:
        cleanup_all(
            (
                self._clear_action_admission,
                lambda: self._clear_store(self.memo_owner, self.memo),
                lambda: self._clear_store(self.active_owner, self.active),
                self.frames.clear,
                self.summary_frames.clear,
                self.values.clear,
                self.directed_frames.clear,
                self.directed_values.clear,
            )
        )

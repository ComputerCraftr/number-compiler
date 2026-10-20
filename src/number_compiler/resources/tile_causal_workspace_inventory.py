"""Read-only ownership checks for retained causal task workspace payloads."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import fields, is_dataclass
from sys import getsizeof
from typing import TYPE_CHECKING, Protocol, TypeGuard, TypeVar, cast

from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.hashlife.execution.causal_frames import (
    CAUSAL_FRAME_TYPES,
    CausalTaskFrame,
)
from number_compiler.hashlife.interfaces.semantic_structures import LocalInterfaceID
from number_compiler.hashlife.tiles.reverse_threshold_summary import (
    ReverseThresholdFrame,
)
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.hashlife.tiles.tiles import TileID
from number_compiler.resources.causal_audit_contracts import (
    CausalTaskWorkspaceAuditSnapshot,
)
from number_compiler.resources.causal_types import (
    CausalPrefix,
    CausalSpatialValue,
)
from number_compiler.resources.causal_workspace import (
    ACTION_ADMISSION_SNAPSHOT_SIZE,
    CausalActionAdmission,
    CausalSpatialWorkspace,
    CausalTaskWorkspace,
    SpatialReferenceBuffer,
    action_admission_matches,
    action_admission_snapshot,
)
from number_compiler.resources.tile_scheduler_inventory_support import (
    CAUSAL_FRAME_OPS,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_scheduler import (
        CausalSchedulerAuditOwners,
        TileScheduler,
    )


def _is_object_tuple(value: object) -> TypeGuard[tuple[object, ...]]:
    """Narrow heterogeneous tuples at the audit boundary without trusting them."""
    return type(value) is tuple


def valid_frame_value(
    scheduler: TileScheduler,
    value: object,
    approved: set[int] | None = None,
    owners: CausalSchedulerAuditOwners | None = None,
) -> bool:
    """Validate one retained causal frame, value, or task-memo payload."""
    causal_owners = owners if owners is not None else scheduler.audit_causal_owners()
    pending = [value]
    seen: set[int] = set()
    while pending:
        current = pending.pop()
        if id(current) in seen:
            continue
        seen.add(id(current))
        if current is None or type(current) in (int, bool, str):
            continue
        if type(current) is ReverseBoundOutput:
            try:
                current.__post_init__()
            except (TypeError, ValueError, AttributeError):
                return False
            continue
        if type(current) is CausalPrefix:
            if not _valid_causal_prefix(scheduler, current):
                return False
            continue
        if _is_object_tuple(current):
            if len(current) > 8 or (
                len(current) > 2 and all(type(item) is TileID for item in current)
            ):
                return False
            pending.extend(current)
            continue
        if type(current) is FieldCellActionID:
            try:
                scheduler.adapter.validate_action(current)
            except (TypeError, ValueError, KeyError, AttributeError, IndexError):
                return False
            continue
        if type(current) is TileID:
            try:
                scheduler.tiles.resolve(current)
            except (TypeError, ValueError, KeyError, AttributeError, IndexError):
                return False
            continue
        if type(current) is LocalInterfaceID:
            try:
                scheduler.results.interfaces.resolve(current)
            except (TypeError, ValueError, KeyError, AttributeError, IndexError):
                return False
            continue
        if type(current) is PortSignatureID:
            try:
                scheduler.results.interfaces.interface(current)
            except (TypeError, ValueError, KeyError, AttributeError, IndexError):
                return False
            continue
        if type(current) is BoundaryTileView:
            try:
                current.__post_init__()
                tile_record = scheduler.tiles.resolve(current.tile)
                if current.source_offset + current.relative_extent > tile_record.width:
                    return False
            except (TypeError, ValueError, KeyError, AttributeError, IndexError):
                return False
            continue
        if type(current) is SpatialReferenceBuffer:
            if not causal_owners.spatial.owns_buffer(cast(object, current)):
                return False
            continue
        if type(current) is CausalActionAdmission:
            if not causal_owners.tasks.owns_action_admission(current):
                return False
            if approved is not None:
                approved.add(id(current))
            continue
        if is_dataclass(current) and (
            type(current).__module__.startswith(
                (
                    "number_compiler.hashlife.tiles.tile_",
                    "number_compiler.hashlife.execution.tile_",
                )
            )
            or type(current).__module__
            == "number_compiler.arithmetic.contracts.scoped_handles"
        ):
            try:
                dataclass_values: list[object] = []
                for dataclass_field in fields(current):
                    field_value: object = object.__getattribute__(
                        current, dataclass_field.name
                    )
                    dataclass_values.append(field_value)
            except (TypeError, AttributeError):
                return False
            pending.extend(dataclass_values)
            continue
        return False
    return True


def _is_reverse_threshold_frame(value: object) -> TypeGuard[ReverseThresholdFrame]:
    return type(value) is ReverseThresholdFrame


def _is_causal_task_frame(value: object) -> TypeGuard[CausalTaskFrame]:
    return type(value) in CAUSAL_FRAME_TYPES


def _frame_payload_shape(
    value: object,
) -> tuple[tuple[object, ...], tuple[object, ...], int] | None:
    """Validate one retained frame's payload slots and reference accounting."""
    frame: CausalTaskFrame | ReverseThresholdFrame
    if _is_causal_task_frame(value):
        frame = value
    elif _is_reverse_threshold_frame(value):
        frame = value
    else:
        return None
    args_value: object = frame.args
    saved_value: object = frame.saved
    if not _is_object_tuple(args_value) or not _is_object_tuple(saved_value):
        return None
    direct_references = len(args_value) + len(saved_value)
    try:
        reported_references = frame.payload_reference_count()
    except (TypeError, ValueError, KeyError, AttributeError, IndexError):
        return None
    if type(reported_references) is not int or reported_references != direct_references:
        return None
    return args_value, saved_value, direct_references


def _is_tile_id(value: object) -> TypeGuard[TileID]:
    return type(value) is TileID


def _is_spatial_buffer(
    value: object,
) -> TypeGuard[SpatialReferenceBuffer[CausalSpatialValue]]:
    return type(value) is SpatialReferenceBuffer


def _is_spatial_reference_key(value: object) -> TypeGuard[tuple[int, int]]:
    return (
        _is_object_tuple(value)
        and len(value) == 2
        and type(value[0]) is int
        and type(value[1]) is int
    )


class _LedgerSequence(Protocol):
    @property
    def ledger(self) -> object: ...

    def __len__(self) -> int: ...


_StackValue_co = TypeVar("_StackValue_co", covariant=True)


class _FrameStackAudit(Protocol[_StackValue_co]):
    @property
    def owner(self) -> int: ...

    @property
    def store(self) -> _LedgerSequence: ...

    @property
    def values(self) -> tuple[_StackValue_co, ...]: ...

    @property
    def payload_references(self) -> int | None: ...


def _audit_frame_stack(
    stack: _FrameStackAudit[_StackValue_co],
    ledger: object,
    stack_identity: object,
    valid_workspace: bool,
    approved: set[int],
    invalid: set[tuple[int, int]],
    validate_frame: Callable[[object], tuple[bool, int | None]],
) -> bool:
    """Share exact retained-slot and ledger checks between typed task stacks."""
    valid_stack = valid_workspace
    references = 0
    for retained_value in stack.values:
        frame_value: object = retained_value
        valid, slots = validate_frame(frame_value)
        if slots is None:
            valid = False
            valid_stack = False
        else:
            references += slots
        if valid:
            approved.add(id(frame_value))
        else:
            invalid.add((stack.owner, id(frame_value)))
            valid_stack = False
    if (
        type(stack.payload_references) is not int
        or stack.payload_references != references
    ):
        valid_stack = False
        invalid.add((stack.owner, id(stack_identity)))
    valid_stack &= stack.store.ledger is ledger and len(stack.store) == len(
        stack.values
    )
    return valid_stack


def _valid_causal_prefix(scheduler: TileScheduler, prefix: CausalPrefix) -> bool:
    try:
        scheduler.adapter.validate_action(prefix.action)
        if (
            type(prefix.side) is not int
            or prefix.side not in (0, 1)
            or type(prefix.producer_seed) is not int
            or prefix.producer_seed < 0
            or type(prefix.consumer_seed) is not int
            or prefix.consumer_seed < 0
            or type(prefix.explicit_edge) is not bool
        ):
            return False
        for view in (prefix.view, prefix.consumer_view):
            if view is None:
                continue
            view.__post_init__()
            tile_record = scheduler.tiles.resolve(view.tile)
            if view.source_offset + view.relative_extent > tile_record.width:
                return False
    except (TypeError, ValueError, KeyError, AttributeError, IndexError):
        return False
    return True


def audit_task_payloads(
    scheduler: TileScheduler,
    tasks: CausalTaskWorkspace,
    task_state: CausalTaskWorkspaceAuditSnapshot,
    valid_root: bool,
    owners: CausalSchedulerAuditOwners,
) -> tuple[set[int], set[tuple[int, int]]]:
    """Authenticate every retained causal memo and active-task payload."""
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )

    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    adapter_value: object = scheduler.adapter
    if type(adapter_value) is not PrimitiveTileKernelAdapter:
        invalid.add((tasks.action_pending_owner, id(adapter_value)))
        return approved, invalid
    adapter = adapter_value
    active_admission = task_state.action_admission
    try:
        admission_valid = (
            task_state.workspace is tasks
            and task_state.issued_action_admission is active_admission
            and task_state.admission_closing is False
            and tasks.matches_active_run(task_state.run_token)
            and (
                (
                    active_admission is None
                    and not task_state.pending_actions
                    and not task_state.admitted_items
                )
                or (
                    type(active_admission) is CausalActionAdmission
                    and tasks.owns_action_admission(active_admission)
                )
            )
        )
    except (AttributeError, TypeError, ValueError):
        admission_valid = False
    valid_root &= admission_valid

    def valid_key(value: object) -> bool:
        if not _is_object_tuple(value) or len(value) != 2:
            return False
        operation, arguments = value
        return (
            type(operation) is str
            and operation in CAUSAL_FRAME_OPS
            and _is_object_tuple(arguments)
            and len(arguments) <= 8
            and valid_frame_value(scheduler, arguments, approved, owners)
        )

    for memo_key, memo_value in task_state.memo_items:
        valid = (
            valid_root
            and valid_key(memo_key)
            and valid_frame_value(scheduler, memo_value, approved, owners)
        )
        if valid:
            approved.update((id(memo_key), id(memo_value)))
        else:
            invalid.update(
                (
                    (tasks.memo_owner, id(memo_key)),
                    (tasks.memo_owner, id(memo_value)),
                )
            )
    for active_key, active_value in task_state.active_items:
        valid = valid_root and valid_key(active_key) and active_value is True
        if valid:
            approved.update((id(active_key), id(active_value)))
        else:
            invalid.update(
                (
                    (tasks.active_owner, id(active_key)),
                    (tasks.active_owner, id(active_value)),
                )
            )
    for action in task_state.pending_actions:
        valid = valid_root
        try:
            adapter.validate_action(action)
        except (TypeError, ValueError, KeyError, AttributeError, IndexError):
            valid = False
        if valid:
            approved.add(id(action))
        else:
            invalid.add((tasks.action_pending_owner, id(action)))
    for action, marker in task_state.admitted_items:
        valid = (
            valid_root
            and type(marker) is tuple
            and len(marker) == ACTION_ADMISSION_SNAPSHOT_SIZE
        )
        try:
            record = adapter.action_record(action)
            valid = valid and action_admission_matches(
                marker,
                action_admission_snapshot(
                    action,
                    record,
                ),
            )
        except (TypeError, ValueError, KeyError, AttributeError, IndexError):
            valid = False
        if valid:
            approved.update((id(action), id(marker)))
        else:
            invalid.update(
                (
                    (tasks.action_admitted_owner, id(action)),
                    (tasks.action_admitted_owner, id(marker)),
                )
            )
    return approved, invalid


def audit_task_workspace(
    scheduler: TileScheduler,
    spatial: CausalSpatialWorkspace[CausalSpatialValue],
    tasks: CausalTaskWorkspace,
    root_valid: bool,
) -> tuple[set[int], set[tuple[int, int]]]:
    """Audit used spatial references and the separately typed task stacks."""
    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    workspace_valid = root_valid
    owners = scheduler.audit_causal_owners()
    spatial_state = spatial.audit_snapshot()
    task_state = tasks.audit_snapshot()
    workspace_valid &= spatial is owners.spatial and tasks is owners.tasks

    reference_values: dict[tuple[int, int], tuple[object, object]] = {}
    reference_rows_valid = True
    for raw_key, raw_value in spatial_state.references:
        key_value: object = raw_key
        value: object = raw_value
        if not _is_spatial_reference_key(key_value) or key_value in reference_values:
            reference_rows_valid = False
            continue
        reference_values[key_value] = (key_value, value)

    expected_refs: set[tuple[int, int]] = set()
    retained_reference_count = len(reference_values)
    capacities = object_bytes = 0
    buffers_valid = True
    for raw_identity, raw_buffer in spatial_state.buffers:
        identity_value: object = raw_identity
        buffer_value: object = raw_buffer
        if type(identity_value) is not int or not _is_spatial_buffer(buffer_value):
            buffers_valid = False
            invalid.add((spatial_state.buffer_owner, id(buffer_value)))
            continue
        identity = identity_value
        buffer = buffer_value
        valid = workspace_valid
        try:
            valid &= (
                buffer.workspace is spatial
                and buffer.identity == identity
                and type(buffer.capacity) is int
                and type(buffer.used) is int
                and 0 <= buffer.used <= buffer.capacity
                and type(buffer.closed) is bool
                and not buffer.closed
                and type(buffer.backing_bytes) is int
                and buffer.backing_bytes
                == getsizeof(buffer) + buffer.capacity * getsizeof((0, 0))
            )
            if type(buffer.capacity) is int and buffer.capacity >= 0:
                remaining_references = max(0, retained_reference_count - capacities)
                inspect_capacity = (
                    buffer.capacity if buffer.capacity <= remaining_references else 0
                )
                if inspect_capacity != buffer.capacity:
                    valid = False
                capacities += buffer.capacity
            else:
                valid = False
                inspect_capacity = 0
            if type(buffer.backing_bytes) is int and buffer.backing_bytes >= 0:
                object_bytes += buffer.backing_bytes
            else:
                valid = False
            used_references = (
                buffer.used
                if type(buffer.used) is int
                and type(buffer.capacity) is int
                and 0 <= buffer.used <= buffer.capacity
                else 0
            )
            for index in range(inspect_capacity):
                ref_key = (identity, index)
                expected_refs.add(ref_key)
                retained = reference_values.get(ref_key)
                if retained is None:
                    valid = False
                    continue
                actual_key, value = retained
                if index >= used_references:
                    valid_value = value is None
                elif type(value) is int:
                    valid_value = value >= 0
                elif type(value) is TileID:
                    scheduler.tiles.resolve(value)
                    valid_value = True
                elif type(value) is CausalPrefix:
                    valid_value = _valid_causal_prefix(scheduler, value)
                else:
                    valid_value = False
                valid &= valid_value
                if index < used_references and valid and valid_value:
                    approved.update((id(actual_key), id(value)))
        except (TypeError, ValueError, KeyError, AttributeError, IndexError):
            valid = False
        if valid:
            approved.update((id(identity), id(buffer)))
        else:
            buffers_valid = False
            invalid.add((spatial.buffer_owner, id(buffer)))
    workspace_valid &= (
        reference_rows_valid
        and buffers_valid
        and set(reference_values) == expected_refs
        and type(spatial_state.slots) is int
        and spatial_state.slots == capacities
        and type(spatial_state.object_bytes) is int
        and spatial_state.object_bytes == object_bytes
        and type(spatial_state.next_identity) is int
        and spatial_state.next_identity >= 0
        and all(
            identity < spatial_state.next_identity
            for identity, _ in spatial_state.buffers
            if type(identity) is int
        )
        and spatial_state.reference_store.ledger is scheduler.ledger
        and spatial_state.buffer_store.ledger is scheduler.ledger
    )
    if not workspace_valid:
        invalid.add((spatial_state.owner, id(spatial)))

    task_approved, task_invalid = audit_task_payloads(
        scheduler, tasks, task_state, workspace_valid, owners
    )
    approved.update(task_approved)
    invalid.update(task_invalid)
    workspace_valid &= not task_invalid

    def validate_causal_frame(value: object) -> tuple[bool, int | None]:
        if not _is_causal_task_frame(value):
            return False, None
        payload = _frame_payload_shape(value)
        if payload is None:
            return False, None
        args_value, saved_value, direct_references = payload
        args_valid = len(args_value) <= 8 and valid_frame_value(
            scheduler, args_value, approved, owners
        )
        saved_valid = len(saved_value) <= 3 and valid_frame_value(
            scheduler, saved_value, approved, owners
        )
        valid = (
            workspace_valid
            and type(value.op) is str
            and value.op in CAUSAL_FRAME_OPS
            and args_valid
            and saved_valid
            and type(value.stage) is int
            and value.stage >= -1
            and type(value.memoized) is bool
        )
        return valid, direct_references

    task_frames_valid = _audit_frame_stack(
        task_state.frames,
        scheduler.ledger,
        tasks.frames,
        workspace_valid,
        approved,
        invalid,
        validate_causal_frame,
    )
    workspace_valid &= task_frames_valid

    def validate_summary_frame(value: object) -> tuple[bool, int | None]:
        if not _is_reverse_threshold_frame(value):
            return False, None
        payload = _frame_payload_shape(value)
        if payload is None:
            return False, None
        args_value, saved_value, direct_references = payload
        valid = (
            workspace_valid
            and len(args_value) == 1
            and type(value.ready) is bool
            and type(value.known_missing) is bool
            and not saved_value
        )
        tile_value: object = None
        if len(args_value) == 1:
            tile_value = args_value[0]
        if not _is_tile_id(tile_value):
            valid = False
        if _is_tile_id(tile_value):
            try:
                scheduler.tiles.resolve(tile_value)
            except (TypeError, ValueError, KeyError, AttributeError, IndexError):
                valid = False
        else:
            valid = False
        return valid, direct_references

    summary_frames_valid = _audit_frame_stack(
        task_state.summary_frames,
        scheduler.ledger,
        tasks.summary_frames,
        workspace_valid,
        approved,
        invalid,
        validate_summary_frame,
    )
    workspace_valid &= summary_frames_valid

    if not workspace_valid:
        invalid.add((task_state.frames.owner, id(tasks.frames)))
        invalid.add((task_state.summary_frames.owner, id(tasks.summary_frames)))
    for task_value in task_state.values.values:
        if workspace_valid and valid_frame_value(
            scheduler, task_value, approved, owners
        ):
            approved.add(id(task_value))
        else:
            invalid.add((task_state.values.owner, id(task_value)))
    workspace_valid &= (
        task_state.memo_store.ledger is scheduler.ledger
        and task_state.active_store.ledger is scheduler.ledger
        and task_state.pending_store.ledger is scheduler.ledger
        and task_state.admitted_store.ledger is scheduler.ledger
        and task_state.values.store.ledger is scheduler.ledger
        and len(task_state.memo_store) == len(task_state.memo_items)
        and len(task_state.active_store) == len(task_state.active_items)
        and len(task_state.pending_store) == len(task_state.pending_actions)
        and len(task_state.admitted_store) == len(task_state.admitted_items)
        and len(task_state.values.store) == len(task_state.values.values)
    )
    if workspace_valid:
        approved.update(
            (
                id(scheduler),
                id(owners.pins),
                id(spatial),
                id(spatial_state.reference_store),
                id(spatial_state.buffer_store),
                id(tasks),
                id(task_state.memo_store),
                id(task_state.active_store),
                id(tasks.frames),
                id(task_state.frames.store),
                id(tasks.summary_frames),
                id(task_state.summary_frames.store),
                id(tasks.values),
                id(task_state.values.store),
            )
        )
    return approved, invalid


__all__ = ["audit_task_payloads", "audit_task_workspace", "valid_frame_value"]

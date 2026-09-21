"""Read-only ownership checks for retained causal task workspace payloads."""

from __future__ import annotations

from dataclasses import fields, is_dataclass
from typing import TYPE_CHECKING, cast

from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.hashlife.tiles.tiles import TileID
from number_compiler.resources.causal_workspace import (
    _ACTION_ADMISSION_SNAPSHOT_SIZE,
    CausalActionAdmission,
    CausalTaskWorkspace,
    SpatialReferenceBuffer,
    _action_admission_matches,
    _action_admission_snapshot,
)
from number_compiler.resources.tile_scheduler_inventory_support import CAUSAL_FRAME_OPS

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler


def valid_frame_value(
    scheduler: TileScheduler,
    value: object,
    approved: set[int] | None = None,
) -> bool:
    """Validate one retained causal frame, value, or task-memo payload."""
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
        if type(current) is tuple:
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
            if (
                current.workspace is not scheduler._causal_workspace
                or current.closed
                or current.workspace._buffers.get(current.identity) is not current
            ):
                return False
            continue
        if type(current) is CausalActionAdmission:
            if not scheduler._causal_tasks.owns_action_admission(current):
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
            pending.extend(getattr(current, item.name) for item in fields(current))
            continue
        return False
    return True


def audit_task_payloads(
    scheduler: TileScheduler,
    tasks: CausalTaskWorkspace,
    valid_root: bool,
) -> tuple[set[int], set[tuple[int, int]]]:
    """Authenticate every retained causal memo and active-task payload."""
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )

    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    adapter = cast("PrimitiveTileKernelAdapter", scheduler.adapter)
    valid_root &= type(adapter) is PrimitiveTileKernelAdapter
    valid_root &= tasks.valid_action_admission_state()

    def valid_key(value: object) -> bool:
        return (
            type(value) is tuple
            and len(value) == 2
            and type(value[0]) is str
            and value[0] in CAUSAL_FRAME_OPS
            and type(value[1]) is tuple
            and len(value[1]) <= 8
            and valid_frame_value(scheduler, value[1], approved)
        )

    for memo_key, memo_value in tasks.memo.items():
        valid = (
            valid_root
            and valid_key(memo_key)
            and valid_frame_value(scheduler, memo_value, approved)
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
    for active_key, active_value in tasks.active.items():
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
    for action in tasks.action_pending:
        valid = valid_root
        try:
            adapter.validate_action(action)
        except (TypeError, ValueError, KeyError, AttributeError, IndexError):
            valid = False
        if valid:
            approved.add(id(action))
        else:
            invalid.add((tasks.action_pending_owner, id(action)))
    for action, marker in tasks.action_admitted.items():
        valid = (
            valid_root
            and type(marker) is tuple
            and len(marker) == _ACTION_ADMISSION_SNAPSHOT_SIZE
        )
        try:
            adapter.validate_action(action)
            valid = valid and _action_admission_matches(
                marker,
                _action_admission_snapshot(
                    action,
                    adapter._action_record(action),
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


__all__ = ["audit_task_payloads", "valid_frame_value"]

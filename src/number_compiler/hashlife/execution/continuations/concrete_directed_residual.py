"""Certified constant continuations for directed concrete-port actions."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.concrete_port_records import (
    Residual,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.concrete_port_scheduler import (
        ConcretePortScheduler,
    )


def directed_children(
    scheduler: ConcretePortScheduler,
    action: FieldCellActionID,
    side: int,
) -> tuple[FieldCellActionID, FieldCellActionID] | None:
    """Return children when a side-one continuation is provably constant."""
    if side != 1:
        return None
    children = scheduler.adapter.children(action)
    law = getattr(scheduler.adapter, "output_ignores_port", None)
    if children is None or law is None:
        return None
    before, after = children
    return children if law(before, 0) and law(after, 0) else None


def validate_residual(
    scheduler: ConcretePortScheduler,
    record: Residual,
) -> None:
    """Validate a residual completely before an interner lookup."""
    scheduler.adapter.validate_action(record.action)
    scheduler.validate_side(record.side)
    scheduler.validate_atom(record.anchor_after)
    if record.constant_result is not None:
        children = directed_children(scheduler, record.action, record.side)
        if children is None:
            raise ValueError("constant residual lacks a directed-port certificate")
        if (
            record.previous is not None
            or record.cell is not None
            or record.layer is not None
            or record.reverse
        ):
            raise ValueError("constant residual retains occurrence history")
        scheduler.validate_action_state(
            children[1],
            record.side,
            record.constant_result,
        )
        return
    if record.previous is not None:
        scheduler.resolve_residual(record.previous)
    if record.cell is not None:
        scheduler.sources.resolve(record.cell)
    scheduler.layers.validate_optional(record.layer)


__all__ = ["directed_children", "validate_residual"]

"""Validated projection of a composed boundary onto its second temporal port."""

from __future__ import annotations

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.concrete_port_records import (
    PortAtom,
    PortStateID,
)
from number_compiler.hashlife.execution.continuations.concrete_port_scheduler import (
    ConcretePortScheduler,
)


def project_boundary(
    scheduler: ConcretePortScheduler,
    action: FieldCellActionID,
    side: int,
    state: PortAtom,
    opposite: PortAtom,
) -> PortAtom:
    """Apply a composed boundary residual after checking its complete wiring.

    ``opposite`` is the first child's opposite boundary, not a boundary of the
    whole temporal composition. Validation precedes even a warm residual hit.
    """
    if type(scheduler) is not ConcretePortScheduler:
        raise TypeError("boundary projection requires the shared port scheduler")
    scheduler.adapter.validate_action(action)
    side = scheduler.validate_side(side)
    scheduler.validate_action_state(action, side, state)
    children = scheduler.adapter.children(action)
    if children is None:
        raise ValueError("boundary projection requires a temporal composition")
    if type(state) is not PortStateID:
        raise TypeError("boundary projection requires a scoped composed state")
    port = scheduler.resolve_port(state)
    residual = scheduler.resolve_residual(port.residual)
    if residual.action != action or residual.side != side:
        raise ValueError("boundary residual has inconsistent temporal wiring")
    scheduler.validate_action_state(children[0], 1 - side, opposite)
    scheduler.validate_atom(opposite)
    return scheduler.run(("RES", action, side, port.residual, opposite))


__all__ = ["project_boundary"]

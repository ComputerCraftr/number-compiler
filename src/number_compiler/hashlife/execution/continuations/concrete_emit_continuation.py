"""Provider-layer construction after a temporal emission continuation."""

from __future__ import annotations

from typing import TYPE_CHECKING, cast

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.concrete_port_normalization import (
    normalize_request,
)
from number_compiler.hashlife.execution.continuations.concrete_port_records import (
    ComposedPort,
    PortAtom,
    ResidualBindingID,
)
from number_compiler.hashlife.execution.continuations.provider_layers import (
    ProviderLayer,
    ProviderLayerID,
)
from number_compiler.hashlife.execution.field_images import SourceCellID
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.concrete_port_scheduler import (
        ConcretePortScheduler,
    )


def emit_after_task(
    scheduler: ConcretePortScheduler,
    frame: tuple[object, ...],
    second_left: PortAtom,
    second_right: PortAtom,
) -> tuple[object, ...]:
    """Bind the first action as one canonical provider layer for the second."""
    layer = ProviderLayer(
        cast(FieldCellActionID, frame[2]),
        cast(PortAtom, frame[3]),
        cast(PortAtom, frame[4]),
    )
    layer_id = scheduler.layers.intern(
        cast(ProviderLayerID | None, frame[6]),
        layer,
    )
    return "EMIT", frame[1], second_left, second_right, frame[5], layer_id


def cached_residual(
    scheduler: ConcretePortScheduler,
    action: FieldCellActionID,
    side: int,
    residual: ResidualBindingID,
    argument: PortAtom,
) -> PortAtom | None:
    """Probe an already-complete normalized residual before scheduling it."""
    scheduler.adapter.validate_action(action)
    scheduler.validate_side(side)
    scheduler.resolve_residual(residual)
    scheduler.validate_atom(argument)
    children = scheduler.adapter.children(action)
    if children is None:
        raise ValueError("cached residual lookup requires a composed action")
    scheduler.validate_action_state(children[0], 1 - side, argument)
    key = normalize_request(
        scheduler,
        ("RES", action, side, residual, argument),
    )
    result = scheduler.cached_result(key)
    if result is not None:
        scheduler.ledger.bump(_execution_keys.CONCRETE_PORT_TASK_EARLY_HITS)
    return result


def composed_emit_tasks(
    scheduler: ConcretePortScheduler,
    frame: tuple[object, ...],
    left_argument: PortAtom,
    right_argument: PortAtom,
) -> tuple[tuple[object, ...], ...]:
    """Plan a composed emission after probing its complete residual parents."""
    action = cast(FieldCellActionID, frame[1])
    left = cast(ComposedPort, frame[2])
    right = cast(ComposedPort, frame[3])
    cell = cast(SourceCellID, frame[4])
    layer = cast(ProviderLayerID | None, frame[5])
    before, after = cast(
        tuple[FieldCellActionID, FieldCellActionID],
        scheduler.adapter.children(action),
    )
    continuation = (
        "EMIT_AFTER_RES",
        after,
        before,
        left.anchor,
        right.anchor,
        cell,
        layer,
    )
    constant = scheduler.resolve_residual(right.residual).constant_result
    if constant is not None:
        cached = cached_residual(
            scheduler,
            action,
            0,
            left.residual,
            left_argument,
        )
        if cached is not None:
            return (emit_after_task(scheduler, continuation, cached, constant),)
        return (
            (
                "EMIT_AFTER_LEFT_RES",
                after,
                before,
                left.anchor,
                right.anchor,
                cell,
                layer,
                constant,
            ),
            ("RES", action, 0, left.residual, left_argument),
        )
    return (
        continuation,
        ("RES", action, 1, right.residual, right_argument),
        ("RES", action, 0, left.residual, left_argument),
    )


__all__ = ["cached_residual", "composed_emit_tasks", "emit_after_task"]

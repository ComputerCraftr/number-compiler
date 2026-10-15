"""Erase certified irrelevant port dependencies before observation lookup."""

from __future__ import annotations

from dataclasses import replace
from typing import TYPE_CHECKING, cast

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.concrete_port_records import (
    PortAtom,
    VirtualBinding,
)
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.concrete_port_scheduler import (
        ConcretePortScheduler,
    )


def ignored_initial(
    scheduler: ConcretePortScheduler,
    action: FieldCellActionID,
    side: int,
) -> PortAtom | None:
    law = getattr(scheduler.adapter, "output_ignores_port", None)
    if law is None or not law(action, side):
        return None
    # Preparation builds only the logarithmic temporal DAG's initial ports.
    # Never invoke the scheduler from inside its own dependency loop.
    return scheduler._memo.get(("INIT", action, side))


def normalize_binding(
    scheduler: ConcretePortScheduler,
    binding: VirtualBinding,
) -> VirtualBinding:
    children = scheduler.adapter.children(binding.parent)
    if children is None:
        raise ValueError("a virtual binding requires a temporal composition")
    before = children[0]
    initial = ignored_initial(scheduler, before, 0)
    if initial is None:
        return binding
    left = binding.anchor if binding.side == 0 else binding.argument
    scheduler._validate_action_state(before, 0, left)
    if left == initial:
        return binding
    scheduler.ledger.bump(_execution_keys.CONCRETE_IRRELEVANT_PORT_ELISIONS)
    return (
        replace(binding, anchor=initial)
        if binding.side == 0
        else replace(binding, argument=initial)
    )


def normalize_request(
    scheduler: ConcretePortScheduler,
    frame: tuple[object, ...],
) -> tuple[object, ...]:
    tag = frame[0]
    if tag == "EMIT":
        action = cast(FieldCellActionID, frame[1])
        initial = ignored_initial(scheduler, action, 0)
        if initial is not None:
            scheduler._validate_action_state(action, 0, cast(PortAtom, frame[2]))
            return (*frame[:2], initial, *frame[3:])
    elif tag in ("RES", "SECOND"):
        action = cast(FieldCellActionID, frame[1])
        children = scheduler.adapter.children(action)
        if children is not None and (tag == "SECOND" or frame[2] == 1):
            initial = ignored_initial(scheduler, children[0], 0)
            if initial is not None:
                slot = 4 if tag == "RES" else (6 if frame[2] == 0 else 7)
                scheduler._validate_action_state(
                    children[0],
                    0,
                    cast(PortAtom, frame[slot]),
                )
                return (*frame[:slot], initial, *frame[slot + 1 :])
    elif tag in ("VIRTUAL", "VIRTUAL_APPLY", "VIRTUAL_COMPOSE"):
        slots = (
            (1,)
            if tag == "VIRTUAL"
            else ((2,) if tag == "VIRTUAL_APPLY" else (1, 3, 4))
        )
        parts = list(frame)
        for slot in slots:
            parts[slot] = normalize_binding(
                scheduler, cast(VirtualBinding, frame[slot])
            )
        return tuple(parts)
    return frame

"""Iterative concrete execution of opaque composed higher operations."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING, cast

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.higher_values import (
    RuntimeActionFunction,
    RuntimeAtom,
    RuntimeFunction,
    RuntimeTableFunction,
    RuntimeValueID,
)
from number_compiler.hashlife.execution.continuations.operation_dependencies import (
    advance_operation,
)
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.higher_semantic import (
        HigherSemanticArena,
    )


# This is a bound on a primitive local port, not a composed continuation
# universe.  Decimal reverse/add has twenty pair symbols and 43 states on its
# larger directed primitive port; admitting that fixed kernel interface keeps
# T^2 on the extensional carrier.  Higher temporal domains remain recursive
# and are never enumerated here.
MAX_EXTENSIONAL_TABLE_DOMAIN = 64


def singleton_state(
    arena: HigherSemanticArena,
    machine: OperationMachine,
    action: FieldCellActionID,
    side: int,
) -> bool:
    """Return whether the recursive state sort has exactly one inhabitant."""
    key = action, side
    cached = machine.singleton_states.get(key)
    if cached is not None:
        return cached
    pending: list[tuple[FieldCellActionID, bool]] = [(action, False)]
    while pending:
        current, ready = pending.pop()
        current_key = current, side
        if current_key in machine.singleton_states:
            continue
        children = operation_children(arena, machine, current)
        if children is None:
            machine.singleton_states[current_key] = (
                arena.schema.state_count(current, side) == 1
            )
            continue
        if not ready:
            pending.append((current, True))
            pending.extend((child, False) for child in children)
            continue
        machine.singleton_states[current_key] = all(
            machine.singleton_states[child, side] for child in children
        )
    return machine.singleton_states[key]


def constant_anchor(
    arena: HigherSemanticArena,
    machine: OperationMachine,
    function: RuntimeValueID,
) -> RuntimeAtom | None:
    if function in machine.constant_anchors:
        return machine.constant_anchors[function]
    record = arena.runtime_values.resolve(function)
    if type(record) is RuntimeActionFunction and record.kind == "constant":
        result: RuntimeAtom | None = record.anchor
        machine.constant_anchors[function] = result
        return result
    if type(record) is RuntimeTableFunction:
        result = (
            record.outputs[0]
            if all(value == record.outputs[0] for value in record.outputs[1:])
            else None
        )
        machine.constant_anchors[function] = result
        return result
    if type(record) is RuntimeFunction:
        syntax = arena.function_record(record.function)
        if not syntax.parameter_used:
            environment = arena.runtime_values.project_environment(
                record.environment,
                tuple(item.local_id for item in syntax.free_variables),
                projection=-(record.function.local_id + 2),
            )
            cached = arena.runtime_values.evaluations.get(
                (syntax.body.local_id, environment)
            )
            if cached is not None:
                arena.runtime_values.validate_atom(cached)
                machine.constant_anchors[function] = cached
                return cached
            # The function is extensionally constant, but its body has not
            # been evaluated in this observation yet.  Do not memoize this as
            # a negative result: callers can apply the constant function to
            # any correctly sorted value and thereby avoid constructing the
            # otherwise discarded opposite-side transition.
            return None
    machine.constant_anchors[function] = None
    return None


def is_constant_function(
    arena: HigherSemanticArena,
    function: RuntimeValueID,
) -> bool:
    """Recognize a constant continuation without evaluating its body."""
    record = arena.runtime_values.resolve(function)
    if type(record) is RuntimeActionFunction:
        return record.kind == "constant"
    if type(record) is RuntimeTableFunction:
        return all(value == record.outputs[0] for value in record.outputs[1:])
    if type(record) is RuntimeFunction:
        return not arena.function_record(record.function).parameter_used
    return False


@dataclass(slots=True)
class OperationMachine:
    tasks: list[tuple[object, ...]]
    results: list[RuntimeAtom]
    children: dict[
        FieldCellActionID,
        tuple[FieldCellActionID, FieldCellActionID] | None,
    ]
    singleton_states: dict[tuple[FieldCellActionID, int], bool]
    constant_anchors: dict[RuntimeValueID, RuntimeAtom | None]


def operation_children(
    arena: HigherSemanticArena,
    machine: OperationMachine,
    action: FieldCellActionID,
) -> tuple[FieldCellActionID, FieldCellActionID] | None:
    """Resolve one action edge once per transient operation machine."""
    try:
        return machine.children[action]
    except KeyError:
        result = arena.schema.children(action)
        machine.children[action] = result
        return result


def has_primitive_children(
    arena: HigherSemanticArena,
    machine: OperationMachine,
    action: FieldCellActionID,
) -> tuple[FieldCellActionID, FieldCellActionID] | None:
    """Return a bottom temporal diamond whose state domain stays bounded."""
    children = operation_children(arena, machine, action)
    if children is None:
        return None
    return (
        children
        if all(operation_children(arena, machine, child) is None for child in children)
        else None
    )


@dataclass(frozen=True, slots=True)
class RuntimeFunctionRequest:
    function: RuntimeFunction
    argument: RuntimeAtom


def start_operation(
    operation: str,
    action: FieldCellActionID,
    side: int,
    arguments: tuple[RuntimeAtom, ...],
) -> OperationMachine:
    return OperationMachine(
        [(operation, action, side, *arguments)],
        [],
        {},
        {},
        {},
    )


def start_function_application(
    function: RuntimeValueID,
    argument: RuntimeAtom,
) -> OperationMachine:
    return OperationMachine([("apply", function, argument)], [], {}, {}, {})


def evaluate_operation(
    arena: HigherSemanticArena,
    operation: str,
    action: FieldCellActionID,
    side: int,
    arguments: tuple[RuntimeAtom, ...],
) -> RuntimeAtom:
    """Evaluate an operation that does not cross a syntax continuation."""
    result = advance_operation(
        arena,
        start_operation(operation, action, side, arguments),
    )
    if isinstance(result, RuntimeFunctionRequest):
        raise ValueError("operation requires the unified continuation scheduler")
    return result


def force_value(arena: HigherSemanticArena, value: RuntimeAtom) -> RuntimeAtom:
    """Resolve one summary-backed state with the unified iterative scheduler."""
    arena.runtime_values.validate_atom(value)
    if type(value) is int:
        return value
    result = advance_operation(
        arena,
        OperationMachine([("force", value)], [], {}, {}, {}),
    )
    if isinstance(result, RuntimeFunctionRequest):
        raise ValueError("summary forcing reached a syntax continuation")
    return result


__all__ = [
    "OperationMachine",
    "RuntimeFunctionRequest",
    "advance_operation",
    "evaluate_operation",
    "force_value",
    "start_function_application",
    "start_operation",
]


def publish_temporal_table(
    arena: HigherSemanticArena, machine: OperationMachine, task: tuple[object, ...]
) -> None:
    """Publish a resolved primitive temporal summary with its finite port table."""
    values = arena.runtime_values
    results = machine.results
    action, current_side, domain = (
        cast(FieldCellActionID, task[1]),
        cast(int, task[2]),
        cast(int, task[3]),
    )
    outputs = results[-domain:]
    del results[-domain:]
    anchor = results.pop()
    if type(anchor) is not int or any(type(value) is not int for value in outputs):
        raise ValueError("primitive temporal summary returned structured ports")
    continuation = values.table_function(
        action, current_side, cast(tuple[int, ...], tuple(outputs))
    )
    results.append(values.pair(anchor, continuation))
    arena.ledger.bump(_execution_keys.HIGHER_EXTENSIONAL_TABLE_PUBLICATIONS)


def canonical_operation_task(
    arena: HigherSemanticArena, task: tuple[object, ...]
) -> tuple[object, ...]:
    """Normalize structured arguments before the existing operation memo probe."""
    values = arena.runtime_values
    tag = task[0]
    if tag == "step":
        task = (
            *task[:3],
            values.canonical_atom(cast(RuntimeAtom, task[3])),
            task[4],
        )
    elif tag == "emit":
        task = (
            *task[:3],
            values.canonical_atom(cast(RuntimeAtom, task[3])),
            task[4],
            values.canonical_atom(cast(RuntimeAtom, task[5])),
        )
    elif tag == "apply":
        task = (tag, task[1], values.canonical_atom(cast(RuntimeAtom, task[2])))
    return task

"""Experimental scalar observation through a binary temporal action diamond.

This is the local, output-complete part of temporal-over-spatial HashLife.  A
composed boundary is an anchor for the first action together with a bounded
continuation for the second action.  The evaluator consumes those canonical
objects directly; it never emits a midpoint field or advances a generation.
"""

from __future__ import annotations

from collections.abc import Callable
from typing import cast

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.higher_operations import (
    RuntimeFunctionRequest,
    evaluate_operation,
    force_value,
    start_function_application,
)
from number_compiler.hashlife.execution.continuations.higher_semantic import (
    HigherSemanticArena,
)
from number_compiler.hashlife.execution.continuations.higher_values import (
    RuntimeActionFunction,
    RuntimeAtom,
    RuntimePair,
    RuntimeTableFunction,
    RuntimeValueID,
)
from number_compiler.hashlife.execution.continuations.operation_dependencies import (
    advance_operation,
)


def _constant_continuation(
    semantics: HigherSemanticArena,
    function: RuntimeValueID,
) -> tuple[bool, RuntimeAtom]:
    record = semantics.runtime_values.resolve(function)
    if type(record) is RuntimeActionFunction and record.kind == "constant":
        return True, record.anchor
    if type(record) is RuntimeTableFunction and all(
        value == record.outputs[0] for value in record.outputs[1:]
    ):
        return True, record.outputs[0]
    return False, 0


def _apply_continuation(
    semantics: HigherSemanticArena,
    function: RuntimeValueID,
    argument: RuntimeAtom,
) -> RuntimeAtom:
    machine = start_function_application(function, argument)
    result = advance_operation(semantics, machine)
    if isinstance(result, RuntimeFunctionRequest):
        raise ValueError("temporal image retained an opaque syntax continuation")
    return result


def evaluate_temporal_leaf(
    semantics: HigherSemanticArena,
    action: FieldCellActionID,
    symbol: int,
    left: RuntimeAtom,
    right: RuntimeAtom,
    *,
    prefix_probe: Callable[[FieldCellActionID], None] | None = None,
) -> int:
    """Evaluate one coordinate through temporal diamonds without recursion."""
    semantics.schema.validate_action(action)
    if type(symbol) is not int:
        raise TypeError("temporal output symbol must be an exact integer")
    semantics.runtime_values.validate_atom(left)
    semantics.runtime_values.validate_atom(right)
    tasks: list[tuple[object, ...]] = [
        ("emit", action, symbol, left, right, True),
    ]
    results: list[int] = []
    while tasks:
        task = tasks.pop()
        if task[0] == "publish":
            if not results:
                raise AssertionError("temporal diamond lost its complete output")
            semantics.runtime_values.publish_operation(
                cast(tuple[object, ...], task[1]),
                results[-1],
            )
            semantics.ledger.bump("temporal_leaf_parent_publications")
            continue
        if task[0] == "after":
            after = cast(FieldCellActionID, task[1])
            after_left = cast(RuntimeAtom, task[2])
            after_right = cast(RuntimeAtom, task[3])
            if not results:
                raise AssertionError("temporal diamond lost its prefix output")
            tasks.append(
                (
                    "emit",
                    after,
                    results.pop(),
                    after_left,
                    after_right,
                    False,
                )
            )
            continue
        current = cast(FieldCellActionID, task[1])
        current_symbol = cast(int, task[2])
        current_left = semantics.runtime_values.canonical_atom(
            cast(RuntimeAtom, task[3])
        )
        current_right = semantics.runtime_values.canonical_atom(
            cast(RuntimeAtom, task[4])
        )
        require_prefix = cast(bool, task[5])
        # Carry/interface composition may already have evaluated this complete
        # output action. Probe its semantic operation key before descending.
        # This shares the existing memo; it publishes no coordinate values.
        key = (
            "emit",
            current,
            -1,
            current_left,
            current_symbol,
            current_right,
        )
        cached = semantics.runtime_values.operations.get(key)
        if cached is not None:
            if type(cached) is not int:
                raise ValueError("cached temporal emission has another result sort")
            semantics.ledger.bump("temporal_leaf_parent_hits")
            results.append(cached)
            continue
        children = semantics.schema.children(current)
        if children is None:
            result = evaluate_operation(
                semantics,
                "emit",
                current,
                -1,
                (current_left, current_symbol, current_right),
            )
            if type(result) is not int:
                raise ValueError("temporal primitive output is not a symbol")
            results.append(result)
            continue
        before, after = children
        if require_prefix and prefix_probe is not None:
            prefix_probe(before)
        left_value = force_value(semantics, current_left)
        right_value = force_value(semantics, current_right)
        if (
            type(left_value) is not RuntimeValueID
            or type(right_value) is not RuntimeValueID
        ):
            raise ValueError("temporal boundary lost its composed pair")
        left_pair = semantics.runtime_values.resolve(left_value)
        right_pair = semantics.runtime_values.resolve(right_value)
        if type(left_pair) is not RuntimePair or type(right_pair) is not RuntimePair:
            raise ValueError("temporal boundary is not a canonical pair")
        left_constant, left_after = _constant_continuation(
            semantics,
            left_pair.continuation,
        )
        if not left_constant:
            left_argument = evaluate_operation(
                semantics,
                "step",
                before,
                1,
                (right_pair.anchor, current_symbol),
            )
            left_after = _apply_continuation(
                semantics,
                left_pair.continuation,
                left_argument,
            )
        right_constant, right_after = _constant_continuation(
            semantics,
            right_pair.continuation,
        )
        if not right_constant:
            right_argument = evaluate_operation(
                semantics,
                "step",
                before,
                0,
                (left_pair.anchor, current_symbol),
            )
            right_after = _apply_continuation(
                semantics,
                right_pair.continuation,
                right_argument,
            )
        semantics.ledger.bump(
            "temporal_constant_argument_elisions",
            int(left_constant) + int(right_constant),
        )
        # Publish the completed semantic action/port result, not a coordinate
        # binding. Without this continuation the parent probe above can only
        # reuse emissions produced by a different evaluator.
        tasks.append(("publish", key))
        tasks.append(("after", after, left_after, right_after))
        tasks.append(
            (
                "emit",
                before,
                current_symbol,
                left_pair.anchor,
                right_pair.anchor,
                False,
            )
        )
        semantics.ledger.bump("temporal_leaf_diamond_descents")
    if len(results) != 1:
        raise AssertionError("temporal diamond returned another arity")
    return results[0]


__all__ = ["evaluate_temporal_leaf"]

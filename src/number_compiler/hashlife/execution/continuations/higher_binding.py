"""Iterative binding analysis for higher semantic expressions."""

from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.higher_semantic import (
        HigherSemanticArena,
    )
    from number_compiler.hashlife.execution.continuations.higher_types import (
        FieldStateSort,
        HigherExpressionID,
    )


def binder_depth(
    arena: HigherSemanticArena,
    expression: HigherExpressionID,
    sort: FieldStateSort,
) -> int:
    pending = [expression.local_id]
    seen: set[int] = set()
    depth = 0
    while pending:
        local_id = pending.pop()
        if local_id in seen:
            continue
        seen.add(local_id)
        node = arena._expressions[local_id]
        pending.extend(node.children)
        if node.function is None:
            continue
        function = arena.function_record(node.function)
        pending.append(function.body.local_id)
        parameter = arena.expression(function.parameter)
        if parameter.sort == sort and parameter.kind == "bound":
            depth = max(depth, parameter.value + 1)
    return depth


def free_variables(
    arena: HigherSemanticArena,
    expression: HigherExpressionID,
) -> tuple[HigherExpressionID, ...]:
    arena.expression(expression)
    return tuple(
        arena._expression_handle(item)
        for item in arena._expression_free_ids[expression.local_id]
    )


def reachable_size(
    arena: HigherSemanticArena,
    expression: HigherExpressionID,
    *,
    limit: int,
) -> int | None:
    """Return the shared DAG size unless it exceeds a fixed local bound."""
    pending = [expression.local_id]
    seen: set[int] = set()
    while pending:
        local_id = pending.pop()
        if local_id in seen:
            continue
        seen.add(local_id)
        if len(seen) > limit:
            return None
        node = arena._expressions[local_id]
        pending.extend(node.children)
        if node.function is not None:
            pending.append(arena.function_record(node.function).body.local_id)
    return len(seen)


__all__ = ["binder_depth", "free_variables", "reachable_size"]

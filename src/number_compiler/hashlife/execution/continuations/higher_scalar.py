"""Canonical bounded-scalar constructors for higher semantic programs."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.execution.continuations.higher_types import (
    FieldAtomSort,
    FieldSymbolSort,
    HigherExpression,
    HigherExpressionID,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.higher_semantic import (
        HigherSemanticArena,
    )


def canonical_equal_constant(
    arena: HigherSemanticArena,
    value: HigherExpressionID,
    expected: int,
) -> HigherExpressionID:
    node = arena.expression(value)
    sort = node.sort
    if type(sort) is FieldAtomSort:
        cardinality = sort.cardinality
    elif type(sort) is FieldSymbolSort:
        cardinality = sort.blank + 1
    else:
        raise ValueError("higher equality requires a bounded scalar")
    if type(expected) is not int or not 0 <= expected < cardinality:
        raise ValueError("higher equality constant is outside its domain")
    if node.kind in ("constant", "symbol"):
        return arena.constant(
            FieldAtomSort("boolean", 2),
            int(node.value == expected),
        )
    return arena.intern_expression(
        HigherExpression(
            "equal-constant",
            FieldAtomSort("boolean", 2),
            (value.local_id,),
            value=expected,
        )
    )


def canonical_add_constant(
    arena: HigherSemanticArena,
    value: HigherExpressionID,
    offset: int,
    output: FieldAtomSort,
) -> HigherExpressionID:
    node = arena.expression(value)
    if type(node.sort) is not FieldAtomSort or type(offset) is not int:
        raise ValueError("higher addition requires a bounded atom and exact offset")
    arena.validate_sort(output)
    if offset == 0:
        return arena.retag(value, output)
    if node.kind == "constant":
        result = node.value + offset
        if not 0 <= result < output.cardinality:
            raise ValueError("higher constant addition exceeds its output sort")
        return arena.constant(output, result)
    # Widening is an exact identity. Removing only tags preserves every
    # bounded addition's independently checked output domain.
    source = value
    source_node = arena.expression(source)
    while source_node.kind == "retag":
        source = arena.expression_id(source_node.children[0])
        source_node = arena.expression(source)
    return arena.intern_expression(
        HigherExpression(
            "add-constant",
            output,
            (source.local_id,),
            value=offset,
        )
    )


def canonical_retag(
    arena: HigherSemanticArena,
    value: HigherExpressionID,
    output: FieldAtomSort,
) -> HigherExpressionID:
    node = arena.expression(value)
    arena.validate_sort(output)
    if (
        type(node.sort) is not FieldAtomSort
        or output.cardinality < node.sort.cardinality
    ):
        raise ValueError("higher retag cannot narrow or restructure a value")
    if node.sort == output:
        return value
    while node.kind == "retag":
        value = arena.expression_id(node.children[0])
        node = arena.expression(value)
    if node.sort == output:
        return value
    return arena.intern_expression(HigherExpression("retag", output, (value.local_id,)))


def canonical_select(
    arena: HigherSemanticArena,
    condition: HigherExpressionID,
    yes: HigherExpressionID,
    no: HigherExpressionID,
) -> HigherExpressionID:
    condition_node = arena.expression(condition)
    yes_node, no_node = arena.expression(yes), arena.expression(no)
    if (
        condition_node.sort != FieldAtomSort("boolean", 2)
        or yes_node.sort != no_node.sort
    ):
        raise ValueError("higher selection requires a boolean and equal branches")
    if yes == no:
        return yes
    if condition_node.kind == "constant":
        return yes if condition_node.value else no
    while yes_node.kind == "select" and yes_node.children[0] == condition.local_id:
        yes = arena.expression_id(yes_node.children[1])
        yes_node = arena.expression(yes)
    while no_node.kind == "select" and no_node.children[0] == condition.local_id:
        no = arena.expression_id(no_node.children[2])
        no_node = arena.expression(no)
    if yes == no:
        return yes
    return arena.intern_expression(
        HigherExpression(
            "select",
            yes_node.sort,
            (condition.local_id, yes.local_id, no.local_id),
        )
    )


__all__ = [
    "canonical_add_constant",
    "canonical_equal_constant",
    "canonical_retag",
    "canonical_select",
]

"""Boundary validation for canonical higher-expression interning."""

from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.higher_types import (
    HigherExpression,
    HigherFunctionID,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.higher_types import (
        HigherActionSchema,
        HigherSort,
    )


_CHILD_COUNTS: dict[str, int | None] = {
    "variable": None,
    "bound": 0,
    "literal": 0,
    "symbol": 0,
    "constant": 0,
    "pair": 2,
    "anchor": 1,
    "continuation": 1,
    "function": 0,
    "apply": 2,
    "bind-free": 2,
    "select": 3,
    "equal-constant": 1,
    "add-constant": 1,
    "retag": 1,
    "primitive-step": 2,
    "primitive-emit": 3,
    "action-initial": 0,
    "action-step": 2,
    "action-emit": 3,
}
_ACTION_KINDS = frozenset(
    (
        "literal",
        "symbol",
        "pair",
        "anchor",
        "continuation",
        "primitive-step",
        "primitive-emit",
        "action-initial",
        "action-step",
        "action-emit",
    )
)
_SIDE_KINDS = frozenset(
    (
        "literal",
        "pair",
        "anchor",
        "continuation",
        "primitive-step",
        "action-initial",
        "action-step",
    )
)


def validate_higher_expression_record(
    record: HigherExpression,
    *,
    schema: HigherActionSchema,
    expression_count: int,
    validate_sort: Callable[[HigherSort], None],
    resolve_function: Callable[[HigherFunctionID], object],
) -> None:
    """Reject malformed records before they enter the expression interner."""
    if type(record) is not HigherExpression:
        raise TypeError("higher expression interning requires a canonical record")
    if type(record.kind) is not str or record.kind not in _CHILD_COUNTS:
        raise ValueError("higher expression has an unknown semantic operation")
    validate_sort(record.sort)
    if type(record.children) is not tuple or any(
        type(child) is not int or not 0 <= child < expression_count
        for child in record.children
    ):
        raise ValueError("higher expression children must be allocated earlier nodes")
    expected_children = _CHILD_COUNTS[record.kind]
    if expected_children is not None and len(record.children) != expected_children:
        raise ValueError("higher expression has the wrong child arity")
    if type(record.side) is not int or record.side not in (-1, 0, 1):
        raise ValueError("higher expression side is outside its finite domain")
    if type(record.value) is not int or type(record.role) is not str:
        raise TypeError("higher expression scalar fields have invalid types")
    if record.kind == "variable":
        if not record.role or len(record.role) > 128 or record.value != -1:
            raise ValueError("higher variable record has invalid port metadata")
    elif record.role:
        raise ValueError("non-variable expression carries a free-port role")
    if record.kind in _SIDE_KINDS:
        if record.side not in (0, 1):
            raise ValueError("higher expression requires a directed side")
    elif record.side != -1:
        raise ValueError("side is present on a side-independent expression")
    if record.kind == "bound":
        if record.value < 0:
            raise ValueError("bound expression depth must be nonnegative")
    elif record.kind in ("literal", "symbol", "constant", "equal-constant"):
        if record.value < 0:
            raise ValueError("higher expression value must be nonnegative")
    elif record.kind == "bind-free":
        if record.value < 0:
            raise ValueError("higher binding variable ID must be nonnegative")
    elif (
        record.kind not in ("add-constant", "variable", "bound") and record.value != -1
    ):
        raise ValueError("unused higher expression value must retain its sentinel")
    if record.kind in _ACTION_KINDS:
        if type(record.action) is not FieldCellActionID:
            raise TypeError("higher action expression requires a scoped action")
        schema.validate_action(record.action)
    elif record.action is not None:
        raise ValueError("action is attached to a non-action expression")
    if record.kind == "function":
        function = record.function
        if type(function) is not HigherFunctionID:
            raise TypeError("higher function expression requires a scoped function")
        resolve_function(function)
    elif record.function is not None:
        raise ValueError("function is attached to a non-function expression")


__all__ = ["validate_higher_expression_record"]

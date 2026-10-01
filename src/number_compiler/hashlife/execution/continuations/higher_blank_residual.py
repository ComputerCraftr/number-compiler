"""Admission for the primitive first-blank residual law."""

from __future__ import annotations

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.higher_types import (
    FieldSymbolSort,
    HigherActionSchema,
    HigherExpression,
)


def primitive_blank_run_admitted(
    schema: HigherActionSchema,
    action: FieldCellActionID,
) -> bool:
    """Return whether an atomic action exposes the complete blank-tail law.

    The optional hook is supplied by an arithmetic owner that authenticates its
    action and primitive kernel. A composite action is never admitted here;
    its temporal residual needs a separate construction and proof.
    """
    hook = getattr(schema, "primitive_blank_run", None)
    if not callable(hook):
        return False
    result = hook(action)
    if type(result) is not bool:
        raise TypeError("blank-run admission must be Boolean")
    return result


def is_idempotent_blank_transfer(
    schema: HigherActionSchema,
    action: FieldCellActionID,
    side: int,
    state: HigherExpression,
    symbol: HigherExpression,
    symbol_id: int,
) -> bool:
    """Recognize exactly one repeated blank transfer on the same port."""
    if (
        symbol.kind != "symbol"
        or type(symbol.sort) is not FieldSymbolSort
        or symbol.value != symbol.sort.blank
    ):
        return False
    return (
        primitive_blank_run_admitted(schema, action)
        and state.kind == "primitive-step"
        and state.action == action
        and state.side == side
        and len(state.children) == 2
        and state.children[1] == symbol_id
    )


__all__ = ["is_idempotent_blank_transfer", "primitive_blank_run_admitted"]

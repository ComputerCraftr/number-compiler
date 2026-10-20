"""Validation for retained higher-runtime operation memo entries."""

from __future__ import annotations

from typing import cast

from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.higher_semantic import (
    HigherSemanticArena,
)
from number_compiler.hashlife.execution.continuations.higher_values import (
    RuntimeAtom,
    RuntimeValueArena,
    RuntimeValueID,
)


def valid_higher_operation(
    arena: RuntimeValueArena,
    semantics: HigherSemanticArena | None,
    operation: object,
    result: RuntimeAtom,
) -> bool:
    """Validate one canonical operation key and its scoped result."""
    try:
        if not is_exact_object_tuple(operation) or semantics is None:
            return False
        tag = operation[0]
        arities = {"initial": 3, "step": 5, "emit": 6, "apply": 3, "force": 2}
        if type(tag) is not str or tag not in arities or len(operation) != arities[tag]:
            return False
        if tag == "force":
            function = operation[1]
            if type(function) is not RuntimeValueID:
                return False
            arena.resolve(function)
        elif tag == "apply":
            function, argument = operation[1:]
            if type(function) is not RuntimeValueID:
                return False
            arena.resolve(function)
            arena.validate_atom(cast(RuntimeAtom, argument))
        else:
            action, side = operation[1:3]
            semantics.schema.validate_action(cast(FieldCellActionID, action))
            if type(side) is not int or side not in (-1, 0, 1):
                return False
            for argument in operation[3:]:
                arena.validate_atom(cast(RuntimeAtom, argument))
        arena.validate_atom(result)
    except (TypeError, ValueError, IndexError, KeyError, AttributeError):
        return False
    return True


__all__ = ["valid_higher_operation"]

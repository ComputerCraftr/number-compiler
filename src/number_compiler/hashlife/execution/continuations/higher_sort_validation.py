"""Shared structural validation for higher semantic sorts."""

from __future__ import annotations

from number_compiler.hashlife.execution.continuations.higher_types import (
    FieldAtomSort,
    FieldFunctionSort,
    FieldStateSort,
    FieldSymbolSort,
    HigherActionSchema,
    HigherSort,
)
from number_compiler.resources.higher_readonly import audit_validate_action


def validate_higher_sort(
    schema: HigherActionSchema,
    sort: HigherSort,
    *,
    readonly: bool = False,
) -> None:
    pending: list[HigherSort] = [sort]
    while pending:
        current = pending.pop()
        if type(current) is FieldStateSort:
            if readonly:
                audit_validate_action(schema, current.action)
            else:
                schema.validate_action(current.action)
            if type(current.side) is not int or current.side not in (0, 1):
                raise ValueError("field-state direction must be zero or one")
        elif type(current) is FieldFunctionSort:
            pending.extend((current.codomain, current.domain))
        elif type(current) is FieldSymbolSort:
            if (
                type(current.base) is not int
                or current.base < 2
                or type(current.blank) is not int
                or not 1 <= current.blank < 1 << 64
            ):
                raise ValueError("invalid higher symbol sort")
        elif type(current) is FieldAtomSort:
            if (
                type(current.role) is not str
                or not current.role
                or len(current.role) > 128
                or type(current.cardinality) is not int
                or not 1 <= current.cardinality <= 1 << 64
            ):
                raise ValueError("invalid higher bounded-atom sort")
        else:
            raise TypeError("unknown higher semantic sort")

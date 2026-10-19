"""Read-only schema calls used by retained higher-semantic audits."""

from __future__ import annotations

from collections.abc import Mapping
from typing import Protocol, runtime_checkable

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.higher_types import (
    HigherActionSchema,
)


@runtime_checkable
class ReadonlyActionValidation(Protocol):
    """Optional schema operation that authenticates without memo publication."""

    def validate_action_readonly(self, action: FieldCellActionID) -> None: ...


def audit_validate_action(
    schema: HigherActionSchema, action: FieldCellActionID
) -> None:
    """Use the declared read-only authority when the schema provides it."""
    if isinstance(schema, ReadonlyActionValidation):
        schema.validate_action_readonly(action)
    else:
        schema.validate_action(action)


def audit_identity_index(mapping: object, record: object, index: int) -> bool:
    """Check an interner entry without mutating it, even after record corruption."""
    if not isinstance(mapping, Mapping):
        return False
    try:
        found = mapping.get(record)
        return type(found) is int and found == index
    except (KeyError, TypeError, AttributeError):
        return any(
            key is record and type(value) is int and value == index
            for key, value in mapping.items()
        )


__all__ = ["audit_identity_index", "audit_validate_action"]

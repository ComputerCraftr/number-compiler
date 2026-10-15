"""Stable behavior tags owned by the reverse/add cylinder semantics."""

from typing import Final

from number_compiler.arithmetic.contracts.semantic_identity import (
    SemanticIdentityDomain,
)

REVERSE_ADD_SOURCE_CARRY_TAG: Final[str] = (
    SemanticIdentityDomain.REVERSE_ADD_SOURCE_CARRY.value
)
REVERSE_ADD_PRIMITIVE_CYLINDER_CLAUSE_TAG: Final[str] = (
    SemanticIdentityDomain.REVERSE_ADD_PRIMITIVE_CYLINDER_CLAUSE.value
)
REVERSE_CENTERED_RADIAL_ACTION_TAG: Final[str] = (
    SemanticIdentityDomain.REVERSE_CENTERED_RADIAL_ACTION.value
)
REVERSE_FIELD_OCCURRENCE_TAG: Final[str] = "reverse-field-occurrence-v1"

__all__ = [
    "REVERSE_ADD_PRIMITIVE_CYLINDER_CLAUSE_TAG",
    "REVERSE_ADD_SOURCE_CARRY_TAG",
    "REVERSE_CENTERED_RADIAL_ACTION_TAG",
    "REVERSE_FIELD_OCCURRENCE_TAG",
]

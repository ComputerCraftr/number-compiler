"""Public immutable records used by the factored finite Boolean arena."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle
from number_compiler.arithmetic.functions.finite_function_types import (
    FunctionSignature,
    SemanticFunctionID,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable


@dataclass(frozen=True, slots=True)
class FactoredFunctionID(ArenaHandle):
    """Canonical fixed-bit finite output in one semantic arena."""


@dataclass(frozen=True, slots=True)
class FactoredFunction:
    signature: FunctionSignature
    bits: tuple[SemanticFunctionID, ...]
    valid: SemanticFunctionID


@dataclass(frozen=True, slots=True)
class BinaryDivision:
    remainder: FactoredFunctionID
    quotient: FactoredFunctionID


@dataclass(frozen=True, slots=True)
class BitSubstitutionKey:
    function: FactoredFunctionID
    replacements: tuple[tuple[PortVariable, FactoredFunctionID], ...]


@dataclass(frozen=True, slots=True)
class PendingFunction:
    signature: FunctionSignature
    bits: tuple[int, ...]
    valid: int


__all__ = [
    "BinaryDivision",
    "BitSubstitutionKey",
    "FactoredFunction",
    "FactoredFunctionID",
    "PendingFunction",
]

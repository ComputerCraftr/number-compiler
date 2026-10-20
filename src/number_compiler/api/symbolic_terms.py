"""Demanded symbolic term text, separate from exact integer projection metadata."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.family_identity import FamilyId
from number_compiler.arithmetic.fields.symbolic_extent import integer_text

if TYPE_CHECKING:
    from number_compiler.api.number_api import (
        ProjectedNumberTerm,
        ProjectionMetrics,
        TermPayload,
    )


@dataclass(frozen=True, slots=True)
class SymbolicExpression:
    family: FamilyId | None = None
    index: int = 0
    parameter: int | None = None
    radix: int | None = None
    literal: str | None = None

    def render(self, index_text: str | None = None) -> str:
        if self.literal is not None:
            return self.literal
        coordinate = integer_text(self.index) if index_text is None else index_text
        if self.family is FamilyId.A367620:
            return f"A367620[{coordinate}]"
        if self.family is FamilyId.REVERSE_ADD:
            return f"reverse_add(seed={self.parameter},base={self.radix})[{coordinate}]"
        if self.family is FamilyId.DOUBLE_REVERSE:
            return f"double_reverse10(seed={self.parameter})[{coordinate}]"
        if self.family is FamilyId.COLLATZ:
            return f"collatz(seed={self.parameter})[{coordinate}]"
        if self.family is FamilyId.ANTIHYDRA:
            return f"antihydra_arithmetic(source=blank)[{coordinate}]"
        if self.family is FamilyId.PRIME:
            return f"prime_at_or_after(start={self.parameter})[{coordinate}]"
        if self.family is FamilyId.FERMAT:
            power = coordinate if index_text is None else f"({coordinate})"
            return f"2^(2^{power})+1"
        if self.family is FamilyId.MERSENNE:
            power = coordinate if index_text is None else f"({coordinate})"
            return f"2^{power}-1"
        raise ValueError("unsupported symbolic term family")


def initialize_projected(
    term: ProjectedNumberTerm,
    family: FamilyId,
    index: int,
    parameter: int | None,
    source_radix: int | None,
    symbolic: str | SymbolicExpression,
    payload: TermPayload,
    metrics: ProjectionMetrics,
) -> None:
    descriptor = (
        SymbolicExpression(literal=symbolic) if isinstance(symbolic, str) else symbolic
    )
    names = (
        "family",
        "index",
        "parameter",
        "source_radix",
        "_symbolic",
        "payload",
        "metrics",
    )
    values = (family, index, parameter, source_radix, descriptor, payload, metrics)
    for name, value in zip(names, values, strict=True):
        object.__setattr__(term, name, value)

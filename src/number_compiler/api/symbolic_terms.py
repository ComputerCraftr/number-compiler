"""Demanded symbolic term text, separate from exact integer projection metadata."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.fields.symbolic_extent import integer_text

if TYPE_CHECKING:
    from number_compiler.api.number_api import (
        NumberFamily,
        ProjectedNumberTerm,
        ProjectionMetrics,
        TermPayload,
    )


@dataclass(frozen=True, slots=True)
class SymbolicExpression:
    family: str = ""
    index: int = 0
    parameter: int | None = None
    radix: int | None = None
    literal: str | None = None

    def render(self, index_text: str | None = None) -> str:
        if self.literal is not None:
            return self.literal
        coordinate = integer_text(self.index) if index_text is None else index_text
        if self.family == "a367620":
            return f"A367620[{coordinate}]"
        if self.family == "reverse-add":
            return f"reverse_add(seed={self.parameter},base={self.radix})[{coordinate}]"
        if self.family == "collatz":
            return f"collatz(seed={self.parameter})[{coordinate}]"
        if self.family == "antihydra":
            return f"antihydra_arithmetic(source=blank)[{coordinate}]"
        if self.family == "prime":
            return f"prime_at_or_after(start={self.parameter})[{coordinate}]"
        if self.family == "fermat":
            power = coordinate if index_text is None else f"({coordinate})"
            return f"2^(2^{power})+1"
        if self.family == "mersenne":
            power = coordinate if index_text is None else f"({coordinate})"
            return f"2^{power}-1"
        raise ValueError("unsupported symbolic term family")


def initialize_projected(
    term: ProjectedNumberTerm,
    family: NumberFamily,
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


def render_symbolic(term: ProjectedNumberTerm, index_text: str) -> str:
    return term._symbolic.render(index_text)

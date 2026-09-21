"""Research-only reverse/add threshold state and random-access projections.

This bounded reference is not an installed source-image observer or a
production cylinder constructor.

The pair coefficient ``S_i`` always lies in ``[0, 2(b-1)]``.  Relative to the
carry threshold ``b-1`` its exact defect

    delta_i = S_i - (b-1)

therefore lives in a fixed alphabet of ``2b-1`` states, independent of digit
width.  The sign of ``delta`` is the LT/EQ/GT carry domain; the magnitude is the
small threshold-distance phase needed to evolve that domain exactly.

This module replaces the old fixed-height carry slab as the canonical spatial
196/reverse-add observer.  It never materializes a carry row: every boundary is
queried through the shared logarithmic prefix monoid.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.carry.prefix_monoid import FormulaPrefixMonoidProjection
from number_compiler.arithmetic.formula.formula import FormulaArena, FormulaRoot
from number_compiler.arithmetic.formula.pair_algebra import (
    carry_boundary_at,
    carry_prefix_projection,
)
from number_compiler.arithmetic.formula.skew_residue_laws import (
    pair_growth_edge,
    pair_growth_interior,
    pair_no_growth,
)
from number_compiler.arithmetic.formula.summary import (
    get_summary,
    synthesize_symmetric_summary,
)
from number_compiler.arithmetic.formula.types import RadixSpec


@dataclass(frozen=True, slots=True)
class ReverseAddDomainSymbol:
    """One exact finite threshold-distance symbol."""

    base: int
    defect: int

    def __post_init__(self) -> None:
        b, d = int(self.base), int(self.defect)
        if b < 2 or not -(b - 1) <= d <= b - 1:
            raise ValueError((b, d))
        object.__setattr__(self, "base", b)
        object.__setattr__(self, "defect", d)

    @property
    def relation(self) -> int:
        return -1 if self.defect < 0 else 1 if self.defect > 0 else 0

    @property
    def carry_domain(self) -> str:
        return "LT" if self.defect < 0 else "GT" if self.defect > 0 else "EQ"

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("reverse-add-domain", self.base, self.defect)

    @property
    def description_bits(self) -> int:
        return (
            max(1, self.base.bit_length())
            + max(1, (abs(self.defect) + 1).bit_length())
            + 1
        )


@dataclass(frozen=True, slots=True)
class ReverseAddSpatialIndex:
    """Random-access domain/carry/digit observer for one symmetric pair field."""

    arena: FormulaArena
    pair: FormulaRoot
    spec: RadixSpec
    prefix: FormulaPrefixMonoidProjection
    growth: int

    @classmethod
    def build(
        cls,
        arena: FormulaArena,
        pair: FormulaRoot,
        spec: RadixSpec,
    ) -> ReverseAddSpatialIndex:
        if pair.plane_count != spec.plane_count:
            raise ValueError((pair.plane_count, spec.plane_count))
        summary = get_summary(arena, pair, spec)
        if summary is None:
            summary = synthesize_symmetric_summary(arena, pair, spec)
        return cls(
            arena,
            pair,
            spec,
            carry_prefix_projection(arena, pair.planes, spec),
            summary.growth_from_outer_symmetry,
        )

    @property
    def source_width(self) -> int:
        return self.pair.width

    @property
    def target_width(self) -> int:
        return self.source_width + self.growth

    @property
    def prefix_stages(self) -> int:
        return int(self.prefix.stages)

    def source_value_at(self, position: int) -> int:
        p = int(position)
        if not 0 <= p < self.source_width:
            raise IndexError(p)
        return sum(
            self.arena.eval_closed_bit(plane, p) << bit
            for bit, plane in enumerate(self.pair.planes)
        )

    def source_symbol_at(self, position: int) -> ReverseAddDomainSymbol:
        return ReverseAddDomainSymbol(
            self.spec.base,
            self.source_value_at(position) - self.spec.threshold,
        )

    def carry_boundary(self, boundary: int) -> int:
        return carry_boundary_at(self.arena, self.prefix, int(boundary), incoming=0)

    def next_digit_at(self, position: int) -> int:
        """Project one digit of ``x+reverse(x)`` without a carry vector."""
        p = int(position)
        d = self.source_width
        if not 0 <= p < self.target_width:
            raise IndexError(p)
        if p == d:
            if not self.growth:
                raise IndexError(p)
            return 1
        return (self.source_value_at(p) + self.carry_boundary(p)) % self.spec.base

    def next_value_at(self, position: int) -> int:
        """Project one coefficient of the next symmetric pair field exactly."""
        p = int(position)
        d, b = self.source_width, self.spec.base
        if not 0 <= p < self.target_width:
            raise IndexError(p)
        C = self.carry_boundary
        if not self.growth:
            s = self.source_value_at(p)
            value = pair_no_growth(s, C(p), C(p + 1), C(d - p - 1), C(d - p), b)
        elif p == 0 or p == d:
            s0 = self.source_value_at(0)
            value = pair_growth_edge(s0, C(1), b)
        else:
            value = pair_growth_interior(
                self.source_value_at(p),
                self.source_value_at(p - 1),
                C(p),
                C(p + 1),
                C(d - p),
                C(d - p + 1),
                b,
            )
        if not 0 <= value <= 2 * (b - 1):
            raise AssertionError((p, value, b))
        return int(value)

    def next_symbol_at(self, position: int) -> ReverseAddDomainSymbol:
        return ReverseAddDomainSymbol(
            self.spec.base,
            self.next_value_at(position) - self.spec.threshold,
        )


__all__ = ["ReverseAddDomainSymbol", "ReverseAddSpatialIndex"]

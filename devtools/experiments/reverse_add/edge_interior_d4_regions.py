"""Research-only symbolic C2 -> C4 regions for the edge/interior chamber.

The constructor extends :mod:`edge_interior_regions` by deriving Q2 and Q3
from closed affine inequalities.  Widths 3, 4 and 5 are separate overlap
cases; widths at least 6 use bounded seam/interior regions.  Each carry field
is one formal finite union of intervals, never a coefficient word.

The returned arrows remain source-labelled research algebra.  They have no
authenticated source admission, complete output-channel effect, schema
canonicality, or pump certificate.
"""

from __future__ import annotations

from dataclasses import dataclass

from devtools.experiments.reverse_add.edge_interior_regions import (
    EdgeInteriorD2Clause,
    construct_edge_interior_d2,
)
from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.fields.symbolic_innovation import (
    InnovationID,
    RadialMultiplier,
    SymbolicInnovationArena,
    SymbolicRadialInnovation,
)


@dataclass(frozen=True, slots=True)
class FiniteInterval:
    start: int
    stop: int

    def __post_init__(self) -> None:
        if type(self.start) is not int or type(self.stop) is not int:
            raise TypeError("carry-region endpoints must be exact integers")
        if not 0 <= self.start < self.stop:
            raise ValueError("carry-region interval must be nonempty and ordered")


@dataclass(frozen=True, slots=True)
class FiniteCarryRegion:
    """A bounded union of disjoint half-open intervals in one clause extent."""

    extent: int
    intervals: tuple[FiniteInterval, ...]

    def __post_init__(self) -> None:
        if type(self.extent) is not int or self.extent < 1:
            raise ValueError("carry region requires a positive extent")
        if type(self.intervals) is not tuple:
            raise TypeError("carry regions require immutable interval tuples")
        if len(self.intervals) > 3:
            raise ValueError("this D4 source region has at most three intervals")
        previous = 0
        for index, interval in enumerate(self.intervals):
            if type(interval) is not FiniteInterval:
                raise TypeError("carry region requires typed finite intervals")
            interval.__post_init__()
            if interval.stop > self.extent or index and interval.start <= previous:
                raise ValueError(
                    "carry-region intervals touch, overlap or leave the extent"
                )
            previous = interval.stop

    def contains(self, index: int) -> bool:
        if type(index) is not int:
            raise TypeError("carry-region coordinates must be exact integers")
        return any(
            interval.start <= index < interval.stop for interval in self.intervals
        )


@dataclass(frozen=True, slots=True)
class EdgeInteriorD4Clause:
    d2: EdgeInteriorD2Clause
    q2_region: FiniteCarryRegion
    q3_region: FiniteCarryRegion
    q2_semantic: SemanticIdentity
    q3_semantic: SemanticIdentity
    growth2: int
    growth3: int
    e2: InnovationID
    beta2: InnovationID
    output2: SymbolicRadialInnovation
    pair3: SymbolicRadialInnovation
    e3: InnovationID
    beta3: InnovationID
    output3: SymbolicRadialInnovation
    pair4: SymbolicRadialInnovation
    q2_case: str
    q3_case: str

    @property
    def production_admitted(self) -> bool:
        return False

    def require_production_admission(self) -> None:
        raise ValueError(
            "research parameter regions are not authenticated production admission"
        )


def _region(extent: int, *intervals: tuple[int, int]) -> FiniteCarryRegion:
    return FiniteCarryRegion(
        extent, tuple(FiniteInterval(start, stop) for start, stop in intervals)
    )


def _q2_region(extent: int, edge: int, interior: int) -> tuple[FiniteCarryRegion, str]:
    """Classify Q2 from the closed P2 coefficient formulas.

    P2 has width ``m+1`` and edge ``2*a-8 < 10``.  For ``m=3`` its two
    interior coefficients are ``2*a+4*b-37``.  For ``m>=4`` the shoulders
    and bulk separate; the only non-full high chamber is ``m=4,b=8,a>=7``,
    where the two high shoulders are separated by a low center.
    """
    width = extent + 1
    if extent == 3:
        # P2 interior is 2a+4b-37; its two positions are GT exactly here.
        if 2 * edge + 4 * interior - 37 >= 10:
            return _region(width, (1, 3)), "m3-interior-gt"
        return _region(width), "m3-interior-lt-eq"
    if extent == 4:
        if interior == 9:
            return _region(width, (1, 4)), "m4-b9-core"
        if edge >= 7:
            return _region(width, (1, 2), (3, 4)), "m4-b8-split"
        return _region(width), "m4-b8-low"
    if extent == 5:
        if interior == 9 or edge >= 7:
            return _region(width, (1, 5)), "m5-high-core"
        return _region(width), "m5-b8-low"
    if interior == 9 or edge >= 7:
        return _region(width, (1, extent)), "wide-high-core"
    return _region(width, (3, extent - 1)), "wide-b8-inner-core"


def _q3_region(
    extent: int, edge: int, interior: int
) -> tuple[FiniteCarryRegion, int, str]:
    """Classify Q3 using affine P3 seams, with overlap widths split first.

    On the full-Q2 branch the stable coefficients are edge ``4*a-15``,
    shoulder ``4*a+8*b-91``, next seam ``16*b-128``, and bulk
    ``16*b-126``.  The ``m=3`` interior is instead ``4*a+8*b-93``.  On the
    center-Q2 branch ``b=8,a<=6,m>=6``, the boundary pattern is
    ``edge, GT, 9, low..., 9, GT, edge``; carry propagation therefore gives
    two fixed boundary intervals.  These formulas imply terminal growth
    exactly when ``a>=7``.
    """
    width = extent + 1
    if extent == 3:
        high2 = 2 * edge + 4 * interior - 37 >= 10
        if not high2:
            if edge >= 7:
                return _region(width, (0, width)), 1, "m3-low2-all"
            return _region(width, (1, 3)), 0, "m3-low2-center"
        if (edge, interior) == (6, 9):
            return _region(width), 0, "m3-high2-empty"
        if (edge, interior) == (8, 9):
            return _region(width, (0, width)), 1, "m3-high2-all"
        return _region(width, (0, 1), (3, 4)), 1, "m3-high2-edges"
    if extent == 4:
        if interior == 8 and edge <= 6:
            return _region(width, (1, 4)), 0, "m4-b8-low-interior"
        if interior == 8:
            return _region(width, (0, 1), (2, 3), (4, 5)), 1, "m4-b8-alternating"
        if edge <= 6:
            return _region(width, (2, 3)), 0, "m4-b9-center"
        return _region(width, (0, width)), 1, "m4-b9-all"
    if extent == 5:
        if interior == 8 and edge <= 6:
            return _region(width, (1, 5)), 0, "m5-b8-low-interior"
        if interior == 8:
            return _region(width, (0, 1), (5, 6)), 1, "m5-b8-edges"
        if edge <= 6:
            return _region(width, (2, 4)), 0, "m5-b9-center"
        return _region(width, (0, width)), 1, "m5-b9-all"
    if interior == 8 and edge <= 6:
        return _region(width, (1, 3), (extent - 1, extent)), 0, "wide-b8-seams"
    if interior == 8:
        return _region(width, (0, 1), (extent, width)), 1, "wide-b8-edges"
    if edge <= 6:
        return _region(width, (2, extent - 1)), 0, "wide-b9-core"
    return _region(width, (0, width)), 1, "wide-b9-all"


def _semantic(
    source_label: int, layer: int, region: FiniteCarryRegion, case: str
) -> SemanticIdentity:
    return SemanticIdentity(
        "edge-interior-d4-region-v1",
        (
            "edge-interior-d4-region-v1",
            source_label,
            layer,
            region.extent,
            tuple((item.start, item.stop) for item in region.intervals),
            case,
        ),
    )


def _correction(arena: SymbolicInnovationArena, q: InnovationID) -> InnovationID:
    return arena.linear_combination(
        ((1, arena.chart(q, CylinderChart(1, -1))), (-10, q))
    )


def _beta(
    arena: SymbolicInnovationArena,
    correction: InnovationID,
    reflection: int,
) -> InnovationID:
    return arena.add(
        correction,
        arena.chart(correction, CylinderChart(-1, reflection)),
    )


def construct_edge_interior_d4(
    arena: SymbolicInnovationArena,
    *,
    source_label: int,
    extent: int,
    edge: int,
    interior_digit: int,
) -> EdgeInteriorD4Clause:
    """Construct formal C2 -> C4 arrows from analytic carry-region cases."""
    d2 = construct_edge_interior_d2(
        arena,
        source_label=source_label,
        extent=extent,
        edge=edge,
        interior_digit=interior_digit,
    )
    q2_region, q2_case = _q2_region(extent, edge, interior_digit)
    q3_region, growth3, q3_case = _q3_region(extent, edge, interior_digit)
    q2_semantic = _semantic(source_label, 2, q2_region, q2_case)
    q3_semantic = _semantic(source_label, 3, q3_region, q3_case)
    q2 = arena.atom(q2_semantic)
    q3 = arena.atom(q3_semantic)

    e2 = _correction(arena, q2)
    beta2 = _beta(arena, e2, extent)
    b3 = arena.add(arena.radial(d2.action.innovation, RadialMultiplier(1, 0)), beta2)
    pair3 = arena.action(RadialMultiplier(2, 1), b3)
    output2 = arena.action(d2.action.multiplier, arena.add(d2.action.innovation, e2))

    e3 = _correction(arena, q3)
    beta3 = _beta(arena, e3, extent + growth3)
    step3 = RadialMultiplier(1, 0) if growth3 == 0 else RadialMultiplier(0, 1)
    b4 = arena.add(arena.radial(b3, step3), beta3)
    pair4 = arena.action(pair3.multiplier.then(step3), b4)
    output3 = arena.action(pair3.multiplier, arena.add(b3, e3))
    return EdgeInteriorD4Clause(
        d2,
        q2_region,
        q3_region,
        q2_semantic,
        q3_semantic,
        0,
        growth3,
        e2,
        beta2,
        output2,
        pair3,
        e3,
        beta3,
        output3,
        pair4,
        q2_case,
        q3_case,
    )


__all__ = [
    "EdgeInteriorD4Clause",
    "FiniteCarryRegion",
    "FiniteInterval",
    "construct_edge_interior_d4",
]

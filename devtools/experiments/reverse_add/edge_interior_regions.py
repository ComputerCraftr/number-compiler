"""Symbolic D2 carry regions for the decimal edge/interior source chamber.

This research kernel admits the parameter region

``S = edge(a) + interior(2*b) + edge(a)``

with ``m>=3``, ``5<=a<=8`` and ``8<=b<=9``.  It separates formal source
occurrences by an unauthenticated ``source_label`` and represents carry support
by two interval atoms:

``Q0 = 1_[1,m-1)`` and ``Q1 = 1_[0,m)``.

The second region follows from parameter inequalities, without evaluating the
future field: after the first primitive successor, all coefficients exceed 9.
The resulting two-step affine arrow is

``M2 = 2*(1+z)``

``B2 = (1+z)*beta0 - 9*(1+z)*Q1``.

The directional second output is retained separately as
``D1 = 2*S + beta0 + E1`` with ``E1=(z-10)Q1``.  This is still only the
arithmetic output polynomial, not a complete thirteen-channel effect.

``source_label`` is only a formal binder separating research expressions.  It
is not authenticated source admission and this module cannot publish a
production clause.  The construction establishes one algebraic
source-parameter kernel, not a D4 constructor, canonical schema match, or
temporal pump.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.fields.radial_innovation import (
    InnovationID,
    RadialMultiplier,
    SymbolicRadialInnovation,
)
from number_compiler.arithmetic.fields.symbolic_innovation import (
    SymbolicInnovationArena,
)


@dataclass(frozen=True, slots=True)
class EdgeInteriorPredicate:
    minimum_extent: int = 3
    edge_low: int = 5
    edge_high: int = 8
    interior_low: int = 8
    interior_high: int = 9

    def admits(self, *, extent: int, edge: int, interior_digit: int) -> bool:
        return (
            type(extent) is int
            and type(edge) is int
            and type(interior_digit) is int
            and extent >= self.minimum_extent
            and self.edge_low <= edge <= self.edge_high
            and self.interior_low <= interior_digit <= self.interior_high
        )


@dataclass(frozen=True, slots=True)
class IntervalCarryRegion:
    """A parameter interval ``[start, extent + stop_offset)``."""

    start: int
    stop_offset: int

    def contains(self, index: int, extent: int) -> bool:
        if type(index) is not int or type(extent) is not int:
            raise TypeError("carry-region coordinates must be exact integers")
        return self.start <= index < extent + self.stop_offset


@dataclass(frozen=True, slots=True)
class SuccessorThresholdCertificate:
    """Lower bounds proving that the complete second carry region is GT."""

    edge_minimum: int
    width_three_center_minimum: int
    shoulder_minimum: int
    bulk_minimum: int

    def validate(self, predicate: EdgeInteriorPredicate) -> None:
        if type(predicate) is not EdgeInteriorPredicate:
            raise TypeError("threshold certificate requires the fixed chamber")
        if any(
            type(value) is not int
            for value in (
                predicate.minimum_extent,
                predicate.edge_low,
                predicate.edge_high,
                predicate.interior_low,
                predicate.interior_high,
            )
        ):
            raise TypeError("chamber parameters must be exact integers")
        if predicate != EdgeInteriorPredicate():
            raise ValueError("threshold certificate requires the fixed chamber")
        if any(
            type(value) is not int
            for value in (
                self.edge_minimum,
                self.width_three_center_minimum,
                self.shoulder_minimum,
                self.bulk_minimum,
            )
        ):
            raise TypeError("threshold bounds must be exact integers")
        expected = (
            2 * predicate.edge_low + 1,
            4 * predicate.interior_low - 20,
            4 * predicate.interior_low - 19,
            4 * predicate.interior_low - 18,
        )
        if (
            self.edge_minimum,
            self.width_three_center_minimum,
            self.shoulder_minimum,
            self.bulk_minimum,
        ) != expected:
            raise ValueError("threshold bounds were not derived from the chamber")
        if (
            min(
                self.edge_minimum,
                self.width_three_center_minimum,
                self.shoulder_minimum,
                self.bulk_minimum,
            )
            <= 9
        ):
            raise ValueError("successor threshold certificate does not imply GT")


@dataclass(frozen=True, slots=True)
class EdgeInteriorD2Clause:
    """One formal source-parameter affine arrow through two primitive steps."""

    source_label: int
    extent: int
    edge: int
    interior_digit: int
    predicate: EdgeInteriorPredicate
    q0_region: IntervalCarryRegion
    q1_region: IntervalCarryRegion
    q0_semantic: SemanticIdentity
    q1_semantic: SemanticIdentity
    beta0: InnovationID
    e1: InnovationID
    beta1: InnovationID
    output_action: SymbolicRadialInnovation
    action: SymbolicRadialInnovation
    threshold: SuccessorThresholdCertificate

    @property
    def production_admitted(self) -> bool:
        return False

    def require_production_admission(self) -> None:
        raise ValueError(
            "research source labels are not authenticated production admission"
        )


def _region_semantic(
    source_label: int,
    extent: int,
    region: IntervalCarryRegion,
    layer: int,
) -> SemanticIdentity:
    return SemanticIdentity(
        "edge-interior-carry-region-v1",
        (
            "edge-interior-carry-region-v1",
            source_label,
            extent,
            layer,
            region.start,
            region.stop_offset,
        ),
    )


def construct_edge_interior_d2(
    arena: SymbolicInnovationArena,
    *,
    source_label: int,
    extent: int,
    edge: int,
    interior_digit: int,
) -> EdgeInteriorD2Clause:
    """Construct the chamber's exact D2 affine expression without point cases."""
    if type(arena) is not SymbolicInnovationArena:
        raise TypeError("edge/interior research requires a symbolic arena")
    if type(source_label) is not int or source_label < 0:
        raise ValueError("formal source label must be a nonnegative integer")
    predicate = EdgeInteriorPredicate()
    if not predicate.admits(extent=extent, edge=edge, interior_digit=interior_digit):
        raise ValueError("parameters leave the edge/interior D2 chamber")

    threshold = SuccessorThresholdCertificate(
        edge_minimum=2 * predicate.edge_low + 1,
        width_three_center_minimum=4 * predicate.interior_low - 20,
        shoulder_minimum=4 * predicate.interior_low - 19,
        bulk_minimum=4 * predicate.interior_low - 18,
    )
    threshold.validate(predicate)

    q0_region = IntervalCarryRegion(1, -1)
    q1_region = IntervalCarryRegion(0, 0)
    q0_semantic = _region_semantic(source_label, extent, q0_region, 0)
    q1_semantic = _region_semantic(source_label, extent, q1_region, 1)
    q0 = arena.atom(q0_semantic)
    q1 = arena.atom(q1_semantic)

    shifted_q0 = arena.chart(q0, CylinderChart(1, -1))
    e0 = arena.linear_combination(((1, shifted_q0), (-10, q0)))
    beta0 = arena.add(e0, arena.chart(e0, CylinderChart(-1, extent - 1)))

    hasse = RadialMultiplier(0, 1)
    e1 = arena.linear_combination(
        ((1, arena.chart(q1, CylinderChart(1, -1))), (-10, q1))
    )
    beta1 = arena.linear_combination(((-9, arena.radial(q1, hasse)),))
    output_action = arena.action(RadialMultiplier(1, 0), arena.add(beta0, e1))
    b2 = arena.add(arena.radial(beta0, hasse), beta1)
    action = arena.action(RadialMultiplier(1, 1), b2)
    return EdgeInteriorD2Clause(
        source_label,
        extent,
        edge,
        interior_digit,
        predicate,
        q0_region,
        q1_region,
        q0_semantic,
        q1_semantic,
        beta0,
        e1,
        beta1,
        output_action,
        action,
        threshold,
    )


__all__ = [
    "EdgeInteriorD2Clause",
    "EdgeInteriorPredicate",
    "IntervalCarryRegion",
    "SuccessorThresholdCertificate",
    "construct_edge_interior_d2",
]

"""Joint source-issued outer mod-99/100 and inner negacyclic phase constraints.

This is a *relation*, not a hypothetical uniform period of the middle digits.
For X_t=3**(2**t), t>=1, the physical exponent is at least two and
3**m (mod 9900) has a 20-step cyclotomic orbit. Sampling m=2**t gives a
four-level cycle starting at t=2. Neither period is a Fermat prime test.

For binary positions j>=2, 2**(j+60) == 2**j (mod 9900); the first two
positions are exceptional because 2 is not a unit modulo 100. Combining
this *spatial* period with 2**(2w)==1 (mod 2**w+1) yields phase length
P=lcm(60,2w), sufficient to project BOTH the global cyclotomic residue and
the complete signed Fermat fold from one phase histogram.

An unknown middle retains an exact integer congruence and bounded phase
capacities. No unobserved carry or count is assigned and no modular square
is used. The source-to-prime gate remains fail-closed for open fibers.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from math import gcd, lcm
from typing import TYPE_CHECKING

from number_compiler.sequences.power_numbers._harmonic_authority import (
    harmonic_verified,
    issue_harmonic,
    new_harmonic_issuer,
)

if TYPE_CHECKING:
    from number_compiler.sequences.power_numbers.three_power_signed_border_action import (
        SourceWeightedTriplingAction,
    )
    from number_compiler.sequences.power_numbers.three_power_two_sided_cylinder import (
        FermatTwoSidedSourceCylinder,
    )

OUTER_MODULUS = 9_900
OUTER_PHYSICAL_PERIOD = 20
OUTER_BINARY_WEIGHT_PERIOD = 60


@dataclass(frozen=True, slots=True)
class FermatOuterCyclotomicClock:
    """Exact ordinary-tripling orbit with a separate dyadic-level cursor."""

    level: int
    physical_offset: int
    physical_phase: int
    residue99: int
    residue100: int

    @classmethod
    def from_level(
        cls, level: int, physical_offset: int = 0
    ) -> FermatOuterCyclotomicClock:
        if (
            type(level) is not int
            or not 1 <= level <= 65535
            or type(physical_offset) is not int
            or physical_offset < 0
        ):
            raise ValueError("invalid Fermat source cyclotomic clock")
        phase = (pow(2, level, 20) + physical_offset) % 20
        # Exponent may have reduced to 0/1, but the physical exponent is
        # always >=2, so choose a representative >=2.
        residue = pow(3, 2 + (phase - 2) % 20, OUTER_MODULUS)
        obj = cls(level, physical_offset, phase, residue % 99, residue % 100)
        obj.verify()
        return obj

    @property
    def residue198(self) -> int:
        """Odd lift of mod99; not an independent Fermat-source clock."""
        return self.residue99 + (99 if self.residue99 % 2 == 0 else 0)

    @property
    def residue9900(self) -> int:
        # CRT: 100 == 1 (mod 99); both values are canonical.
        return (
            self.residue100 + 100 * ((self.residue99 - self.residue100) % 99)
        ) % OUTER_MODULUS

    def verify(self) -> None:
        if (
            type(self.level) is not int
            or not 1 <= self.level <= 65535
            or type(self.physical_offset) is not int
            or self.physical_offset < 0
            or type(self.physical_phase) is not int
            or not 0 <= self.physical_phase < 20
            or type(self.residue99) is not int
            or type(self.residue100) is not int
        ):
            raise ValueError("invalid cyclotomic clock packet")
        p = (pow(2, self.level, 20) + self.physical_offset) % 20
        value = pow(3, 2 + (p - 2) % 20, OUTER_MODULUS)
        if self.physical_phase != p or (self.residue99, self.residue100) != (
            value % 99,
            value % 100,
        ):
            raise ArithmeticError("source cyclotomic clock is not closed")

    def advance(self, steps: int) -> FermatOuterCyclotomicClock:
        """Exact outer projection of `steps` ordinary tripling events.

        Does not claim that upper/inner guards repeat during this interval.
        """
        if type(steps) is not int or steps < 0:
            raise ValueError("negative/noninteger temporal advance")
        self.verify()
        return type(self).from_level(self.level, self.physical_offset + steps)

    def dyadic_successor(self) -> FermatOuterCyclotomicClock:
        """Exact low cyclotomic projection only, NOT an inner-period proof."""
        self.verify()
        if self.physical_offset != 0 or self.level == 65535:
            raise ValueError("dyadic source clock requires unshifted level")
        new = type(self).from_level(self.level + 1)
        if new.physical_phase != (self.physical_phase + pow(2, self.level, 20)) % 20:
            raise ArithmeticError("dyadic and physical cyclotomic clocks disagree")
        return new


@dataclass(frozen=True, slots=True)
class UnknownBinaryBlockCongruence:
    """A forced congruence for ONE unresolved interval, when it is unique."""

    start: int
    width: int
    residue: int
    modulus: int

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (self.start, self.width, self.residue, self.modulus)
        ):
            raise TypeError(
                "binary block congruence coordinates must be exact integers"
            )
        if (
            self.start < 0
            or self.width < 1
            or self.modulus < 1
            or not 0 <= self.residue < self.modulus
        ):
            raise ValueError("invalid binary block congruence domain")

    def admits(self, source_word: int) -> bool:
        return (
            type(source_word) is int
            and 0 <= source_word
            and source_word.bit_length() <= self.width
            and source_word % self.modulus == self.residue
        )


def _phase_capacity(start: int, end: int, period: int, phase: int) -> int:
    """Count j in [start,end), j>=2, (j-2)%period == phase."""
    first = max(start, 2)
    desired = 2 + phase
    pos = first + (desired - first) % period
    return 0 if pos >= end else 1 + (end - 1 - pos) // period


def _source_phase_counts(
    source: SourceWeightedTriplingAction, period: int
) -> tuple[
    tuple[int, ...],
    tuple[int, ...],
    tuple[int | None, int | None],
    int,
    tuple[tuple[int, int], ...],
]:
    """Known/unknown phase histograms with the nonunit head kept separate."""
    known = [0] * period
    capacities = [0] * period
    head: list[int | None] = [None, None]
    weighted_known_mod = 0
    gaps: list[tuple[int, int]] = []
    for block in source.blocks:
        start, end = block.start, block.start + block.width
        if block.source_value is None:
            gaps.append((start, block.width))
            for p in range(period):
                capacities[p] += _phase_capacity(start, end, period, p)
        else:
            weighted_known_mod = (
                weighted_known_mod + block.source_value * pow(2, start, OUTER_MODULUS)
            ) % OUTER_MODULUS
            bits = block.source_value
            while bits:
                lowest = bits & -bits
                j = start + lowest.bit_length() - 1
                if j >= 2:
                    known[(j - 2) % period] += 1
                bits ^= lowest
        for j in (0, 1):
            if start <= j < end and block.source_value is not None:
                head[j] = (block.source_value >> (j - start)) & 1
    return (
        tuple(known),
        tuple(capacities),
        (head[0], head[1]),
        weighted_known_mod,
        tuple(gaps),
    )


@dataclass(frozen=True, slots=True, weakref_slot=True)
class FermatOuterInnerPhaseConstraint:
    """The same signed phase counts observed by both outer cyclotomic clocks.

    Unknown-phase capacities are UPPER BOUNDS, never assertions that a count
    is achieved. The source-wide congruence couples their possible values.
    """

    clock: FermatOuterCyclotomicClock
    fold_width: int
    phase_period: int
    known_phase_counts: tuple[int, ...]
    unknown_phase_capacities: tuple[int, ...]
    known_head_bits: tuple[int | None, int | None]
    unknown_head_positions: tuple[int, ...]
    known_source_residue9900: int
    required_unknown_residue9900: int
    unknown_blocks: tuple[tuple[int, int], ...]
    forced_single_block: UnknownBinaryBlockCongruence | None
    source_owner: SourceWeightedTriplingAction = field(repr=False, compare=False)
    cylinder_owner: FermatTwoSidedSourceCylinder = field(repr=False, compare=False)
    _issuer: object = field(default=None, init=False, repr=False, compare=False)

    def structural_payload(self) -> tuple[object, ...]:
        return (
            self.clock,
            self.fold_width,
            self.phase_period,
            self.known_phase_counts,
            self.unknown_phase_capacities,
            self.known_head_bits,
            self.unknown_head_positions,
            self.known_source_residue9900,
            self.required_unknown_residue9900,
            self.unknown_blocks,
            self.forced_single_block,
            self.source_owner.issuer_payload(),
            self.cylinder_owner.structural_payload(),
        )

    @property
    def producer_verified(self) -> bool:
        return (
            self.source_owner.producer_verified
            and self.cylinder_owner.producer_verified
            and self.cylinder_owner.source is self.source_owner
            and harmonic_verified(
                self, self.structural_payload(), issuer=_OUTER_INNER_ISSUER
            )
        )

    @property
    def all_signed_phase_counts_forced(self) -> bool:
        if not self.producer_verified:
            raise ValueError("unissued outer/inner phase constraint")
        return not self.unknown_blocks

    @property
    def unknown_count_equation(self) -> tuple[tuple[int, ...], int, int]:
        """Sum coefficients*unknown_count ≡ target (mod 9900).

        Possible unknown bits at absolute j=0/1 must be separately included;
        in the production source low two bits are always authenticated.
        """
        if not self.producer_verified:
            raise ValueError("unissued outer/inner phase constraint")
        weights = tuple(pow(2, 2 + p, OUTER_MODULUS) for p in range(self.phase_period))
        return weights, self.required_unknown_residue9900, OUTER_MODULUS

    def project_known_fold(self) -> int:
        if not self.producer_verified:
            raise ValueError("unissued outer/inner phase constraint")
        modulus = (1 << self.fold_width) + 1
        return (
            sum((b or 0) << j for j, b in enumerate(self.known_head_bits))
            + sum(
                n * pow(2, (2 + p) % (2 * self.fold_width), modulus)
                for p, n in enumerate(self.known_phase_counts)
            )
        ) % modulus

    def project_known_outer(self) -> int:
        if not self.producer_verified:
            raise ValueError("unissued outer/inner phase constraint")
        return (
            sum((b or 0) << j for j, b in enumerate(self.known_head_bits))
            + sum(
                n * pow(2, 2 + p, OUTER_MODULUS)
                for p, n in enumerate(self.known_phase_counts)
            )
        ) % OUTER_MODULUS

    def verify_complete_fiber(self, integer: int) -> tuple[int, int]:
        """Small reference-only check of one *admitted candidate*.

        Passing does not prove that the candidate belongs to 3**(2**t).
        """
        if not self.producer_verified:
            raise ValueError("unissued outer/inner phase constraint")
        if type(integer) is not int or integer < 0:
            raise ValueError("invalid full source")
        known = self.source_owner
        if integer.bit_length() != known.origin.bilateral.binary.source_digits:
            raise ValueError("full source has wrong certified length")
        for b in known.blocks:
            if (
                b.source_value is not None
                and (integer >> b.start) & ((1 << b.width) - 1) != b.source_value
            ):
                raise ArithmeticError("source differs from certified island")
        if self.cylinder_owner.admitted_edges(integer) is None:
            raise ArithmeticError(
                "source violates the full issued CRT/high/carry cylinder"
            )
        if integer % OUTER_MODULUS != self.clock.residue9900:
            raise ArithmeticError("source violates cyclotomic clock")
        if self.forced_single_block is not None:
            gap = self.forced_single_block
            if not gap.admits((integer >> gap.start) & ((1 << gap.width) - 1)):
                raise ArithmeticError("source violates exact middle congruence")
        return integer % OUTER_MODULUS, integer % ((1 << self.fold_width) + 1)

    def physical_successor(
        self, steps: int = 1
    ) -> tuple[FermatOuterCyclotomicClock, tuple[int, int]]:
        """Source-authenticated OUTER action and symbolic signed multiplier.

        Does not certify intermediate high digits or assign unknown K lanes.
        The symbolic factor is (base=3, exponent=steps), not a modular power.
        """
        if not self.producer_verified:
            raise ValueError("unissued outer/inner phase constraint")
        return self.clock.advance(steps), (3, steps)


_OUTER_INNER_ISSUER = new_harmonic_issuer(FermatOuterInnerPhaseConstraint)


def demand_outer_inner_phase_constraint(
    source: SourceWeightedTriplingAction,
    cylinder: FermatTwoSidedSourceCylinder,
) -> FermatOuterInnerPhaseConstraint:
    """Cross-certify source's complete outer modulo-99/100 ring with its
    signed folded inner clock. This is an exact RELATION on open middle counts.
    """
    if not source.producer_verified or not cylinder.producer_verified:
        raise ValueError("source-owned outer/inner ring required")
    if cylinder.source is not source:
        raise ValueError(
            "outer and inner packets belong to different source occurrences"
        )
    clock = cylinder.outer_clock
    clock.verify()
    if clock.level != source.level or clock.physical_offset != 0:
        raise ArithmeticError("source and outer clock have different owners")
    period = lcm(2 * source.fold_width, OUTER_BINARY_WEIGHT_PERIOD)
    if period > 8192:
        raise ValueError("joint positional phase exceeds explicit cell budget")
    known, capacity, head, known_mod, gaps = _source_phase_counts(source, period)
    projected_mod = (
        sum((v or 0) << j for j, v in enumerate(head))
        + sum(n * pow(2, 2 + p, OUTER_MODULUS) for p, n in enumerate(known))
    ) % OUTER_MODULUS
    if projected_mod != known_mod:
        raise ArithmeticError("cyclotomic projection of known islands disagrees")
    required = (clock.residue9900 - known_mod) % OUTER_MODULUS
    head_unknown = tuple(j for j, bit in enumerate(head) if bit is None)
    # The actual 3**(2**level), level>=1, is 1 mod 4. In this
    # source-backed issuer the first two bits must already be authenticated.
    # Otherwise the phase equation would also need explicit head variables.
    if head != (1, 0) or head_unknown:
        raise ArithmeticError("outer/inner joint needs authenticated 01 low-bit head")
    forced = None
    if len(gaps) == 1:
        start, width = gaps[0]
        g = gcd(pow(2, start, OUTER_MODULUS), OUTER_MODULUS)
        if required % g:
            raise ArithmeticError("single interior interval contradicts outer clock")
        modulus = OUTER_MODULUS // g
        base = (pow(2, start, OUTER_MODULUS) // g) % modulus
        residue = (required // g * pow(base, -1, modulus)) % modulus
        forced = UnknownBinaryBlockCongruence(start, width, residue, modulus)
    result = FermatOuterInnerPhaseConstraint(
        clock,
        source.fold_width,
        period,
        known,
        capacity,
        head,
        head_unknown,
        known_mod,
        required,
        gaps,
        forced,
        source,
        cylinder,
    )
    issue_harmonic(result, result.structural_payload(), issuer=_OUTER_INNER_ISSUER)
    return result


__all__ = [
    "OUTER_BINARY_WEIGHT_PERIOD",
    "OUTER_MODULUS",
    "OUTER_PHYSICAL_PERIOD",
    "FermatOuterCyclotomicClock",
    "FermatOuterInnerPhaseConstraint",
    "UnknownBinaryBlockCongruence",
    "demand_outer_inner_phase_constraint",
]

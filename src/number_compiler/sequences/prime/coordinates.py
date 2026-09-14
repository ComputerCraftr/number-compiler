"""Alternative exact coordinate systems for the finite prime projector.

This module deliberately separates three questions that are easy to conflate:

* candidate translation (which *is* a tiny digit-pair/carry monoid),
* factor-set representation (which can be packed into one lcm-wheel modulus),
* first-hole/composite projection (which must still be charged explicitly).

Encoding-only experiments (power-radix decision DAGs, Zeckendorf/Fibonacci
coordinates, and period probes) live in :mod:`prime_encoding_analysis` so the
production prime projector cannot depend on measurement-only code.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd, isqrt

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.sequences.prime.set import (
    PrimeBlockSummary,
    canonical_multiplicative_lanes,
)
from number_compiler.sequences.prime.wheel import PackedWheelProgram


@dataclass(frozen=True, slots=True)
class PrimePairField:
    """Digit-pair addition ``origin + offset`` with an explicit 0/1 carry field.

    ``pair_sums[i]`` is the unnormalised coefficient ``x_i+y_i``.  The full
    integer is already ``sum(pair_sums[i]*base**i)``; the carry vector is only
    the radix-normalisation certificate.  Consequently modular divisibility can
    consume the pair field directly and does not need a second reconstructed
    digit state.
    """

    base: int
    origin: int
    offset: int
    pair_sums: tuple[int, ...]
    carries: tuple[int, ...]
    normalized_digits: tuple[int, ...]

    @property
    def value(self) -> int:
        return self.origin + self.offset

    def raw_value(self) -> int:
        return sum(s * (self.base**i) for i, s in enumerate(self.pair_sums))

    def normalized_value(self) -> int:
        return sum(d * (self.base**i) for i, d in enumerate(self.normalized_digits))

    def residue(self, modulus: int) -> int:
        modulus = int(modulus)
        if modulus <= 0:
            raise ValueError(modulus)
        # Consume the unnormalised pair coefficients directly.  Carry terms
        # telescope in the weighted radix sum and therefore are unnecessary.
        acc = 0
        weight = 1 % modulus
        for coefficient in self.pair_sums:
            acc = (acc + coefficient * weight) % modulus
            weight = (weight * self.base) % modulus
        return acc

    @property
    def carry_ones(self) -> int:
        return sum(self.carries)


def prime_pair_field(origin: int, offset: int, *, base: int = 10) -> PrimePairField:
    origin, offset, base = int(origin), int(offset), int(base)
    if origin < 0 or offset < 0 or base < 2:
        raise ValueError((origin, offset, base))
    x = digits_lsd(origin, base)
    y = digits_lsd(offset, base)
    width = max(len(x), len(y))
    x = digits_lsd(origin, base, width)
    y = digits_lsd(offset, base, width)
    pair = tuple(a + b for a, b in zip(x, y))
    carries = [0]
    digits: list[int] = []
    carry = 0
    for coefficient in pair:
        total = coefficient + carry
        digits.append(total % base)
        carry = total // base
        if carry not in (0, 1):
            raise AssertionError((base, coefficient, carry))
        carries.append(carry)
    if carry:
        digits.append(carry)
    result = PrimePairField(base, origin, offset, pair, tuple(carries), tuple(digits))
    if result.raw_value() != result.value or result.normalized_value() != result.value:
        raise AssertionError(result)
    return result


@dataclass(frozen=True, slots=True)
class LeastFactorLane:
    factor: int
    hits: int
    wins: int


@dataclass(frozen=True, slots=True)
class LeastFactorProjection:
    """Disjoint tropical/min envelope of the multiplicative witness lanes."""

    start: int
    length: int
    labels: tuple[int, ...]  # 0 means prime; otherwise the least active factor.
    summary: PrimeBlockSummary
    periodic_lanes: int
    active_lanes: tuple[LeastFactorLane, ...]

    @property
    def active_lane_count(self) -> int:
        return len(self.active_lanes)

    @property
    def removed_finite_lanes(self) -> int:
        return self.periodic_lanes - len(self.active_lanes)


def project_least_factor_field(start: int, length: int) -> LeastFactorProjection:
    """Canonicalize overlapping divisor sets by their pointwise minimum factor.

    A retained lane is active iff it wins at least one candidate.  Dropping all
    non-winning lanes preserves the composite set on this finite block exactly.
    """
    start, length = int(start), int(length)
    if start < 3 or start % 2 == 0 or length < 0:
        raise ValueError((start, length))
    if length == 0:
        return LeastFactorProjection(start, 0, (), PrimeBlockSummary.empty(), 0, ())
    _candidates, _natural, lanes = canonical_multiplicative_lanes(start, length)
    labels = [0] * length
    active: list[LeastFactorLane] = []
    for lane in lanes:
        wins = 0
        for j in range(lane.first_index, length, lane.factor):
            if labels[j] == 0:
                labels[j] = lane.factor
                wins += 1
        if wins:
            active.append(LeastFactorLane(lane.factor, lane.hits, wins))
    prime_count = sum(label == 0 for label in labels)
    first = next((j for j, label in enumerate(labels) if label == 0), None)
    return LeastFactorProjection(
        start,
        length,
        tuple(labels),
        PrimeBlockSummary(length, prime_count, first),
        len(lanes),
        tuple(active),
    )


@dataclass(frozen=True, slots=True)
class HyperbolicPackedPrimeSummary:
    start: int
    length: int
    summary: PrimeBlockSummary
    limit: int
    generator_events: int
    active_factor_count: int
    cofactor_points: int
    roughness_word_gcds: int
    first_hole_word_gcds: int
    packed_groups: int
    total_group_bits: int


def prime_block_summary_hyperbolic_packed(
    start: int,
    length: int,
    *,
    word_bits: int = 62,
) -> HyperbolicPackedPrimeSummary:
    """Exact disjoint hyperbolic projector with no candidate bitmap.

    Every odd composite in the block has a unique least prime factor ``q`` and
    cofactor ``r``.  While natural generators are scanned, newly discovered q's
    are tested against the already-built packed wheel for primes < q:

        q wins on q*r  <=>  gcd(r, product(p<q)) == 1.

    Summing wins therefore counts composites without overlap.  First-hole is
    obtained independently from the completed packed wheel.
    """
    start, length, word_bits = int(start), int(length), int(word_bits)
    if start < 3 or start % 2 == 0 or length < 0 or word_bits < 2:
        raise ValueError((start, length, word_bits))
    if length == 0:
        return HyperbolicPackedPrimeSummary(
            start, 0, PrimeBlockSummary.empty(), 1, 0, 0, 0, 0, 0, 0, 0
        )
    high = start + 2 * (length - 1)
    limit = isqrt(high)
    lcm_value = 1
    squarefree = 1
    groups: list[int] = []
    current = 1
    generator_events = 0
    active_factors = 0
    cofactor_points = 0
    roughness_gcds = 0
    composite_count = 0

    def prefix_groups() -> tuple[int, ...]:
        return tuple(groups) + (() if current == 1 else (current,))

    for k in range(2, limit + 1):
        new_lcm = (lcm_value // gcd(lcm_value, k)) * k
        if new_lcm == lcm_value:
            continue
        ratio = new_lcm // lcm_value
        fresh = ratio // gcd(squarefree, ratio)
        if fresh != 1:
            q = fresh
            generator_events += 1
            if q != 2:
                lo = max(q, (start + q - 1) // q)
                hi = high // q
                if lo % 2 == 0:
                    lo += 1
                wins = 0
                mods = prefix_groups()
                for r in range(lo, hi + 1, 2):
                    cofactor_points += 1
                    rough = True
                    for modulus in mods:
                        roughness_gcds += 1
                        if gcd(r, modulus) > 1:
                            rough = False
                            break
                    if rough:
                        wins += 1
                if wins:
                    active_factors += 1
                    composite_count += wins
            if fresh.bit_length() > word_bits:
                raise ValueError((fresh, word_bits))
            if current != 1 and (current * fresh).bit_length() > word_bits:
                groups.append(current)
                current = 1
            current *= fresh
            squarefree *= fresh
        lcm_value = new_lcm

    if current != 1:
        groups.append(current)
    final_program = PackedWheelProgram(
        limit, word_bits, tuple(groups), 0, generator_events
    )
    first = final_program.first_prime(start, length)
    prime_count = length - composite_count
    summary = PrimeBlockSummary(length, prime_count, first.first_index)
    return HyperbolicPackedPrimeSummary(
        start,
        length,
        summary,
        limit,
        generator_events,
        active_factors,
        cofactor_points,
        roughness_gcds,
        first.gcd_calls,
        len(groups),
        sum(modulus.bit_length() for modulus in groups),
    )


__all__ = [
    "HyperbolicPackedPrimeSummary",
    "LeastFactorLane",
    "LeastFactorProjection",
    "PrimePairField",
    "prime_block_summary_hyperbolic_packed",
    "prime_pair_field",
    "project_least_factor_field",
]

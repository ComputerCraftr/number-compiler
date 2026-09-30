"""Exact multiplicative-set composite operator and constant-size prime summaries.

The source-independent composite field is the Boolean multiplicative convolution
``U star_x U`` for ``U(n)=[n>=2]``.  Translation is a tiny additive monoid.  The
expensive operation is deliberately exposed as projection onto a finite interval;
we do not hide that work behind the summary algebra.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from math import gcd, isqrt


@dataclass(frozen=True, slots=True)
class AdditiveTranslation:
    """Canonical nonnegative additive shift in sparse binary form.

    ``2**1_000_000`` is represented by the exponent ``1_000_000`` rather than
    by a million-bit integer.  Equal powers carry immediately, so composition
    is canonical by numerical value without materializing the shift.
    """

    pow2_exponents: tuple[int, ...] = ()

    def __post_init__(self) -> None:
        exps = tuple(map(int, self.pow2_exponents))
        if any(e < 0 for e in exps):
            raise ValueError(exps)
        if exps != tuple(sorted(set(exps))):
            raise ValueError("pow2_exponents must be canonical and unique")

    @classmethod
    def from_int(cls, value: int) -> AdditiveTranslation:
        value = int(value)
        if value < 0:
            raise ValueError("symbolic translation is a nonnegative monoid")
        exps: list[int] = []
        bit = 0
        while value:
            if value & 1:
                exps.append(bit)
            value >>= 1
            bit += 1
        return cls(tuple(exps))

    @classmethod
    def power_of_two(cls, exponent: int) -> AdditiveTranslation:
        exponent = int(exponent)
        if exponent < 0:
            raise ValueError(exponent)
        return cls((exponent,))

    @staticmethod
    def _normalize_exponents(exponents: Iterable[int]) -> tuple[int, ...]:
        counts: dict[int, int] = {}
        for exponent in exponents:
            e = int(exponent)
            if e < 0:
                raise ValueError(e)
            counts[e] = counts.get(e, 0) + 1
        if not counts:
            return ()
        e = min(counts)
        top = max(counts)
        while e <= top:
            count = counts.get(e, 0)
            if count >= 2:
                counts[e] = count & 1
                counts[e + 1] = counts.get(e + 1, 0) + (count >> 1)
                top = max(top, e + 1)
            e += 1
        return tuple(k for k in sorted(counts) if counts[k] & 1)

    def then(self, other: AdditiveTranslation) -> AdditiveTranslation:
        return AdditiveTranslation(
            self._normalize_exponents(self.pow2_exponents + other.pow2_exponents)
        )

    def materialize(self) -> int:
        return sum(1 << e for e in self.pow2_exponents)

    def description_bits(self) -> int:
        return max(1, len(self.pow2_exponents).bit_length()) + sum(
            max(1, e.bit_length()) for e in self.pow2_exponents
        )


@dataclass(frozen=True, slots=True)
class MultiplicativeSetOperator:
    """Symbolic translated view ``d -> composite(origin + shift + d)``."""

    origin: int = 0
    shift: AdditiveTranslation = AdditiveTranslation()

    @classmethod
    def at(cls, origin: int) -> MultiplicativeSetOperator:
        return cls(int(origin), AdditiveTranslation())

    def translate(self, amount: int | AdditiveTranslation) -> MultiplicativeSetOperator:
        if not isinstance(amount, AdditiveTranslation):
            amount = AdditiveTranslation.from_int(int(amount))
        return MultiplicativeSetOperator(self.origin, self.shift.then(amount))

    def contains(self, offset: int) -> bool:
        return composite_convolution(
            self.origin + self.shift.materialize() + int(offset)
        )

    def first_hole(self, start: int, stop: int) -> int | None:
        start, stop = int(start), int(stop)
        if stop < start:
            raise ValueError((start, stop))
        for d in range(start, stop):
            if not self.contains(d):
                return d
        return None

    @property
    def operator_nodes(self) -> int:
        return 1

    @property
    def description_bits(self) -> int:
        return max(1, abs(self.origin).bit_length()) + 1 + self.shift.description_bits()


def is_prime_u64(value: int) -> bool:
    """Deterministic primality predicate for unsigned 64-bit integers.

    This is the canonical bounded predicate used when compiler algebra needs an
    auxiliary machine-word prime (for example a cyclotomic wheel field).  The
    fixed Miller--Rabin bases are deterministic for ``n < 2**64``; this does
    not replace :func:`smallest_factor`, which remains the factor-producing
    primitive for sequence semantics.
    """
    n = int(value)
    if n < 2 or n >= 1 << 64:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for prime in small:
        if n == prime:
            return True
        if n % prime == 0:
            return False
    d = n - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    # Jim Sinclair / deterministic 64-bit basis set.
    for base in (2, 325, 9375, 28178, 450775, 9780504, 1795265022):
        a = base % n
        if a == 0:
            continue
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True


def jacobi_symbol(a: int, n: int) -> int:
    """Return the exact Jacobi symbol ``(a/n)`` for positive odd ``n``.

    This Euclidean-style implementation is ring-safe: ``-1`` is a sound
    certificate that ``a`` is not a square modulo ``n``; ``+1`` is only a
    quadratic-residue certificate when ``n`` is known prime.
    """
    a, n = normalize_jacobi_inputs(a, n)
    a %= n
    result = 1
    while a:
        while not (a & 1):
            a >>= 1
            if n & 7 in (3, 5):
                result = -result
        a, n = n, a
        if (a & 3) == 3 and (n & 3) == 3:
            result = -result
        a %= n
    return result if n == 1 else 0


def smallest_factor(n: int, *, max_divisor: int | None = None) -> int | None:
    """Return the least proper factor of ``n`` or ``None`` when ``n`` is prime.

    With ``max_divisor``, None means no factor within that bound, not primality.
    This is the canonical bounded factor primitive shared by the prime and
    special-number compilers.  It does not retain a prime table.
    """
    n = int(n)
    if n < 2:
        return None
    if n == 2:
        return None
    if n % 2 == 0:
        return 2
    limit = isqrt(n)
    if max_divisor is not None:
        if type(max_divisor) is not int or max_divisor < 2:
            raise ValueError("trial divisor bound must be at least two")
        limit = min(limit, max_divisor)
    for factor in range(3, limit + 1, 2):
        if n % factor == 0:
            return factor
    return None


def composite_convolution(n: int) -> bool:
    """Exact ``(U star_x U)(n)`` without a stored prime sequence."""
    n = int(n)
    return n >= 4 and smallest_factor(n) is not None


@dataclass(frozen=True, slots=True)
class PrimeBlockSummary:
    """Complete observable for prime count + first-prime projection."""

    length: int
    count: int
    first: int | None

    def __post_init__(self) -> None:
        if self.length < 0 or not 0 <= self.count <= self.length:
            raise ValueError(self)
        if self.count == 0:
            if self.first is not None:
                raise ValueError(self)
        elif self.first is None or not 0 <= self.first < self.length:
            raise ValueError(self)

    @classmethod
    def empty(cls) -> PrimeBlockSummary:
        return cls(0, 0, None)

    @classmethod
    def bit(cls, is_prime: bool) -> PrimeBlockSummary:
        return cls(1, int(bool(is_prime)), 0 if is_prime else None)

    def then(self, other: PrimeBlockSummary) -> PrimeBlockSummary:
        first = self.first
        if first is None and other.first is not None:
            first = self.length + other.first
        return PrimeBlockSummary(
            self.length + other.length,
            self.count + other.count,
            first,
        )


@dataclass(frozen=True, slots=True)
class MultiplicativeLane:
    """One natural-factor divisibility lane over odd candidate indices.

    Candidates are ``start + 2*j``.  For odd ``factor`` the lane is the single
    congruence ``j == phase (mod factor)``.  Composite natural factors become
    redundant because a proper divisor lane contains them.
    """

    factor: int
    phase: int
    first_index: int
    hits: int


@dataclass(frozen=True, slots=True)
class PrimeProjection:
    start: int
    length: int
    composite_mask: int
    summary: PrimeBlockSummary
    factor_candidates: int
    natural_lanes: int
    canonical_lanes: tuple[MultiplicativeLane, ...]

    @property
    def prime_mask(self) -> int:
        return ((1 << self.length) - 1) ^ self.composite_mask


def _odd_factor_lane(start: int, length: int, factor: int) -> MultiplicativeLane | None:
    if factor <= 1 or factor % 2 == 0:
        return None
    # 2 is invertible modulo every odd factor.
    phase = ((-start) * pow(2, -1, factor)) % factor
    if phase >= length:
        return None
    hits = 1 + (length - 1 - phase) // factor
    return MultiplicativeLane(factor, phase, phase, hits)


def packed_generator_step(
    moduli: tuple[int, ...], value: int, *, word_bits: int = 62
) -> tuple[tuple[int, ...], bool, int]:
    """Classify/append one irreducible factor using the packed carrier itself.

    If ``moduli`` contain exactly the earlier prime generators, ``value`` is a
    new generator iff it is coprime to every packed group.  The returned call
    count meters bounded-word gcd projections.  No prime table is consulted.
    """
    value, word_bits = int(value), int(word_bits)
    groups = list(map(int, moduli))
    if (
        value < 2
        or word_bits < 2
        or any(m <= 1 or m.bit_length() > word_bits for m in groups)
    ):
        raise ValueError((value, word_bits, groups))
    calls = 0
    for modulus in groups:
        calls += 1
        if gcd(value, modulus) > 1:
            return tuple(groups), False, calls
    if value.bit_length() > word_bits:
        raise ValueError((value, word_bits))
    if groups and (groups[-1] * value).bit_length() <= word_bits:
        groups[-1] *= value
    else:
        groups.append(value)
    return tuple(groups), True, calls


@dataclass(frozen=True, slots=True)
class MultiplicativeLaneBasis:
    """Canonical irreducible divisor basis with explicit generator work."""

    factor_candidates: int
    natural_lanes: int
    lanes: tuple[MultiplicativeLane, ...]
    generator_gcd_calls: int
    generator_groups: int


def canonical_multiplicative_lane_basis(
    start: int, length: int, *, word_bits: int = 62
) -> MultiplicativeLaneBasis:
    """Discover irreducible odd-factor lanes with the self-modifying wheel.

    Every relevant odd factor is examined to report the unquotiented lane
    count.  Even factors are impossible divisors of the odd candidate block
    and are discarded structurally before the generator carrier.  Irreducible
    generators are *not* found by comparing every lane to
    all previously retained lanes: the bounded-word coprimality carrier decides
    whether each natural factor is a new prime generator.  This is the same
    canonical set morphism used by the packed prime compiler and avoids the
    previous quadratic-ish containment scan.
    """
    start, length, word_bits = int(start), int(length), int(word_bits)
    if start < 3 or start % 2 == 0 or length < 0 or word_bits < 2:
        raise ValueError((start, length, word_bits))
    if length == 0:
        return MultiplicativeLaneBasis(0, 0, (), 0, 0)
    high = start + 2 * (length - 1)
    limit = isqrt(high)
    # Only odd divisors can divide ``start + 2*j``.  The old generator loop
    # still fed every even integer through the packed coprimality carrier even
    # though `_odd_factor_lane` then discarded it.  Quotient that impossible
    # parity branch before any gcd work.
    factor_candidates = max(0, (limit - 1) // 2)
    natural_lanes = 0
    gcd_calls = 0
    groups: tuple[int, ...] = ()
    kept: list[MultiplicativeLane] = []
    for factor in range(3, limit + 1, 2):
        groups, is_generator, calls = packed_generator_step(
            groups, factor, word_bits=word_bits
        )
        gcd_calls += calls
        lane = _odd_factor_lane(start, length, factor)
        if lane is None:
            continue
        min_index = max(0, (factor * factor - start + 1) // 2)
        first = lane.phase
        if first < min_index:
            delta = min_index - first
            first += ((delta + factor - 1) // factor) * factor
        if first >= length:
            continue
        hits = 1 + (length - 1 - first) // factor
        natural_lanes += 1
        if is_generator:
            kept.append(MultiplicativeLane(factor, lane.phase, first, hits))
    return MultiplicativeLaneBasis(
        factor_candidates, natural_lanes, tuple(kept), gcd_calls, len(groups)
    )


def canonical_multiplicative_lanes(
    start: int, length: int
) -> tuple[int, int, tuple[MultiplicativeLane, ...]]:
    """Return the canonical quotient-first natural-factor basis."""
    basis = canonical_multiplicative_lane_basis(start, length)
    return basis.factor_candidates, basis.natural_lanes, basis.lanes


def finite_cover_lanes(start: int, length: int) -> tuple[MultiplicativeLane, ...]:
    """Return exactly the periodic divisor lanes that win in a finite block."""
    start, length = int(start), int(length)
    if length == 0:
        return ()
    _candidates, _natural, lanes = canonical_multiplicative_lanes(start, length)
    covered = [False] * length
    active: list[MultiplicativeLane] = []
    for lane in lanes:
        won = False
        for j in range(lane.first_index, length, lane.factor):
            if not covered[j]:
                covered[j] = True
                won = True
        if won:
            active.append(lane)
    return tuple(active)


def project_odd_prime_block(start: int, length: int) -> PrimeProjection:
    """Project ``U star_x U`` onto ``start + 2*j`` for ``j in [0,length)``.

    ``start`` must be odd and >= 3.  Every natural factor up to ``sqrt(high)``
    is considered.  Dominated multiplicative lanes are removed *before* the
    bitmap is built, so the retained basis is discovered by semantic
    containment rather than by supplying primes.
    """
    start, length = int(start), int(length)
    if start < 3 or start % 2 == 0 or length < 0:
        raise ValueError((start, length))
    if length == 0:
        return PrimeProjection(start, 0, 0, PrimeBlockSummary.empty(), 0, 0, ())
    factor_candidates, natural_lanes, lanes = canonical_multiplicative_lanes(
        start, length
    )
    composite_mask = 0
    for lane in lanes:
        for j in range(lane.first_index, length, lane.factor):
            composite_mask |= 1 << j

    full = (1 << length) - 1
    prime_mask = full ^ composite_mask
    count = prime_mask.bit_count()
    if count:
        first = (prime_mask & -prime_mask).bit_length() - 1
    else:
        first = None
    return PrimeProjection(
        start=start,
        length=length,
        composite_mask=composite_mask,
        summary=PrimeBlockSummary(length, count, first),
        factor_candidates=factor_candidates,
        natural_lanes=natural_lanes,
        canonical_lanes=lanes,
    )


def summarize_prime_bits(bits: Iterable[bool]) -> PrimeBlockSummary:
    result = PrimeBlockSummary.empty()
    for bit in bits:
        result = result.then(PrimeBlockSummary.bit(bool(bit)))
    return result


__all__ = [
    "AdditiveTranslation",
    "MultiplicativeLane",
    "MultiplicativeLaneBasis",
    "MultiplicativeSetOperator",
    "PrimeBlockSummary",
    "PrimeProjection",
    "canonical_multiplicative_lane_basis",
    "canonical_multiplicative_lanes",
    "composite_convolution",
    "finite_cover_lanes",
    "is_prime_u64",
    "jacobi_symbol",
    "packed_generator_step",
    "project_odd_prime_block",
    "smallest_factor",
    "summarize_prime_bits",
]


def normalize_jacobi_inputs(a: int, n: int) -> tuple[int, int]:
    a = int(a)
    n = int(n)
    if n <= 0 or not (n & 1):
        raise ValueError((a, n))
    return a, n

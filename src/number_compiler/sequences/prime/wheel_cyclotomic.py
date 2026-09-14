"""Cyclotomic-field automata for finite prime wheels.

A divisor lane over candidate indices is the cyclic language

    j == phase (mod q).

Instead of storing one additive residue per divisor, a group of prime periods
``q_i`` is embedded into one finite-field multiplicative group.  Choose a
machine-word prime ``P`` with ``M=prod(q_i) | P-1`` and an element ``a`` of
exact order ``M``.  The single field state ``x=a**j`` advances by
multiplication, while lane ``q`` is recognized by the root-of-unity projection

    x**(M/q) == a**(phase*M/q).

This is an exact cyclotomic automaton for the wheel action.  It does not claim
that every such representation beats packed congruence residues; construction
and classification work are charged explicitly and the compiler may retain the
packed automaton when it is cheaper.
"""

from __future__ import annotations

from bisect import bisect_left
from collections.abc import Sequence
from dataclasses import dataclass
from functools import lru_cache
from math import gcd, prod

from number_compiler.arithmetic.fields.morphism_core import binary_power, modular_power
from number_compiler.arithmetic.fields.radix import bit_width
from number_compiler.sequences.prime.set import MultiplicativeLane, is_prime_u64


@dataclass(frozen=True, slots=True)
class PrimeWheelCircularQuotient:
    """Exact quotient of a phase histogram by the uniform ``Phi_q`` direction.

    For prime ``q``, ``Phi_q(z)=1+z+...+z**(q-1)``.  A length-``q``
    histogram therefore has one algebraically redundant uniform direction.
    ``residue[i] = h[i]-h[q-1]`` stores the exact class modulo ``Phi_q``;
    retaining ``total=sum(h)`` recovers the discarded uniform coefficient
    uniquely.  This is an integer quotient, not a modular fingerprint.
    """

    prime: int
    total: int
    residue: tuple[int, ...]

    def __post_init__(self) -> None:
        q = int(self.prime)
        if q < 2 or len(self.residue) != q - 1 or int(self.total) < 0:
            raise ValueError(self)
        object.__setattr__(self, "prime", q)
        object.__setattr__(self, "total", int(self.total))
        object.__setattr__(self, "residue", tuple(map(int, self.residue)))
        # Prove the quotient can be lifted back to an integral histogram.
        numerator = self.total - sum(self.residue)
        if numerator % q:
            raise ValueError(("nonintegral-uniform-lift", self))
        baseline = numerator // q
        if baseline < 0 or any(baseline + value < 0 for value in self.residue):
            raise ValueError(("negative-histogram-lift", self))

    @classmethod
    def from_histogram(cls, histogram: Sequence[int]) -> PrimeWheelCircularQuotient:
        h = tuple(map(int, histogram))
        if len(h) < 2 or any(value < 0 for value in h):
            raise ValueError(h)
        baseline = h[-1]
        return cls(len(h), sum(h), tuple(value - baseline for value in h[:-1]))

    @property
    def baseline(self) -> int:
        return (self.total - sum(self.residue)) // self.prime

    def coefficient(self, phase: int) -> int:
        """Recover one histogram coefficient without lifting all q entries."""
        i = int(phase) % self.prime
        base = self.baseline
        return base if i == self.prime - 1 else base + self.residue[i]

    def histogram(self) -> tuple[int, ...]:
        base = self.baseline
        return tuple(base + value for value in self.residue) + (base,)

    def rotate(self, shift: int) -> PrimeWheelCircularQuotient:
        q = self.prime
        shift = int(shift) % q
        h = self.histogram()
        if shift:
            h = tuple(h[(index - shift) % q] for index in range(q))
        return PrimeWheelCircularQuotient.from_histogram(h)

    def add(self, other: PrimeWheelCircularQuotient) -> PrimeWheelCircularQuotient:
        if self.prime != other.prime:
            raise ValueError((self.prime, other.prime))
        return PrimeWheelCircularQuotient.from_histogram(
            tuple(
                a + b for a, b in zip(self.histogram(), other.histogram(), strict=True)
            )
        )

    @property
    def max_deviation(self) -> int:
        return max((abs(value) for value in self.residue), default=0)

    @property
    def description_bits(self) -> int:
        def signed_bits(value: int) -> int:
            value = abs(int(value))
            return 1 + bit_width(value)

        return (
            bit_width(self.prime)
            + bit_width(self.total)
            + sum(signed_bits(v) for v in self.residue)
        )


@dataclass(frozen=True, slots=True)
class PrimeWheelPhaseBlock:
    """Composable affine deletion-phase block for one wheel extension.

    If ``q`` is the new prime and ``alpha=-M**-1 (mod q)``, each old wheel
    gap ``g`` advances the deletion-copy phase by ``alpha*g``.  The block
    retains only the total phase shift and the exact circular histogram of
    prefix phases, quotiented by the uniform ``Phi_q`` direction above.

    For adjacent blocks ``A,B``, B's histogram is rotated by A's endpoint
    phase and then added.  This is the additive/wreath law needed for powered
    construction and rank queries; the individual phase itinerary is never
    retained.
    """

    prime: int
    alpha: int
    length: int
    phase_shift: int
    circular: PrimeWheelCircularQuotient
    compositions: int = 0

    def __post_init__(self) -> None:
        q = int(self.prime)
        if q < 2 or self.circular.prime != q:
            raise ValueError(self)
        if (
            int(self.length) < 0
            or self.circular.total != int(self.length)
            or int(self.compositions) < 0
        ):
            raise ValueError(self)
        object.__setattr__(self, "prime", q)
        object.__setattr__(self, "alpha", int(self.alpha) % q)
        object.__setattr__(self, "length", int(self.length))
        object.__setattr__(self, "phase_shift", int(self.phase_shift) % q)
        object.__setattr__(self, "compositions", int(self.compositions))

    @classmethod
    def identity(cls, prime: int, alpha: int) -> PrimeWheelPhaseBlock:
        q = int(prime)
        return cls(
            q,
            int(alpha) % q,
            0,
            0,
            PrimeWheelCircularQuotient.from_histogram((0,) * q),
            0,
        )

    @classmethod
    def gap(cls, gap: int, *, prime: int, alpha: int) -> PrimeWheelPhaseBlock:
        q = int(prime)
        a = int(alpha) % q
        h = [0] * q
        h[0] = 1
        return cls(
            q, a, 1, a * int(gap) % q, PrimeWheelCircularQuotient.from_histogram(h), 0
        )

    @classmethod
    def from_gaps(
        cls, gaps: Sequence[int], *, prime: int, alpha: int
    ) -> PrimeWheelPhaseBlock:
        """Build one phase block in O(len(gaps)+q), not O(len(gaps)*q)."""
        q = int(prime)
        a = int(alpha) % q
        if q < 2:
            raise ValueError(q)
        histogram = [0] * q
        phase = 0
        length = 0
        for gap in map(int, gaps):
            if gap <= 0:
                raise ValueError(gap)
            histogram[phase] += 1
            phase = (phase + a * gap) % q
            length += 1
        return cls(
            q, a, length, phase, PrimeWheelCircularQuotient.from_histogram(histogram), 0
        )

    @classmethod
    def from_endpoint_differences(
        cls,
        first_gap: int,
        differences: Sequence[int],
        *,
        prime: int,
        alpha: int,
    ) -> PrimeWheelPhaseBlock:
        """Build from the endpoint-difference field without storing endpoints.

        ``differences`` contains ``g[i+1]-g[i]`` for a linear block.  The
        initial gap plus these differences regenerates the exact gap action
        one symbol at a time and is used by the research compiler to test
        whether the difference field offers a smaller construction program.
        """
        gap = int(first_gap)
        if gap <= 0:
            raise ValueError(gap)
        gaps = [gap]
        for delta in map(int, differences):
            gap += delta
            if gap <= 0:
                raise ValueError(("nonpositive-gap", gap))
            gaps.append(gap)
        return cls.from_gaps(gaps, prime=prime, alpha=alpha)

    def then(self, other: PrimeWheelPhaseBlock) -> PrimeWheelPhaseBlock:
        if (self.prime, self.alpha) != (other.prime, other.alpha):
            raise ValueError(((self.prime, self.alpha), (other.prime, other.alpha)))
        shifted = other.circular.rotate(self.phase_shift)
        return PrimeWheelPhaseBlock(
            self.prime,
            self.alpha,
            self.length + other.length,
            (self.phase_shift + other.phase_shift) % self.prime,
            self.circular.add(shifted),
            self.compositions + other.compositions + 1,
        )

    def power_block(self, exponent: int) -> PrimeWheelPhaseBlock:
        base = PrimeWheelPhaseBlock(
            self.prime, self.alpha, self.length, self.phase_shift, self.circular, 0
        )
        powered = binary_power(
            base,
            exponent,
            identity=PrimeWheelPhaseBlock.identity(self.prime, self.alpha),
            compose=PrimeWheelPhaseBlock.then,
        )
        result = powered.value
        return PrimeWheelPhaseBlock(
            result.prime,
            result.alpha,
            result.length,
            result.phase_shift,
            result.circular,
            powered.compositions,
        )

    def phase_histogram(self, *, entering_phase: int = 0) -> tuple[int, ...]:
        return self.circular.rotate(int(entering_phase)).histogram()

    def count_phase(self, phase: int, *, entering_phase: int = 0) -> int:
        # rotate(entering)[phase] == original[phase-entering].  Recover just
        # that coefficient instead of allocating a q-entry lifted histogram.
        return self.circular.coefficient(int(phase) - int(entering_phase))

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "prime-wheel-phase-block",
            self.prime,
            self.alpha,
            self.length,
            self.phase_shift,
            self.circular.total,
            self.circular.residue,
        )

    @property
    def description_bits(self) -> int:
        return (
            bit_width(self.prime)
            + bit_width(self.alpha)
            + bit_width(self.length)
            + bit_width(self.phase_shift)
            + self.circular.description_bits
        )


@dataclass(frozen=True, slots=True)
class PrimeWheelExtensionMorphism:
    """Exact recursive descriptor for extending an Euler wheel by one prime.

    The morphism does not retain old residues or the deletion-copy itinerary.
    ``phase`` summarizes the old gap cycle; ``initial_copy`` is the sole
    absolute CRT phase needed to recover deletion counts in any of the q copies.
    """

    old_modulus: int
    new_prime: int
    initial_copy: int
    phase: PrimeWheelPhaseBlock

    def __post_init__(self) -> None:
        M, q = int(self.old_modulus), int(self.new_prime)
        if M <= 0 or q < 2 or gcd(M, q) != 1 or self.phase.prime != q:
            raise ValueError(self)
        if not 0 <= int(self.initial_copy) < q or self.phase.phase_shift != q - 1:
            raise ValueError(self)
        object.__setattr__(self, "old_modulus", M)
        object.__setattr__(self, "new_prime", q)
        object.__setattr__(self, "initial_copy", int(self.initial_copy))

    @classmethod
    def from_gaps(
        cls,
        old_gaps: Sequence[int],
        *,
        old_modulus: int,
        new_prime: int,
    ) -> PrimeWheelExtensionMorphism:
        gaps = tuple(map(int, old_gaps))
        M = int(old_modulus)
        q = int(new_prime)
        if not gaps or sum(gaps) != M or gcd(M, q) != 1:
            raise ValueError((gaps, M, q))
        inv = pow(M, -1, q)
        alpha = (-inv) % q
        return cls(
            M,
            q,
            (-inv) % q,
            PrimeWheelPhaseBlock.from_gaps(gaps, prime=q, alpha=alpha),
        )

    @property
    def new_modulus(self) -> int:
        return self.old_modulus * self.new_prime

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "prime-wheel-extension",
            self.old_modulus,
            self.new_prime,
            self.initial_copy,
            self.phase.canonical_key,
        )

    @property
    def description_bits(self) -> int:
        return (
            bit_width(self.old_modulus)
            + bit_width(self.new_prime)
            + bit_width(self.initial_copy)
            + self.phase.description_bits
        )

    def deletion_count(self, copy_index: int) -> int:
        """Count old vertices deleted in one q-copy without the phase itinerary."""
        return self.phase.count_phase(int(copy_index), entering_phase=self.initial_copy)

    def deletion_counts(self) -> tuple[int, ...]:
        # One O(q) lift is cheaper than q independent coefficient recoveries
        # (each of which must derive the uniform cyclotomic baseline).
        return self.phase.phase_histogram(entering_phase=self.initial_copy)

    def powered_old_cycles(self, copies: int) -> PrimeWheelPhaseBlock:
        return self.phase.power_block(int(copies))


@dataclass(frozen=True, slots=True)
class PrimeWheelExtensionIndex:
    """Non-expanding rank/select view of one exact Euler-wheel extension.

    The old wheel has ``N`` vertices and the new prime is ``q``.  The naive
    extension constructs ``q*N`` deletion flags before emitting ``N*(q-1)``
    gaps.  This index instead stores the old prefix residues and exactly one
    deletion position per old vertex, grouped by copy.  Retained size is
    O(N+q), while select/rank use binary search and never allocate the extended
    wheel.

    This closes the eager *single-extension* rank/select blocker.  Building a
    later extension from this view still needs a compact cross-modulus counting
    law; that deeper recursive-wheel closure is deliberately not claimed here.
    """

    old_gaps: tuple[int, ...]
    old_modulus: int
    new_prime: int
    morphism: PrimeWheelExtensionMorphism
    old_residues: tuple[int, ...]
    deletion_positions: tuple[tuple[int, ...], ...]
    cumulative_deletions: tuple[int, ...]

    @classmethod
    def build(
        cls,
        old_gaps: Sequence[int],
        *,
        old_modulus: int,
        new_prime: int,
    ) -> PrimeWheelExtensionIndex:
        gaps = tuple(map(int, old_gaps))
        M = int(old_modulus)
        q = int(new_prime)
        morphism = PrimeWheelExtensionMorphism.from_gaps(
            gaps, old_modulus=M, new_prime=q
        )
        residues: list[int] = []
        r = 1
        for gap in gaps:
            residues.append(r)
            r += gap
        if r != M + 1:
            raise AssertionError((r, M, gaps))
        by_copy: list[list[int]] = [[] for _ in range(q)]
        inv = pow(M, -1, q)
        for i, residue in enumerate(residues):
            copy = (-residue * inv) % q
            by_copy[copy].append(i)
        positions = tuple(tuple(xs) for xs in by_copy)
        cumulative = [0]
        for xs in positions:
            cumulative.append(cumulative[-1] + len(xs))
        if cumulative[-1] != len(gaps):
            raise AssertionError((cumulative[-1], len(gaps)))
        # Cross-check the phase quotient without lifting a deletion bitmap.
        if tuple(len(xs) for xs in positions) != morphism.deletion_counts():
            raise AssertionError("phase quotient disagrees with deletion index")
        return cls(gaps, M, q, morphism, tuple(residues), positions, tuple(cumulative))

    @property
    def old_length(self) -> int:
        return len(self.old_gaps)

    @property
    def length(self) -> int:
        return self.old_length * (self.new_prime - 1)

    @property
    def raw_length(self) -> int:
        return self.old_length * self.new_prime

    @property
    def new_modulus(self) -> int:
        return self.old_modulus * self.new_prime

    @property
    def retained_positions(self) -> int:
        return sum(len(xs) for xs in self.deletion_positions)

    def is_deleted_raw(self, raw_index: int) -> bool:
        t = int(raw_index)
        if not 0 <= t < self.raw_length:
            raise IndexError(t)
        copy, old_index = divmod(t, self.old_length)
        xs = self.deletion_positions[copy]
        j = bisect_left(xs, old_index)
        return j < len(xs) and xs[j] == old_index

    def deleted_before_raw(self, raw_count: int) -> int:
        """Deleted vertices in the raw half-open prefix ``[0, raw_count)``."""
        t = int(raw_count)
        if not 0 <= t <= self.raw_length:
            raise IndexError(t)
        copy, rem = divmod(t, self.old_length)
        if copy == self.new_prime:
            return self.old_length
        return self.cumulative_deletions[copy] + bisect_left(
            self.deletion_positions[copy], rem
        )

    def survivors_before_raw(self, raw_count: int) -> int:
        t = int(raw_count)
        return t - self.deleted_before_raw(t)

    def raw_index_at(self, rank: int) -> int:
        """Select zero-based survivor rank in O(log(q*N) log N)."""
        rank = int(rank)
        if not 0 <= rank < self.length:
            raise IndexError(rank)
        lo, hi = 0, self.raw_length
        while lo < hi:
            mid = (lo + hi) // 2
            if self.survivors_before_raw(mid + 1) <= rank:
                lo = mid + 1
            else:
                hi = mid
        if lo >= self.raw_length or self.is_deleted_raw(lo):
            raise AssertionError((rank, lo))
        return lo

    def residue_at(self, rank: int) -> int:
        raw = self.raw_index_at(int(rank))
        copy, old_index = divmod(raw, self.old_length)
        return copy * self.old_modulus + self.old_residues[old_index]

    def gap_at(self, rank: int) -> int:
        rank = int(rank)
        if not 0 <= rank < self.length:
            raise IndexError(rank)
        here = self.residue_at(rank)
        if rank + 1 < self.length:
            nxt = self.residue_at(rank + 1)
        else:
            nxt = self.new_modulus + self.residue_at(0)
        return nxt - here

    def rank_before(self, value: int) -> int:
        """Count extended-wheel residues strictly below ``value``."""
        x = int(value)
        if x <= 1:
            return 0
        if x > self.new_modulus:
            return self.length
        copy = min(self.new_prime - 1, (x - 1) // self.old_modulus)
        threshold = x - copy * self.old_modulus
        old_before = bisect_left(self.old_residues, threshold)
        raw_count = copy * self.old_length + old_before
        return self.survivors_before_raw(raw_count)

    def materialize_gaps(self) -> tuple[int, ...]:
        return tuple(self.gap_at(i) for i in range(self.length))

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("prime-wheel-extension-index", self.morphism.canonical_key)


@lru_cache(maxsize=131_072)
def _wheel_count_leq(
    primes: tuple[int, ...],
    depth: int,
    limit: int,
) -> int:
    """Legendre recurrence for one recursive wheel prefix.

    Returns the count of positive integers ``<= limit`` coprime to the first
    ``depth`` wheel primes.  The recurrence works on the compact prime
    descriptor; it never constructs residues, gaps, or a wheel bitmap.
    """
    from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG

    dag = CoprimeRankDAG(primes[: max(0, int(depth))], retain_queries=False)
    try:
        return dag.count(int(limit))
    finally:
        dag.close()


@dataclass(frozen=True, slots=True)
class PrimeRecursiveWheelIndex:
    """Exact nested-wheel rank/select without retaining any gap cycle.

    The wheel is represented only by its distinct prime factors.  Prefix rank
    is the exact Legendre inclusion/exclusion recurrence and select is a binary
    search over that monotone rank.  Consequently a later wheel extension is
    just ``with_prime(q)``; it does *not* require materializing the parent
    ``phi(M)`` residues or gaps first.

    This removes recursive carrier expansion.  It intentionally does not claim
    that the recurrence is polylogarithmic in the number of wheel factors; the
    separate unbounded nth-prime/magnitude frontier therefore remains honest.
    """

    primes: tuple[int, ...]
    modulus: int
    length: int

    @classmethod
    def from_primes(cls, primes: Sequence[int]) -> PrimeRecursiveWheelIndex:
        ps = tuple(map(int, primes))
        if not ps or ps != tuple(sorted(set(ps))):
            raise ValueError("wheel primes must be nonempty, distinct, and increasing")
        if any(not is_prime_u64(p) for p in ps):
            raise ValueError(("nonprime-wheel-factor", ps))
        modulus = prod(ps)
        length = prod(p - 1 for p in ps)
        return cls(ps, modulus, length)

    def with_prime(self, prime: int) -> PrimeRecursiveWheelIndex:
        q = int(prime)
        if q <= self.primes[-1] or not is_prime_u64(q):
            raise ValueError(q)
        return PrimeRecursiveWheelIndex.from_primes(self.primes + (q,))

    def rank_before(self, value: int) -> int:
        """Count wheel residues in ``[1, value)`` inside one period."""
        x = int(value)
        if x <= 1:
            return 0
        if x >= self.modulus + 1:
            return self.length
        return _wheel_count_leq(self.primes, len(self.primes), x - 1)

    def count_positive_below(self, value: int) -> int:
        """Count all positive integers ``< value`` coprime to the wheel."""
        x = int(value)
        if x <= 1:
            return 0
        maximum = x - 1
        full, rem = divmod(maximum, self.modulus)
        return full * self.length + self.rank_before(rem + 1)

    def residue_at(self, rank: int) -> int:
        """Select a zero-based wheel residue by binary rank descent."""
        r = int(rank)
        if not 0 <= r < self.length:
            raise IndexError(r)
        lo, hi = 1, self.modulus
        while lo < hi:
            mid = (lo + hi) // 2
            if self.rank_before(mid + 1) <= r:
                lo = mid + 1
            else:
                hi = mid
        if gcd(lo, self.modulus) != 1 or self.rank_before(lo) != r:
            raise AssertionError((r, lo, self.rank_before(lo)))
        return lo

    def gap_at(self, rank: int) -> int:
        r = int(rank)
        if not 0 <= r < self.length:
            raise IndexError(r)
        here = self.residue_at(r)
        nxt = (
            self.residue_at(r + 1)
            if r + 1 < self.length
            else self.modulus + self.residue_at(0)
        )
        return nxt - here

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("prime-recursive-wheel-index", self.primes)

    @property
    def description_bits(self) -> int:
        return bit_width(len(self.primes)) + sum(bit_width(p) for p in self.primes)


def recursive_prime_wheel_index(primes: Sequence[int]) -> PrimeRecursiveWheelIndex:
    return PrimeRecursiveWheelIndex.from_primes(primes)


def index_prime_wheel_extension(
    old_gaps: Sequence[int],
    *,
    old_modulus: int,
    new_prime: int,
) -> PrimeWheelExtensionIndex:
    return PrimeWheelExtensionIndex.build(
        old_gaps,
        old_modulus=int(old_modulus),
        new_prime=int(new_prime),
    )


def extend_prime_wheel_gaps(
    old_gaps: Sequence[int],
    *,
    old_modulus: int,
    new_prime: int,
) -> tuple[tuple[int, ...], PrimeWheelPhaseBlock, int]:
    """Compatibility materializer for one Euler-wheel extension.

    Random-access callers should use :func:`index_prime_wheel_extension`, which
    avoids the extended ``q*N`` bitmap and ``N*(q-1)`` gap vector.  This helper
    explicitly requests the full gap output and therefore necessarily pays for
    that output size, but it materializes directly through rank/select.
    """
    index = index_prime_wheel_extension(
        old_gaps,
        old_modulus=int(old_modulus),
        new_prime=int(new_prime),
    )
    return index.materialize_gaps(), index.morphism.phase, index.morphism.initial_copy


@dataclass(frozen=True, slots=True)
class PrimeWheelCyclotomicGroup:
    periods: tuple[int, ...]
    phases: tuple[int, ...]
    first_indices: tuple[int, ...]
    period_product: int
    field_prime: int
    field_multiplier: int
    root: int
    prime_candidates: int
    root_trials: int

    def __post_init__(self) -> None:
        n = len(self.periods)
        if not n or len(self.phases) != n or len(self.first_indices) != n:
            raise ValueError(self)
        if (
            prod(self.periods) != self.period_product
            or (self.field_prime - 1) % self.period_product
        ):
            raise ValueError(self)
        if pow(self.root, self.period_product, self.field_prime) != 1:
            raise ValueError("root does not lie in requested subgroup")
        if any(
            pow(self.root, self.period_product // q, self.field_prime) == 1
            for q in self.periods
        ):
            raise ValueError("root order is not the full squarefree wheel product")

    @property
    def state_bits(self) -> int:
        return bit_width(self.field_prime - 1)

    @property
    def descriptor_bits(self) -> int:
        return (
            self.state_bits
            + bit_width(self.period_product)
            + bit_width(self.root)
            + sum(
                bit_width(q) + bit_width(p) + bit_width(f)
                for q, p, f in zip(
                    self.periods, self.phases, self.first_indices, strict=True
                )
            )
        )

    def advance_value(self, state: int, steps: int) -> int:
        steps = int(steps)
        if steps < 0:
            raise ValueError(steps)
        multiplier = modular_power(self.root, steps, self.field_prime).value
        return (int(state) * multiplier) % self.field_prime

    def classify(self, state: int, index: int) -> tuple[bool, int]:
        """Return ``(composite_witness, root_projections)`` for this group."""
        state = int(state) % self.field_prime
        index = int(index)
        calls = 0
        for q, phase, first in zip(
            self.periods, self.phases, self.first_indices, strict=True
        ):
            if index < first:
                continue
            calls += 1
            exponent = self.period_product // q
            target = pow(self.root, (phase % q) * exponent, self.field_prime)
            if pow(state, exponent, self.field_prime) == target:
                return True, calls
        return False, calls


@dataclass(frozen=True, slots=True)
class PrimeWheelCyclotomicState:
    index: int
    values: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class PrimeWheelCyclotomicAutomaton:
    groups: tuple[PrimeWheelCyclotomicGroup, ...]
    lane_count: int
    construction_prime_candidates: int
    construction_root_trials: int

    @property
    def state_bits(self) -> int:
        return sum(group.state_bits for group in self.groups)

    @property
    def descriptor_bits(self) -> int:
        return sum(group.descriptor_bits for group in self.groups)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "prime-wheel-cyclotomic",
            tuple(
                (g.periods, g.phases, g.first_indices, g.field_prime, g.root)
                for g in self.groups
            ),
        )

    def zero(self) -> PrimeWheelCyclotomicState:
        return PrimeWheelCyclotomicState(0, (1,) * len(self.groups))

    def advance(
        self, state: PrimeWheelCyclotomicState, candidate_steps: int
    ) -> PrimeWheelCyclotomicState:
        steps = int(candidate_steps)
        if steps < 0:
            raise ValueError(steps)
        return PrimeWheelCyclotomicState(
            state.index + steps,
            tuple(
                group.advance_value(value, steps)
                for group, value in zip(self.groups, state.values, strict=True)
            ),
        )

    def classify_state(self, state: PrimeWheelCyclotomicState) -> tuple[bool, int]:
        if len(state.values) != len(self.groups):
            raise ValueError("state belongs to another wheel")
        calls = 0
        for group, value in zip(self.groups, state.values, strict=True):
            composite, used = group.classify(value, state.index)
            calls += used
            if composite:
                return False, calls
        return True, calls

    def classify_index(self, index: int) -> tuple[bool, int]:
        state = self.advance(self.zero(), int(index))
        return self.classify_state(state)


@lru_cache(maxsize=4096)
def _field_prime(
    period_product: int, word_bits: int, max_multiplier: int
) -> tuple[int, int, int] | None:
    m, bits, cap = int(period_product), int(word_bits), int(max_multiplier)
    if m <= 1 or bits < 3 or cap < 2:
        raise ValueError((m, bits, cap))
    # m is odd, so k must be even for k*m+1 to be an odd prime > 2.
    for tested, k in enumerate(range(2, cap + 1, 2), start=1):
        p = k * m + 1
        if p.bit_length() > bits:
            break
        if is_prime_u64(p):
            return p, k, tested
    return None


def _full_order_root(
    field_prime: int, period_product: int, periods: Sequence[int]
) -> tuple[int, int]:
    p, m = int(field_prime), int(period_product)
    qs = tuple(map(int, periods))
    for trial, h in enumerate(range(2, p), start=1):
        root = pow(h, (p - 1) // m, p)
        if root == 1:
            continue
        if all(pow(root, m // q, p) != 1 for q in qs):
            return root, trial
    raise AssertionError((p, m, qs))


def _build_group(
    lanes: Sequence[MultiplicativeLane],
    *,
    field_prime: int,
    field_multiplier: int,
    prime_candidates: int,
) -> PrimeWheelCyclotomicGroup:
    parts = tuple(lanes)
    periods = tuple(int(lane.factor) for lane in parts)
    phases = tuple(int(lane.phase) for lane in parts)
    first = tuple(int(lane.first_index) for lane in parts)
    m = prod(periods)
    root, root_trials = _full_order_root(field_prime, m, periods)
    return PrimeWheelCyclotomicGroup(
        periods,
        phases,
        first,
        m,
        int(field_prime),
        int(field_multiplier),
        root,
        int(prime_candidates),
        root_trials,
    )


def build_prime_wheel_cyclotomic_automaton(
    lanes: Sequence[MultiplicativeLane],
    *,
    word_bits: int = 62,
    max_multiplier: int = 256,
) -> PrimeWheelCyclotomicAutomaton:
    """Greedily pack exact divisor cycles into root-of-unity field groups.

    The grouping policy is deterministic and source-order preserving.  A lane is
    appended only when the enlarged squarefree period product admits a certified
    ``P=k*M+1`` prime inside ``word_bits`` with ``k<=max_multiplier``.
    """
    source = tuple(lanes)
    if not source:
        return PrimeWheelCyclotomicAutomaton((), 0, 0, 0)
    groups: list[PrimeWheelCyclotomicGroup] = []
    current: list[MultiplicativeLane] = []
    current_product = 1
    current_field: tuple[int, int, int] | None = None

    def finish() -> None:
        nonlocal current, current_product, current_field
        if not current:
            return
        if current_field is None:
            raise AssertionError((current_product, current))
        p, k, tested = current_field
        groups.append(
            _build_group(
                current, field_prime=p, field_multiplier=k, prime_candidates=tested
            )
        )
        current = []
        current_product = 1
        current_field = None

    for lane in source:
        q = int(lane.factor)
        trial_product = current_product * q
        trial = _field_prime(trial_product, int(word_bits), int(max_multiplier))
        if trial is None:
            finish()
            trial_product = q
            trial = _field_prime(trial_product, int(word_bits), int(max_multiplier))
            if trial is None:
                raise ValueError(
                    ("no-cyclotomic-field-prime", q, word_bits, max_multiplier)
                )
        current.append(lane)
        current_product = trial_product
        current_field = trial
    finish()
    return PrimeWheelCyclotomicAutomaton(
        tuple(groups),
        len(source),
        sum(group.prime_candidates for group in groups),
        sum(group.root_trials for group in groups),
    )


__all__ = [
    "PrimeRecursiveWheelIndex",
    "PrimeWheelCircularQuotient",
    "PrimeWheelCyclotomicAutomaton",
    "PrimeWheelCyclotomicGroup",
    "PrimeWheelCyclotomicState",
    "PrimeWheelExtensionIndex",
    "PrimeWheelExtensionMorphism",
    "PrimeWheelPhaseBlock",
    "build_prime_wheel_cyclotomic_automaton",
    "extend_prime_wheel_gaps",
    "index_prime_wheel_extension",
    "recursive_prime_wheel_index",
]

"""Packed/lcm wheel construction and finite prime-block execution.

This module owns wheel state and wheel mutation only. Pair-field coordinates,
least-factor projections, and hyperbolic summaries live in ``prime_coordinates``.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from math import gcd, isqrt

from number_compiler.sequences.prime.set import (
    PrimeBlockSummary,
    canonical_multiplicative_lanes,
    finite_cover_lanes,
    packed_generator_step,
)


class _WheelSupportMixin:
    limit: int

    @property
    def exact_high(self) -> int:
        return (int(self.limit) + 1) ** 2 - 1

    def supports(self, n: int) -> bool:
        n = int(n)
        return int(self.limit) < n <= self.exact_high


class _CoprimeWheelMixin(_WheelSupportMixin):
    modulus: int

    def is_prime(self, n: int) -> bool:
        n = int(n)
        if not self.supports(n):
            raise ValueError((n, self.limit, self.exact_high))
        return gcd(n, int(self.modulus)) == 1


@dataclass(frozen=True, slots=True)
class LcmWheel(_CoprimeWheelMixin):
    """Prime-independent packed factor set ``lcm(1,...,limit)``.

    For ``limit < n < (limit+1)^2``:

        n is prime  <=>  gcd(n, modulus) == 1.

    This is an exact finite-capacity carrier.  The modulus is charged by its
    actual bit length; representing the whole factor family by one integer does
    not make that information free.
    """

    limit: int
    modulus: int
    update_events: int
    construction_gcds: int

    @property
    def description_bits(self) -> int:
        return max(1, self.limit.bit_length()) + max(1, self.modulus.bit_length())

    @property
    def modulus_bits(self) -> int:
        return max(1, self.modulus.bit_length())


@lru_cache(maxsize=32)
def build_lcm_wheel(limit: int) -> LcmWheel:
    limit = int(limit)
    if limit < 1:
        raise ValueError(limit)
    modulus = 1
    events = 0
    gcds = 0
    for k in range(2, limit + 1):
        g = gcd(modulus, k)
        gcds += 1
        new_modulus = (modulus // g) * k
        if new_modulus != modulus:
            events += 1
            modulus = new_modulus
    return LcmWheel(limit, modulus, events, gcds)


@dataclass(frozen=True, slots=True)
class LcmWheelFirstPrime:
    start: int
    length: int
    first_index: int | None
    wheel_limit: int
    wheel_bits: int
    wheel_update_events: int
    gcd_calls: int

    @property
    def first_value(self) -> int | None:
        return None if self.first_index is None else self.start + 2 * self.first_index


def _admit_lcm_wheel(
    start: int, length: int, wheel: LcmWheel | None
) -> tuple[int, LcmWheel]:
    high = start + 2 * (length - 1)
    if wheel is None:
        wheel = build_lcm_wheel(isqrt(high))
    if not wheel.supports(start) or not wheel.supports(high):
        raise ValueError((start, high, wheel.limit, wheel.exact_high))
    return high, wheel


def first_prime_lcm_wheel(
    start: int,
    length: int,
    *,
    wheel: LcmWheel | None = None,
) -> LcmWheelFirstPrime:
    """Find the first prime among ``start+2*j`` using one packed factor set."""
    start, length = int(start), int(length)
    if start < 3 or start % 2 == 0 or length < 0:
        raise ValueError((start, length))
    if length == 0:
        return LcmWheelFirstPrime(start, 0, None, 1, 1, 0, 0)
    _unused_high_binding, wheel = _admit_lcm_wheel(start, length, wheel)
    calls = 0
    first: int | None = None
    for j in range(length):
        calls += 1
        if gcd(start + 2 * j, wheel.modulus) == 1:
            first = j
            break
    return LcmWheelFirstPrime(
        start,
        length,
        first,
        wheel.limit,
        wheel.modulus_bits,
        wheel.update_events,
        calls,
    )


@dataclass(frozen=True, slots=True)
class LcmWheelBlockProjection:
    start: int
    length: int
    summary: PrimeBlockSummary
    wheel_limit: int
    wheel_bits: int
    wheel_update_events: int
    gcd_calls: int


def project_odd_prime_block_lcm_wheel(
    start: int,
    length: int,
    *,
    wheel: LcmWheel | None = None,
) -> LcmWheelBlockProjection:
    """Exact count/first summary; unlike ``first_prime_lcm_wheel`` this charges L gcds."""
    start, length = int(start), int(length)
    if start < 3 or start % 2 == 0 or length < 0:
        raise ValueError((start, length))
    if length == 0:
        return LcmWheelBlockProjection(start, 0, PrimeBlockSummary.empty(), 1, 1, 0, 0)
    _unused_high_binding, wheel = _admit_lcm_wheel(start, length, wheel)
    count = 0
    first: int | None = None
    for j in range(length):
        if gcd(start + 2 * j, wheel.modulus) == 1:
            if first is None:
                first = j
            count += 1
    return LcmWheelBlockProjection(
        start,
        length,
        PrimeBlockSummary(length, count, first),
        wheel.limit,
        wheel.modulus_bits,
        wheel.update_events,
        length,
    )


@dataclass(frozen=True, slots=True)
class SquarefreeWheel(_CoprimeWheelMixin):
    """Prime-independent squarefree quotient of ``lcm(1,...,limit)``.

    Scanning all natural generators, lcm changes occur at prime powers.  The
    change ratio is folded through gcd against the retained modulus, so repeated
    powers of an already present prime disappear automatically.  The resulting
    modulus is the primorial ``product(p<=limit)`` without supplying a prime list.
    """

    limit: int
    modulus: int
    lcm_update_events: int
    generator_events: int
    construction_gcds: int

    @property
    def modulus_bits(self) -> int:
        return max(1, self.modulus.bit_length())


@lru_cache(maxsize=32)
def build_squarefree_wheel(limit: int) -> SquarefreeWheel:
    limit = int(limit)
    if limit < 1:
        raise ValueError(limit)
    lcm_value = 1
    modulus = 1
    lcm_events = 0
    generator_events = 0
    gcds = 0
    for k in range(2, limit + 1):
        g = gcd(lcm_value, k)
        gcds += 1
        new_lcm = (lcm_value // g) * k
        if new_lcm != lcm_value:
            lcm_events += 1
            ratio = new_lcm // lcm_value
            fresh = ratio // gcd(modulus, ratio)
            gcds += 1
            if fresh != 1:
                modulus *= fresh
                generator_events += 1
            lcm_value = new_lcm
    return SquarefreeWheel(limit, modulus, lcm_events, generator_events, gcds)


@dataclass(frozen=True, slots=True)
class FinitePackedPrimeWheel:
    """Window-specific packed quotient of the winning least-factor lanes.

    Only the modulus is retained.  ``source_*`` fields are instrumentation for
    the constructor and are not alternate semantic state.
    """

    start: int
    length: int
    modulus: int
    source_periodic_lanes: int
    source_active_lanes: int
    source_lane_hits: int

    @property
    def modulus_bits(self) -> int:
        return max(1, self.modulus.bit_length())

    def is_prime_index(self, index: int) -> bool:
        index = int(index)
        if not 0 <= index < self.length:
            raise IndexError(index)
        return gcd(self.start + 2 * index, self.modulus) == 1

    def first_prime(self) -> tuple[int | None, int]:
        calls = 0
        for j in range(self.length):
            calls += 1
            if self.is_prime_index(j):
                return j, calls
        return None, calls


def build_finite_packed_prime_wheel(start: int, length: int) -> FinitePackedPrimeWheel:
    start, length = int(start), int(length)
    if start < 3 or start % 2 == 0 or length < 0:
        raise ValueError((start, length))
    if length == 0:
        return FinitePackedPrimeWheel(start, 0, 1, 0, 0, 0)
    _candidates, _natural, periodic = canonical_multiplicative_lanes(start, length)
    active = finite_cover_lanes(start, length)
    modulus = 1
    for lane in active:
        modulus *= lane.factor
    return FinitePackedPrimeWheel(
        start,
        length,
        modulus,
        len(periodic),
        len(active),
        sum(lane.hits for lane in periodic),
    )


@dataclass(frozen=True, slots=True)
class PackedWheelState:
    residues: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class PackedWheelStep:
    state: PackedWheelState
    carries: tuple[int, ...]

    @property
    def carry_ones(self) -> int:
        return sum(self.carries)


@dataclass(frozen=True, slots=True)
class PackedWheelFirstPrime:
    start: int
    length: int
    first_index: int | None
    group_count: int
    total_group_bits: int
    gcd_calls: int
    carry_ones: int

    @property
    def first_value(self) -> int | None:
        return None if self.first_index is None else self.start + 2 * self.first_index


@dataclass(frozen=True, slots=True)
class PackedWheelProgram(_WheelSupportMixin):
    """Prime-independent word-packed coprimality program.

    Natural generators are scanned in increasing order.  LCM change ratios
    discover prime generators without a supplied prime list; already-seen prime
    powers are removed by gcd, and fresh generators are greedily multiplied
    into bounded-bit groups.  Each group residue evolves by addition plus one
    0/1 wrap carry.
    """

    limit: int
    word_bits: int
    moduli: tuple[int, ...]
    lcm_update_events: int
    generator_events: int

    @property
    def total_group_bits(self) -> int:
        return sum(max(1, modulus.bit_length()) for modulus in self.moduli)

    @property
    def group_count(self) -> int:
        return len(self.moduli)

    def state_for(self, n: int) -> PackedWheelState:
        n = int(n)
        if not self.supports(n):
            raise ValueError((n, self.limit, self.exact_high))
        return PackedWheelState(tuple(n % modulus for modulus in self.moduli))

    def step2(self, state: PackedWheelState) -> PackedWheelStep:
        if len(state.residues) != len(self.moduli):
            raise ValueError((len(state.residues), len(self.moduli)))
        residues: list[int] = []
        carries: list[int] = []
        for residue, modulus in zip(state.residues, self.moduli):
            total = int(residue) + 2
            carry = int(total >= modulus)
            if carry:
                total -= modulus
            residues.append(total)
            carries.append(carry)
        return PackedWheelStep(PackedWheelState(tuple(residues)), tuple(carries))

    def classify_state(self, state: PackedWheelState) -> tuple[bool, int]:
        """Return ``(is_prime, gcd_calls)`` with ordered early exit."""
        if len(state.residues) != len(self.moduli):
            raise ValueError((len(state.residues), len(self.moduli)))
        calls = 0
        for residue, modulus in zip(state.residues, self.moduli):
            calls += 1
            if gcd(residue, modulus) > 1:
                return False, calls
        return True, calls

    def first_prime(self, start: int, length: int) -> PackedWheelFirstPrime:
        start, length = int(start), int(length)
        if start < 3 or start % 2 == 0 or length < 0:
            raise ValueError((start, length))
        if length == 0:
            return PackedWheelFirstPrime(
                start, 0, None, self.group_count, self.total_group_bits, 0, 0
            )
        high = start + 2 * (length - 1)
        if not self.supports(start) or not self.supports(high):
            raise ValueError((start, high, self.limit, self.exact_high))
        state = self.state_for(start)
        gcd_calls = 0
        carry_ones = 0
        for j in range(length):
            is_prime, calls = self.classify_state(state)
            gcd_calls += calls
            if is_prime:
                return PackedWheelFirstPrime(
                    start,
                    length,
                    j,
                    self.group_count,
                    self.total_group_bits,
                    gcd_calls,
                    carry_ones,
                )
            if j + 1 < length:
                step = self.step2(state)
                state = step.state
                carry_ones += step.carry_ones
        return PackedWheelFirstPrime(
            start,
            length,
            None,
            self.group_count,
            self.total_group_bits,
            gcd_calls,
            carry_ones,
        )


@lru_cache(maxsize=32)
def build_packed_wheel_program(limit: int, word_bits: int = 63) -> PackedWheelProgram:
    limit, word_bits = int(limit), int(word_bits)
    if limit < 2 or word_bits < 2:
        raise ValueError((limit, word_bits))
    lcm_value = 1
    squarefree = 1
    groups: list[int] = []
    current = 1
    lcm_events = 0
    generator_events = 0
    for k in range(2, limit + 1):
        new_lcm = (lcm_value // gcd(lcm_value, k)) * k
        if new_lcm == lcm_value:
            continue
        lcm_events += 1
        ratio = new_lcm // lcm_value
        fresh = ratio // gcd(squarefree, ratio)
        if fresh != 1:
            generator_events += 1
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
    return PackedWheelProgram(
        limit, word_bits, tuple(groups), lcm_events, generator_events
    )


@dataclass(frozen=True, slots=True)
class SelfModifyingPackedWheel:
    """Incrementally discovers and packs its own prime generators.

    Invariant: ``moduli`` contain exactly the primes <= ``limit`` grouped in
    increasing discovery order.  To extend to k=limit+1, the existing carrier
    itself decides whether k is composite.  A coprime k is therefore a new
    prime generator and is appended to the last bounded-bit group.
    """

    limit: int
    word_bits: int
    moduli: tuple[int, ...]
    generator_count: int
    build_gcd_calls: int

    @property
    def group_count(self) -> int:
        return len(self.moduli)

    @property
    def total_group_bits(self) -> int:
        return sum(max(1, m.bit_length()) for m in self.moduli)

    def classify_generator_candidate(self, value: int) -> tuple[bool, int]:
        """Return whether value is coprime to every already-discovered group."""
        value = int(value)
        calls = 0
        for modulus in self.moduli:
            calls += 1
            if gcd(value, modulus) > 1:
                return False, calls
        return True, calls

    def extend_to(self, new_limit: int) -> SelfModifyingPackedWheel:
        new_limit = int(new_limit)
        if new_limit < self.limit:
            raise ValueError((self.limit, new_limit))
        groups = tuple(self.moduli)
        generators = self.generator_count
        calls = self.build_gcd_calls
        for k in range(self.limit + 1, new_limit + 1):
            groups, is_new, step_calls = packed_generator_step(
                groups, k, word_bits=self.word_bits
            )
            calls += step_calls
            if is_new:
                generators += 1
        return SelfModifyingPackedWheel(
            new_limit, self.word_bits, groups, generators, calls
        )

    def as_program(self) -> PackedWheelProgram:
        return PackedWheelProgram(
            self.limit, self.word_bits, self.moduli, 0, self.generator_count
        )


def build_self_modifying_packed_wheel(
    limit: int, word_bits: int = 62
) -> SelfModifyingPackedWheel:
    limit, word_bits = int(limit), int(word_bits)
    if limit < 1 or word_bits < 2:
        raise ValueError((limit, word_bits))
    return SelfModifyingPackedWheel(1, word_bits, (), 0, 0).extend_to(limit)


@dataclass(frozen=True, slots=True)
class BroadwordWheelStep:
    packed_residues: int
    carry_guard_bits: int
    group_count: int

    @property
    def carry_ones(self) -> int:
        return self.carry_guard_bits.bit_count()


@dataclass(frozen=True, slots=True)
class BroadwordPackedWheelProgram(_WheelSupportMixin):
    """SWAR packing of bounded wheel residues into one Python integer.

    Each 64-bit field stores a modulus/residue below 2**62.  Bit 63 is reserved
    as a subtraction guard, so adding replicated 2 cannot carry into the next
    field.  One broadword comparison/subtraction computes all per-group wrap
    carries exactly.  Coprimality/gcd projection intentionally remains separate.
    """

    limit: int
    moduli: tuple[int, ...]
    field_bits: int
    packed_moduli: int
    packed_twos: int
    guard_mask: int

    @property
    def group_count(self) -> int:
        return len(self.moduli)

    @property
    def packed_width_bits(self) -> int:
        return self.field_bits * len(self.moduli)

    @classmethod
    def build(cls, limit: int) -> BroadwordPackedWheelProgram:
        source = build_packed_wheel_program(int(limit), 62)
        field_bits = 64
        packed_moduli = 0
        packed_twos = 0
        guard_mask = 0
        for i, modulus in enumerate(source.moduli):
            if modulus >= (1 << 62):
                raise AssertionError(modulus)
            shift = field_bits * i
            packed_moduli |= modulus << shift
            packed_twos |= 2 << shift
            guard_mask |= (1 << 63) << shift
        return cls(
            source.limit,
            source.moduli,
            field_bits,
            packed_moduli,
            packed_twos,
            guard_mask,
        )

    def pack_state(self, n: int) -> int:
        n = int(n)
        if not self.supports(n):
            raise ValueError((n, self.limit, self.exact_high))
        packed = 0
        for i, modulus in enumerate(self.moduli):
            packed |= (n % modulus) << (self.field_bits * i)
        return packed

    def unpack_state(self, packed: int) -> tuple[int, ...]:
        packed = int(packed)
        mask = (1 << self.field_bits) - 1
        return tuple(
            (packed >> (self.field_bits * i)) & mask for i in range(self.group_count)
        )

    def step2(self, packed: int) -> BroadwordWheelStep:
        packed = int(packed)
        # All source residues are <2**62, so +2 stays below the guard at bit 63
        # and cannot spill into a neighbouring 64-bit field.
        trial = packed + self.packed_twos
        compared = (trial | self.guard_mask) - self.packed_moduli
        carry_guards = compared & self.guard_mask
        # Expand each independent guard bit downward to a full 64-bit selector.
        selector = carry_guards
        selector |= selector >> 1
        selector |= selector >> 2
        selector |= selector >> 4
        selector |= selector >> 8
        selector |= selector >> 16
        selector |= selector >> 32
        out = trial - (self.packed_moduli & selector)
        return BroadwordWheelStep(out, carry_guards, self.group_count)

    def classify_packed(self, packed: int) -> tuple[bool, int]:
        residues = self.unpack_state(packed)
        calls = 0
        for residue, modulus in zip(residues, self.moduli):
            calls += 1
            if gcd(residue, modulus) > 1:
                return False, calls
        return True, calls


__all__ = [
    "BroadwordPackedWheelProgram",
    "BroadwordWheelStep",
    "FinitePackedPrimeWheel",
    "LcmWheel",
    "LcmWheelBlockProjection",
    "LcmWheelFirstPrime",
    "PackedWheelFirstPrime",
    "PackedWheelProgram",
    "PackedWheelState",
    "PackedWheelStep",
    "SelfModifyingPackedWheel",
    "SquarefreeWheel",
    "build_finite_packed_prime_wheel",
    "build_lcm_wheel",
    "build_packed_wheel_program",
    "build_self_modifying_packed_wheel",
    "build_squarefree_wheel",
    "first_prime_lcm_wheel",
    "project_odd_prime_block_lcm_wheel",
]

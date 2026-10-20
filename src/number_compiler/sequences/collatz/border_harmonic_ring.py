"""Exact 2-adic/odd-prime ring for the zero-tail-free 6305 border cycle.

The two normalized odd symbols in one return have the action
    R(x) + 1 = 9 * (x + 1) / 4.
For a 3-ending source, v2(x+1) >= 2*r+1 is equivalent to r consecutive
returns to a 3-ending border.  No intermediate digit or valuation scan is
needed.  This ring predicts only this proved cycle, not arbitrary successors.

Odd-prime residues use multiplication by 9/4 in Z/p**k.  A binary request
instead uses the *higher-precision* input x+1, whose shift is exact on the
certified cylinder.  The symbolic radial scale is (2*r, 2*r).  Both clocks
remain on the same source-bound action, and positions/Walsh are demanded only.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import TYPE_CHECKING, cast

from number_compiler.arithmetic.fields.homogeneous_growth import (
    HomogeneousGrowthScale,
)
from number_compiler.arithmetic.fields.integer_congruence import exact_modular_power
from number_compiler.arithmetic.fields.two_adic import v2_positive

if TYPE_CHECKING:
    from number_compiler.arithmetic.fields.homogeneous_growth import (
        GrowthArithmeticEvaluator,
    )
    from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
        DyadicTerminalFieldAction,
    )
    from number_compiler.sequences.collatz.position_cycle_harmonics import (
        PositionHarmonicSpectrum,
    )


def _radix_modulus(radix: int, places: int) -> int:
    """Validate and construct the shared bounded radix modulus."""
    if type(radix) is not int or not 2 <= radix <= 64:
        raise ValueError("radix port must use a base from 2 to 64")
    if type(places) is not int or not 1 <= places <= 256:
        raise ValueError("radix precision outside supported budget")
    modulus: int = radix**places
    return modulus


def _radix_cylinder(
    radix: int,
    places: int,
    repetitions: int,
    *,
    admits: Callable[[int], bool],
) -> tuple[int, int, int]:
    """Validate one requested residue and split its modulus into CRT parts."""
    modulus = _radix_modulus(radix, places)
    if not admits(repetitions):
        raise ValueError("radix request is outside the source-certified ring")
    two_bits = (modulus & -modulus).bit_length() - 1
    return modulus, two_bits, modulus >> two_bits


def _join_radix_residues(
    low: int, high: int, two_bits: int, odd_modulus: int, modulus: int
) -> int:
    """Reconstruct the exact residue from its coprime 2-adic/odd views."""
    if odd_modulus == 1:
        return low
    shift = 1 << two_bits
    inverse: int = pow(shift, -1, odd_modulus)
    return (low + shift * (((high - low) * inverse) % odd_modulus)) % modulus


def _hybrid_radix_residue(
    radix: int,
    places: int,
    repetitions: int,
    *,
    admits: Callable[[int], bool],
    binary_residue: Callable[[int, int], int],
    odd_residue: Callable[[int, int, int], int],
) -> int:
    modulus, two_bits, odd_modulus = _radix_cylinder(
        radix, places, repetitions, admits=admits
    )
    if two_bits == 0:
        return odd_residue(radix, places, repetitions)
    binary = binary_residue(two_bits, repetitions)
    if odd_modulus == 1:
        return binary
    odd = odd_residue(odd_modulus, 1, repetitions)
    return _join_radix_residues(binary, odd, two_bits, odd_modulus, modulus)


@dataclass(frozen=True, slots=True)
class ZeroTailFreeBorderRing:
    """A source-authenticated closed prefix of the 3->3 6305 return language."""

    source: int
    return_capacity: int

    @classmethod
    def from_source(cls, source: int) -> ZeroTailFreeBorderRing:
        if type(source) is not int or source <= 0 or source % 10 != 3:
            raise ValueError("6305 harmonic ring requires a positive 3-ending source")
        return cls(source, (v2_positive(source + 1) - 1) // 2)

    def __post_init__(self) -> None:
        if type(self.source) is not int or self.source <= 0 or self.source % 10 != 3:
            raise ValueError("foreign 6305 source")
        if (
            type(self.return_capacity) is not int
            or self.return_capacity < 0
            or self.return_capacity != (v2_positive(self.source + 1) - 1) // 2
        ):
            raise ValueError("ring capacity disagrees with the 2-adic cylinder")

    def admissible_count(self, *, ticks: int, returns: int) -> int:
        """Maximal *3-return* block within the authorized physical horizon."""
        if type(ticks) is not int or ticks < 0:
            raise ValueError("negative physical horizon")
        if type(returns) is not int or returns < 0:
            raise ValueError("negative return budget")
        return min(self.return_capacity, ticks // 4, returns)

    def admits(self, repetitions: int) -> bool:
        if type(repetitions) is not int or repetitions < 0:
            raise ValueError("repeat count must be nonnegative")
        return repetitions <= self.return_capacity

    def endpoint(
        self,
        repetitions: int,
        *,
        on_power: Callable[[int, int, int], None] | None = None,
    ) -> int:
        """Cancel all binary shifts before allocating 9**r."""
        if not self.admits(repetitions):
            raise ValueError("requested border repetition is not source admitted")
        power = 9**repetitions
        if on_power is not None:
            on_power(9, repetitions, power)
        endpoint: int = power * ((self.source + 1) >> (2 * repetitions)) - 1
        return endpoint

    def odd_prime_residue(self, prime: int, places: int, repetitions: int) -> int:
        """Exact affine action at an odd prime-power digit boundary."""
        if type(prime) is not int or prime < 3 or prime % 2 == 0:
            raise ValueError("prime port requires an odd base")
        if type(places) is not int or not 1 <= places <= 2048:
            raise ValueError("prime precision outside supported budget")
        if prime.bit_length() * places > 4096:
            raise ValueError("prime-power modulus exceeds the 4096-bit budget")
        if not self.admits(repetitions):
            raise ValueError("prime request is outside the source cylinder")
        modulus: int = prime**places
        four_power = exact_modular_power(4, repetitions, modulus)
        inverse_power = exact_modular_power(four_power, -1, modulus)
        residue: int = (
            exact_modular_power(9, repetitions, modulus)
            * (self.source + 1)
            * inverse_power
            - 1
        ) % modulus
        return residue

    def binary_residue(self, bits: int, repetitions: int) -> int:
        """Preserve required 2-adic lookahead across 2*r right shifts."""
        if type(bits) is not int or not 0 <= bits <= 65536:
            raise ValueError("binary precision outside supported budget")
        if not self.admits(repetitions):
            raise ValueError("binary request is outside the source cylinder")
        if not bits:
            return 0
        modulus = 1 << bits
        # The right shift consumes 2*r low bits.  The original source
        # cylinder supplies exactly those bits; no full 9**r endpoint exists.
        shifted = ((self.source + 1) >> (2 * repetitions)) % modulus
        return (pow(9, repetitions, modulus) * shifted - 1) % modulus

    def radix_residue(self, radix: int, places: int, repetitions: int) -> int:
        """Exact base-3/6/10/64 port with conditional 2-adic lookahead.

        Radix is a requested digit boundary, *not* a source authorization.
        For even moduli the numerator is divided in the integers before the
        residue is projected, rather than incorrectly inverted modulo 2**k.
        """
        return _hybrid_radix_residue(
            radix,
            places,
            repetitions,
            admits=self.admits,
            binary_residue=self.binary_residue,
            odd_residue=self.odd_prime_residue,
        )

    def scale(self, repetitions: int) -> HomogeneousGrowthScale:
        if not self.admits(repetitions):
            raise ValueError("radial clock is outside the source cylinder")
        return HomogeneousGrowthScale(2 * repetitions, 2 * repetitions)

    def demanded_position_harmonics(
        self, repetitions: int, radix: int, position: int, *, walsh64: bool = False
    ) -> PositionHarmonicSpectrum:
        """Use the already minimized, source-bound position frequency owner."""
        from number_compiler.sequences.collatz.position_cycle_harmonics import (
            ZeroTailFree6305Orbit,
        )

        if not self.admits(repetitions):
            raise ValueError("position demand is outside the source cylinder")
        return ZeroTailFree6305Orbit(self.source, repetitions).spectrum(
            radix, position, walsh64=walsh64
        )


@dataclass(frozen=True, slots=True)
class ConstantTail6305Ring:
    """Source-closed repeating 3->3 border with any *fixed* zero-tail j.

    Its identical normalized word is 1, 0**j, 1.  The signed defect
    D=((2**(j+2)-9)*x - (3+2**(j+1))) is multiplied by 9/2**(j+2)
    at each admitted return.  Requiring one residual factor of 2 after
    every copy forces the endpoint back to the odd digit 3 (F5 remains 3).
    This is an exact unary right congruence, not a future selector for a
    different j or a claim about the unbounded Collatz language.
    """

    source: int
    tail: int
    return_capacity: int

    @classmethod
    def from_source(cls, source: int) -> ConstantTail6305Ring:
        if type(source) is not int or source <= 0 or source % 10 != 3:
            raise ValueError("constant-tail ring requires a 3-ending source")
        tail = v2_positive(3 * ((source - 3) // 10) + 1)
        d = tail + 2
        defect = ((1 << d) - 9) * source - (3 + (1 << (tail + 1)))
        if defect == 0:
            raise AssertionError("positive three-ending source has zero border defect")
        return cls(source, tail, max(0, (v2_positive(abs(defect)) - 1) // d))

    def __post_init__(self) -> None:
        if type(self.source) is not int or self.source <= 0 or self.source % 10 != 3:
            raise ValueError("ring source is not a three-border state")
        if type(self.tail) is not int or self.tail < 0:
            raise ValueError("tail must be a nonnegative integer")
        if type(self.return_capacity) is not int or self.return_capacity < 0:
            raise ValueError("invalid ring capacity")
        numerator = 3 * ((self.source - 3) // 10) + 1
        if v2_positive(numerator) != self.tail:
            raise ValueError("tail is not source certified")
        defect = self.defect
        if defect == 0 or self.return_capacity != max(
            0, (v2_positive(abs(defect)) - 1) // self.steps
        ):
            raise ValueError("constant-tail guard does not match its cylinder")

    @property
    def steps(self) -> int:
        return self.tail + 2

    @property
    def offset(self) -> int:
        return 3 + (1 << (self.tail + 1))

    @property
    def denominator_defect(self) -> int:
        return (1 << self.steps) - 9

    @property
    def defect(self) -> int:
        return self.denominator_defect * self.source - self.offset

    @classmethod
    def guard_residue(cls, tail: int, repetitions: int) -> tuple[int, int]:
        """Minimal binary cylinder ensuring r completed 3->3 returns.

        A fixed odd K is invertible in Z_2. Every admitted source must
        satisfy K*x=B (mod 2**(d*r+1)); the additional bit guarantees the
        odd (hence mod-10 3) *last* endpoint.
        """
        if type(tail) is not int or tail < 0:
            raise ValueError("negative zero tail")
        if type(repetitions) is not int or repetitions < 1:
            raise ValueError("guard repetition must be positive")
        bits = (tail + 2) * repetitions + 1
        if bits > 8192:
            raise ValueError("requested finite guard exceeds the ring budget")
        modulus = 1 << bits
        k = (1 << (tail + 2)) - 9
        b = 3 + (1 << (tail + 1))
        return (b * pow(k, -1, modulus)) % modulus, modulus

    def admits(self, repetitions: int) -> bool:
        if type(repetitions) is not int or repetitions < 0:
            raise ValueError("repetition must be nonnegative")
        return repetitions <= self.return_capacity

    def admitted_count(self, *, ticks: int, returns: int) -> int:
        if type(ticks) is not int or ticks < 0:
            raise ValueError("negative clock request")
        if type(returns) is not int or returns < 0:
            raise ValueError("negative return request")
        return min(self.return_capacity, ticks // (self.tail + 4), returns)

    def endpoint(
        self,
        repetitions: int,
        *,
        on_power: Callable[[int, int, int], None] | None = None,
    ) -> int:
        if not self.admits(repetitions):
            raise ValueError("constant-tail repeat is not source certified")
        reduced = self.defect >> (self.steps * repetitions)
        power = 9**repetitions
        if on_power is not None:
            on_power(9, repetitions, power)
        numerator = power * reduced + self.offset
        quotient, remainder = divmod(numerator, self.denominator_defect)
        if remainder or quotient <= 0:
            raise AssertionError("constant-tail affine power lost its exact endpoint")
        endpoint: int = quotient
        return endpoint

    def binary_residue(self, bits: int, repetitions: int) -> int:
        if type(bits) is not int or not 0 <= bits <= 65536:
            raise ValueError("binary precision outside supported budget")
        if not self.admits(repetitions):
            raise ValueError("binary request exceeds source cylinder")
        if bits == 0:
            return 0
        modulus = 1 << bits
        shifted_defect = (self.defect >> (self.steps * repetitions)) % modulus
        return (
            (pow(9, repetitions, modulus) * shifted_defect + self.offset)
            * pow(self.denominator_defect, -1, modulus)
        ) % modulus

    def odd_prime_residue(self, odd_base: int, places: int, repetitions: int) -> int:
        if type(odd_base) is not int or odd_base < 3 or odd_base & 1 == 0:
            raise ValueError("odd prime-radix port needs an odd base")
        if type(places) is not int or not 1 <= places <= 2048:
            raise ValueError("odd-prime precision outside supported budget")
        if odd_base.bit_length() * places > 4096:
            raise ValueError("odd-prime modulus exceeds the 4096-bit budget")
        if not self.admits(repetitions):
            raise ValueError("odd-prime request exceeds source cylinder")
        modulus = odd_base**places
        inverse: int = cast(int, pow(1 << self.steps, -1, modulus))
        step_gain = 9 * inverse % modulus
        step_offset = self.offset * inverse % modulus
        gain, offset = 1, 0
        count = repetitions
        while count:
            if count & 1:
                gain, offset = (
                    (step_gain * gain) % modulus,
                    (step_gain * offset + step_offset) % modulus,
                )
            step_offset = step_gain * step_offset + step_offset
            step_offset %= modulus
            step_gain = step_gain * step_gain % modulus
            count >>= 1
        residue: int = (gain * self.source + offset) % modulus
        return residue

    def radix_residue(self, radix: int, places: int, repetitions: int) -> int:
        return _hybrid_radix_residue(
            radix,
            places,
            repetitions,
            admits=self.admits,
            binary_residue=self.binary_residue,
            odd_residue=self.odd_prime_residue,
        )

    def scale(self, repetitions: int) -> HomogeneousGrowthScale:
        if not self.admits(repetitions):
            raise ValueError("radial request exceeds source cylinder")
        return HomogeneousGrowthScale(2 * repetitions, self.steps * repetitions)

    def demanded_position_harmonics(
        self, repetitions: int, radix: int, position: int, *, walsh64: bool = False
    ) -> PositionHarmonicSpectrum:
        from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
            DyadicTerminalFieldAction,
        )
        from number_compiler.sequences.collatz.position_cycle_harmonics import (
            CenteredMotifPositionOrbit,
        )

        if not self.admits(repetitions):
            raise ValueError("position demand exceeds source cylinder")
        one = DyadicTerminalFieldAction.one_run(1)
        word = one.then(DyadicTerminalFieldAction.zero_run(self.tail)).then(one)
        return CenteredMotifPositionOrbit(self.source, repetitions, word, 2).spectrum(
            radix, position, walsh64=walsh64
        )


def zero_tail_word_coefficients(tails: tuple[int, ...]) -> tuple[int, int, int]:
    """Compose an exact finite sequence of 6305 zero-tail returns."""
    if (
        type(tails) is not tuple
        or not tails
        or any(type(j) is not int or j < 0 or j > 4096 for j in tails)
        or sum(j + 2 for j in tails) > 8191
    ):
        raise ValueError("6305 tail word exceeds the certified coefficient budget")
    gain, offset, steps = 1, 0, 0
    for j in tails:
        offset = 9 * offset + (1 << steps) * (3 + (1 << (j + 1)))
        gain *= 9
        steps += j + 2
    return gain, offset, steps


def _periodic_tail_coefficients(motif: tuple[int, ...]) -> tuple[int, int, int]:
    """Compose a recorded *mixed* 6305 return word without any source digits."""
    if (
        type(motif) is not tuple
        or not 2 <= len(motif) <= 4
        or any(type(j) is not int or j < 0 for j in motif)
        or len(set(motif)) == 1
    ):
        raise ValueError("periodic ring requires 2..4 changing zero-tail letters")
    return zero_tail_word_coefficients(motif)


def periodic_return_capacity(defect: int, steps: int) -> int | None:
    """Exact number of repeated motif returns; ``None`` means unbounded.

    A zero defect is a genuine fixed point of the affine return, not a very
    large finite capacity. The explicit unbounded value keeps callers from
    treating an arbitrary sentinel as a totality proof.
    """
    if type(defect) is not int or type(steps) is not int or steps <= 0:
        raise ValueError("periodic return capacity needs an exact defect and step")
    return None if defect == 0 else max(0, (v2_positive(abs(defect)) - 1) // steps)


@dataclass(frozen=True, slots=True)
class PeriodicTail6305Ring:
    """A **conditional** repeated changing-tail border action.

    This is a source-bound future language, not a guess that an observed
    tail motif remains periodic. For an issued motif W, A(x)=(a*x+B)/2**d,
    K=2**d-a and D=K*x-B. D(A(x))=a*D(x)/2**d. Because a is odd and the
    completed return always has residue 3 modulo 5, the guard
    v2(D)>=d*r+1 certifies r copies returning to the odd 3-border.

    A distinct word may begin after the certified extent: the producer must
    resume its exact upper carry cursor there. Only finite, admitted words
    are published; the orbit is not a global Collatz period claim.
    """

    source: int
    motif: tuple[int, ...]
    gain: int
    offset: int
    steps: int
    return_capacity: int | None

    def __post_init__(self) -> None:
        # Do not allow callers to forge source authorization by constructing
        # a dataclass with an arbitrary capacity or affine coefficient.
        if type(self.source) is not int or self.source <= 0 or self.source % 10 != 3:
            raise ValueError("periodic ring has no positive 3-border source")
        gain, offset, steps = _periodic_tail_coefficients(self.motif)
        if (self.gain, self.offset, self.steps) != (gain, offset, steps):
            raise ValueError("periodic ring coefficients do not match its motif")
        upper = 3 * ((self.source - 3) // 10) + 1
        for j in self.motif:
            if v2_positive(upper) != j:
                raise ValueError("periodic ring has an unauthenticated zero tail")
            odd = upper >> j
            if odd & 3 != 3:
                raise ValueError("periodic ring crosses an eight-border exit")
            upper = (9 * odd + 1) >> 2
        defect = ((1 << steps) - gain) * self.source - offset
        capacity = periodic_return_capacity(defect, steps)
        if (
            (self.return_capacity is not None and type(self.return_capacity) is not int)
            or self.return_capacity != capacity
            or (capacity is not None and capacity < 1)
        ):
            raise ValueError("periodic ring has a foreign source-cylinder capacity")

    @classmethod
    def from_source(cls, source: int, motif: tuple[int, ...]) -> PeriodicTail6305Ring:
        if type(source) is not int or source <= 0 or source % 10 != 3:
            raise ValueError("periodic ring requires a positive 3-ending source")
        gain, offset, steps = _periodic_tail_coefficients(motif)
        # Authenticate *every* member of the first named border motif.
        upper = 3 * ((source - 3) // 10) + 1
        for j in motif:
            if v2_positive(upper) != j:
                raise ValueError("motif disagrees with its exact upper carry")
            odd = upper >> j
            if odd & 3 != 3:
                raise ValueError("motif exits to 8 before its final return")
            upper = (9 * odd + 1) >> 2
        defect = ((1 << steps) - gain) * source - offset
        capacity = periodic_return_capacity(defect, steps)
        if capacity is not None and capacity < 1:
            raise ValueError("first motif has no completed 3-border guard")
        return cls(source, motif, gain, offset, steps, capacity)

    @property
    def physical_ticks(self) -> int:
        return sum(j + 4 for j in self.motif)

    @property
    def defect(self) -> int:
        return ((1 << self.steps) - self.gain) * self.source - self.offset

    @classmethod
    def guard_residue(cls, motif: tuple[int, ...], repetitions: int) -> tuple[int, int]:
        """One exact Hensel cylinder for an entire repeated changing-tail word."""
        gain, offset, steps = _periodic_tail_coefficients(motif)
        if type(repetitions) is not int or repetitions < 1:
            raise ValueError("repetition must be positive")
        bits = steps * repetitions + 1
        if bits > 8192:
            raise ValueError("periodic guard exceeds 8192-bit proof budget")
        modulus = 1 << bits
        k = (1 << steps) - gain  # Always odd; exact 2-adic inverse exists.
        return (offset * pow(k, -1, modulus)) % modulus, modulus

    def admits(self, repetitions: int) -> bool:
        if type(repetitions) is not int or repetitions < 0:
            raise ValueError("repetitions must be nonnegative")
        return self.return_capacity is None or repetitions <= self.return_capacity

    def admitted_count(self, *, ticks: int, returns: int) -> int:
        if type(ticks) is not int or ticks < 0:
            raise ValueError("physical horizon cannot be negative")
        if type(returns) is not int or returns < 0:
            raise ValueError("return budget cannot be negative")
        budgeted = min(ticks // self.physical_ticks, returns // len(self.motif))
        return (
            budgeted
            if self.return_capacity is None
            else min(self.return_capacity, budgeted)
        )

    def endpoint(
        self,
        repetitions: int,
        *,
        on_power: Callable[[int, int, int], None] | None = None,
    ) -> int:
        """Cancel the full 2-adic cone before allocating the power of 3."""
        if not self.admits(repetitions):
            raise ValueError("requested periodic power is not source admitted")
        k = (1 << self.steps) - self.gain
        if self.defect == 0:
            return self.source
        gain_power: int = self.gain**repetitions
        if on_power is not None:
            on_power(self.gain, repetitions, gain_power)
        quotient_value, remainder = divmod(
            gain_power * (self.defect >> (self.steps * repetitions)) + self.offset,
            k,
        )
        quotient: int = quotient_value
        if remainder or quotient <= 0 or quotient % 10 != 3:
            raise AssertionError("periodic 6305 power lost its border certificate")
        return quotient

    def scale(self, repetitions: int) -> HomogeneousGrowthScale:
        if not self.admits(repetitions):
            raise ValueError("radial clock exceeds periodic border cylinder")
        return HomogeneousGrowthScale(
            2 * len(self.motif) * repetitions, self.steps * repetitions
        )

    def word(
        self,
        *,
        on_compose: Callable[
            [DyadicTerminalFieldAction, DyadicTerminalFieldAction], None
        ]
        | None = None,
    ) -> DyadicTerminalFieldAction:
        """Construct the exact parity program only after the guard is issued."""
        from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
            DyadicTerminalFieldAction,
        )

        def compose(
            first: DyadicTerminalFieldAction, second: DyadicTerminalFieldAction
        ) -> DyadicTerminalFieldAction:
            if on_compose is not None and first.steps and second.steps:
                on_compose(first, second)
            return first.then(second)

        one = DyadicTerminalFieldAction.one_run(1)
        action = DyadicTerminalFieldAction.identity()
        for j in self.motif:
            action = compose(
                compose(compose(action, one), DyadicTerminalFieldAction.zero_run(j)),
                one,
            )
        if (
            action.gain != self.gain
            or action.offset != self.offset
            or action.steps != self.steps
            or not action.certifies(self.source)
        ):
            raise AssertionError("periodic ring parity action lost its source")
        return action

    def binary_residue(self, bits: int, repetitions: int) -> int:
        """Exact 2-adic endpoint, dividing the certified defect *first*."""
        if type(bits) is not int or not 0 <= bits <= 65536:
            raise ValueError("2-adic precision outside supported budget")
        if not self.admits(repetitions):
            raise ValueError("2-adic request exceeds periodic source guard")
        if bits == 0:
            return 0
        modulus = 1 << bits
        k = (1 << self.steps) - self.gain
        numerator = (
            pow(self.gain, repetitions, modulus)
            * ((self.defect >> (self.steps * repetitions)) % modulus)
            + self.offset
        ) % modulus
        residue: int = numerator * pow(k, -1, modulus) % modulus
        return residue

    def odd_modulus_residue(self, modulus: int, repetitions: int) -> int:
        """Power the affine unit action over the odd CRT component."""
        if type(modulus) is not int or modulus < 1 or modulus % 2 == 0:
            raise ValueError("odd residue request needs a positive odd modulus")
        if modulus.bit_length() > 4096:
            raise ValueError("odd modulus exceeds 4096-bit observer budget")
        if not self.admits(repetitions):
            raise ValueError("odd residue request exceeds periodic source guard")
        if modulus == 1:
            return 0
        inverse = pow(2, -self.steps, modulus)
        unit_gain = self.gain * inverse % modulus
        unit_offset = self.offset * inverse % modulus
        gain, offset = 1, 0
        count = repetitions
        while count:
            if count & 1:
                gain, offset = (
                    (unit_gain * gain) % modulus,
                    (unit_gain * offset + unit_offset) % modulus,
                )
            unit_offset = (unit_gain * unit_offset + unit_offset) % modulus
            unit_gain = unit_gain * unit_gain % modulus
            count >>= 1
        return (gain * self.source + offset) % modulus

    def radix_residue(self, radix: int, places: int, repetitions: int) -> int:
        """Demand base-3/6/10/64 digits by source-bound CRT, not full powers."""
        modulus, two_bits, odd_modulus = _radix_cylinder(
            radix, places, repetitions, admits=self.admits
        )
        if two_bits == 0:
            return self.odd_modulus_residue(modulus, repetitions)
        low = self.binary_residue(two_bits, repetitions)
        if odd_modulus == 1:
            return low
        high = self.odd_modulus_residue(odd_modulus, repetitions)
        return _join_radix_residues(low, high, two_bits, odd_modulus, modulus)

    def demanded_sturmian_leading(
        self, repetitions: int, width: int, evaluator: GrowthArithmeticEvaluator
    ) -> dict[str, object]:
        """Certified *centered homogeneous* prefix, not affine endpoint bits."""
        from number_compiler.sequences.collatz.position_cycle_harmonics import (
            CenteredMotifPositionOrbit,
        )

        if not self.admits(repetitions):
            raise ValueError("radial leading request exceeds periodic source guard")
        return CenteredMotifPositionOrbit(
            self.source, repetitions, self.word(), 2 * len(self.motif)
        ).centered_leading_binary(repetitions, width, evaluator)

    def demanded_position_harmonics(
        self, repetitions: int, radix: int, position: int, *, walsh64: bool = False
    ) -> PositionHarmonicSpectrum:
        """Fold all motif phases; transport the same centered action per phase."""
        from number_compiler.arithmetic.fields.walsh import walsh64_mod5
        from number_compiler.sequences.collatz.position_cycle_harmonics import (
            CenteredMotifPositionOrbit,
            PositionHarmonicSpectrum,
        )

        if not self.admits(repetitions):
            raise ValueError("position demand exceeds the periodic source cylinder")
        if type(radix) is not int or not 2 <= radix <= 64:
            raise ValueError("position radix must be 2..64")
        if type(position) is not int or position < 0:
            raise ValueError("position must be nonnegative")
        if (position + 1) * radix.bit_length() > 4096:
            raise ValueError("position modulus exceeds 4096-bit budget")
        nphases = len(self.motif)
        if walsh64 and repetitions * nphases < 64:
            raise ValueError("Walsh64 needs 64 authenticated return sources")
        if repetitions <= 1:
            # At one copy, a rotated orbit would consume *future* letters
            # beyond the certified source horizon. Sample only its known
            # phase sources, and do not authorize a second motif implicitly.
            counts = [0] * radix
            current = self.source
            for j in self.motif[: repetitions * nphases]:
                counts[(current // radix**position) % radix] += 1
                upper = 3 * ((current - 3) // 10) + 1
                current = (15 * (upper >> j) + 1) >> 1
            return PositionHarmonicSpectrum(
                radix=radix,
                position=position,
                repetitions=repetitions * nphases,
                counts=tuple(counts),
                forced_position_interval=None,
                forced_position_digit=None,
                two_adic_forced_through=None,
                ternary_forced_from=None,
                odd_preperiod=None,
                odd_period=None,
                evaluated_cells=repetitions * nphases,
                radial_scale=self.scale(repetitions),
                walsh64_change_mod5=None,
            )
        action = self.word()
        prefix = self.source
        orbits: list[CenteredMotifPositionOrbit] = []
        for phase in range(nphases):
            # Phase s advances through a *rotated* motif, a conjugate of A.
            rotated = self.motif[phase:] + self.motif[:phase]
            ring = PeriodicTail6305Ring.from_source(prefix, rotated)
            # A nonzero phase needs only r-1 complete rotated blocks to
            # sample r sources. Demanding r blocks would authorize a future
            # border beyond the root cylinder, a false guard escalation.
            owned = repetitions if phase == 0 else max(0, repetitions - 1)
            orbits.append(
                CenteredMotifPositionOrbit(prefix, owned, ring.word(), 2 * nphases)
            )
            j = self.motif[phase]
            upper = 3 * ((prefix - 3) // 10) + 1
            prefix = (15 * (upper >> j) + 1) >> 1
        if prefix != action.endpoint(self.source):
            raise AssertionError("periodic harmonic motif lost its full endpoint")
        counts = [0] * radix
        evaluated = 0
        for orbit in orbits:
            spectrum = orbit.spectrum(radix, position)
            evaluated += spectrum.evaluated_cells
            for digit, count in enumerate(spectrum.counts):
                counts[digit] += count
            if orbit.repetitions < repetitions:
                counts[orbit.digit(repetitions - 1, radix, position)] += 1
                evaluated += 1
        mask = 0
        if walsh64:

            def sampled_digit(index: int) -> int:
                return orbits[index % nphases].digit(index // nphases, radix, position)

            for tick in range(64):
                if sampled_digit(tick) != sampled_digit(tick + 1):
                    mask |= 1 << tick
        return PositionHarmonicSpectrum(
            radix=radix,
            position=position,
            repetitions=repetitions * nphases,
            counts=tuple(counts),
            forced_position_interval=None,
            forced_position_digit=None,
            two_adic_forced_through=None,
            ternary_forced_from=None,
            odd_preperiod=None,
            odd_period=None,
            evaluated_cells=evaluated,
            radial_scale=self.scale(repetitions),
            walsh64_change_mod5=walsh64_mod5(mask) if walsh64 else None,
        )


__all__ = [
    "ConstantTail6305Ring",
    "PeriodicTail6305Ring",
    "ZeroTailFreeBorderRing",
    "periodic_return_capacity",
    "zero_tail_word_coefficients",
]

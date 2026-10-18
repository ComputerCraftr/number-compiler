"""Random access to an ordered physical-tripling carry word.

The source is 3**phase modulo the demanded radix window. A source period
permits temporal repetition; carry histograms alone never permit it. No full
integer source, period table, recursive lower-layer cache or trajectory is built.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass, field

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.three_power_radix import (
    ThreePowerClock,
    order_three,
)


@dataclass(frozen=True, slots=True)
class TriplingCarrySample:
    digit: int
    incoming: int
    outgoing: int
    successor_digit: int


@dataclass(frozen=True, slots=True)
class OrderedTriplingCarry:
    """Exact source slice, with a certified *source* period, not a minimal word ID."""

    base: int
    position: int
    phase: int
    duration: int
    _input_clock: InitVar[ThreePowerClock] = ThreePowerClock.ORDINARY
    boundary: int = field(init=False)
    modulus: int = field(init=False)
    period: int = field(init=False)
    source: int = field(init=False)

    def __post_init__(self, _input_clock: ThreePowerClock) -> None:
        if type(self.base) is not int or self.base not in (2, 5, 7, 10, 11):
            raise ValueError("ordered tripling radix must be 2,5,7,10 or 11")
        require_integer(self.position, "carry position", 0, 63)
        require_integer(self.phase, "physical phase", 0)
        require_integer(self.duration, "physical duration", 0)
        if type(_input_clock) is not ThreePowerClock:
            raise TypeError("carry source clock must be ThreePowerClock")
        if _input_clock is ThreePowerClock.DYADIC:
            require_integer(self.phase, "dyadic level", 0, 65_535)
        boundary = self.base**self.position
        period = order_three(self.base, self.position + 1)
        assert period is not None
        object.__setattr__(self, "boundary", boundary)
        object.__setattr__(self, "modulus", boundary * self.base)
        object.__setattr__(self, "period", period)
        phase = (
            pow(2, self.phase, period)
            if _input_clock is ThreePowerClock.DYADIC
            else self.phase % period
        )
        object.__setattr__(self, "phase", phase)
        object.__setattr__(self, "source", pow(3, self.phase, self.modulus))

    @classmethod
    def at_dyadic_phase(
        cls, base: int, position: int, level: int, duration: int
    ) -> OrderedTriplingCarry:
        """Select 3**(2**level) without allocating 2**level or 3**(2**level)."""
        return cls(base, position, level, duration, ThreePowerClock.DYADIC)

    def _residue(self, offset: int) -> int:
        return self.source * pow(3, offset % self.period, self.modulus) % self.modulus

    def sample(self, offset: int) -> TriplingCarrySample:
        require_integer(offset, "carry offset", 0, self.duration - 1)
        residue = self._residue(offset)
        digit, lower = divmod(residue, self.boundary)
        incoming = 3 * lower // self.boundary
        outgoing, successor = divmod(3 * digit + incoming, self.base)
        return TriplingCarrySample(digit, incoming, outgoing, successor)

    def conditional_sample(
        self, initial_digit: int, offset: int
    ) -> TriplingCarrySample:
        """Keep the exact lower source, transporting a hypothetical initial digit."""
        require_integer(initial_digit, "initial digit", 0, self.base - 1)
        actual = self.sample(offset)
        delta = initial_digit - self.source // self.boundary
        digit = (
            actual.digit + pow(3, offset % self.period, self.base) * delta
        ) % self.base
        outgoing, successor = divmod(3 * digit + actual.incoming, self.base)
        return TriplingCarrySample(digit, actual.incoming, outgoing, successor)

    def split(self, offset: int) -> tuple[OrderedTriplingCarry, OrderedTriplingCarry]:
        require_integer(offset, "carry split", 0, self.duration)
        return (
            OrderedTriplingCarry(self.base, self.position, self.phase, offset),
            OrderedTriplingCarry(
                self.base, self.position, self.phase + offset, self.duration - offset
            ),
        )

    @property
    def cycle_decomposition(self) -> tuple[int, int]:
        """Complete source-period repeats and the ordered suffix length."""
        return divmod(self.duration, self.period)

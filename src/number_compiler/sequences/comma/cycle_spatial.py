"""Arithmetic Q19 observer for the punctured decimal port cycle.

Only the physical period and the next-zero observations are quotiented here.
Exact dwell, displacement and decade continuation belong to the occurrence;
this observer cannot replace their admission or discover a B1 successor.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd

from .arithmetic import comma_port_previous


@dataclass(frozen=True, slots=True)
class CycleSpatialState:
    """One of 19 states: ten period-10, six period-5, three period-2."""

    period: int
    phase: int | None

    def __post_init__(self) -> None:
        if type(self.period) is not int or self.period not in (2, 5, 10):
            raise ValueError("invalid Q19 physical period")
        if self.phase is None:
            if self.period == 10:
                raise ValueError("a Q19 period-10 orbit cannot omit zero")
        elif type(self.phase) is not int or not 0 <= self.phase < self.period:
            raise ValueError("invalid Q19 cyclic phase")

    @classmethod
    def from_port(cls, leading: int, digit: int) -> CycleSpatialState:
        """Classify one source with bounded arithmetic, without a port table."""
        comma_port_previous(leading, digit)  # Shared exact port validation.
        divisor = gcd(leading, 10)
        period = 10 // divisor
        phase = (
            None
            if digit % divisor
            else (digit // divisor * pow(leading // divisor, -1, period)) % period
        )
        return cls(period, phase)

    @property
    def observation(self) -> tuple[bool, int]:
        """Physical zero at the next subtraction, and physical cycle length."""
        return self.phase == 1, self.period

    def advance(self, steps: int) -> CycleSpatialState:
        """Power punctured port moves; operand work depends on steps.bit_length()."""
        if type(steps) is not int or steps < 0:
            raise ValueError("Q19 duration must be a nonnegative integer")
        if steps == 0 or self.phase is None:
            return self
        # Zero is a transient source, never a punctured successor. Its first
        # move enters phase period-1; nonzero phases cycle with period-1.
        origin = self.phase - 1 if self.phase else 0
        return CycleSpatialState(self.period, 1 + (origin - steps) % (self.period - 1))

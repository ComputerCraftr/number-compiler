"""Composable Collatz-owned helix and quadratic innovation clock.

For an authenticated normalized parity program w, its innovation polynomial is
P_w(3,z) = sum_j 3**(o-1-j) z**p_j, where p_j are odd-bit positions.
The transfer P_AB = 3**o(B)*P_A + z**len(A)*P_B gives the exact
value, first and second logarithmic derivatives at z=2.  These are finite
observer ports; they cannot authorize an arbitrary successor without its
source-cylinder guard. Physical time is tracked separately from normalized
positions (one odd normalized action consumes two physical ticks).
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.fields.homogeneous_growth import (
    GrowthArithmeticEvaluator,
    HomogeneousGrowthScale,
)
from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.arithmetic.fields.radial_sturmian import (
    RadialSturmianClock,
    RadialSturmianPacket,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)


@dataclass(frozen=True, slots=True)
class SkewQuadraticClock:
    precision: int
    steps: int
    odds: int
    value: int
    linear: int
    quadratic: int
    position_sum: int
    first_odd: int | None
    last_odd: int | None

    def __post_init__(self) -> None:
        values = (
            self.precision,
            self.steps,
            self.odds,
            self.value,
            self.linear,
            self.quadratic,
            self.position_sum,
        )
        if any(type(value) is not int for value in values):
            raise TypeError("skew clock fields require exact integers")
        if (
            not 3 <= self.precision <= 4096
            or self.steps < 0
            or not 0 <= self.odds <= self.steps
            or min(self.value, self.linear, self.quadratic, self.position_sum) < 0
            or any(
                value >= 1 << self.precision
                for value in (self.value, self.linear, self.quadratic)
            )
            or (self.odds == 0) != (self.first_odd is None)
            or (self.odds == 0) != (self.last_odd is None)
            or (
                self.first_odd is not None
                and (
                    type(self.first_odd) is not int
                    or not 0 <= self.first_odd < self.steps
                )
            )
            or (
                self.last_odd is not None
                and (
                    type(self.last_odd) is not int
                    or not 0 <= self.last_odd < self.steps
                )
            )
            or (
                self.first_odd is not None
                and self.last_odd is not None
                and self.first_odd > self.last_odd
            )
        ):
            raise ValueError("invalid Collatz quadratic clock")

    @classmethod
    def identity(cls, precision: int = 32) -> SkewQuadraticClock:
        if type(precision) is not int or not 3 <= precision <= 4096:
            raise ValueError("invalid Collatz helix precision")
        return cls(precision, 0, 0, 0, 0, 0, 0, None, None)

    @classmethod
    def atom(cls, bit: int, precision: int = 32) -> SkewQuadraticClock:
        if type(bit) is not int or bit not in (0, 1):
            raise ValueError("normalized parity must be 0 or 1")
        if type(precision) is not int or not 3 <= precision <= 4096:
            raise ValueError("invalid Collatz helix precision")
        return cls(
            precision, 1, bit, bit, 0, 0, 0, 0 if bit else None, 0 if bit else None
        )

    def then(self, other: SkewQuadraticClock) -> SkewQuadraticClock:
        if type(other) is not SkewQuadraticClock or self.precision != other.precision:
            raise ValueError("skew clocks require a matching precision")
        mask = (1 << self.precision) - 1
        shift = pow(2, self.steps, mask + 1)
        gain = pow(3, other.odds, mask + 1)
        return SkewQuadraticClock(
            self.precision,
            self.steps + other.steps,
            self.odds + other.odds,
            (gain * self.value + shift * other.value) & mask,
            (gain * self.linear + shift * (other.linear + self.steps * other.value))
            & mask,
            (
                gain * self.quadratic
                + shift
                * (
                    other.quadratic
                    + 2 * self.steps * other.linear
                    + self.steps * self.steps * other.value
                )
            )
            & mask,
            self.position_sum + other.position_sum + self.steps * other.odds,
            self.first_odd
            if self.first_odd is not None
            else (
                self.steps + other.first_odd if other.first_odd is not None else None
            ),
            (
                self.steps + other.last_odd
                if other.last_odd is not None
                else self.last_odd
            ),
        )

    def power(self, count: int) -> SkewQuadraticClock:
        if type(count) is not int or count < 0:
            raise ValueError("skew clock power must be nonnegative")
        powered = binary_power(
            self,
            count,
            identity=self.identity(self.precision),
            compose=lambda first, second: first.then(second),
        )
        return powered.value

    @classmethod
    def factors(
        cls,
        factors: tuple[tuple[tuple[int, ...], int], ...],
        precision: int = 32,
    ) -> SkewQuadraticClock:
        """Fold a compact grammar; motif repetition never expands into leaves."""
        if type(factors) is not tuple:
            raise TypeError("skew factors must be an immutable tuple")
        result = cls.identity(precision)
        for motif, count in factors:
            result = result.then(_powered_skew_factor(motif, count, precision))
        return result

    @property
    def radial_sturmian_clock(self) -> RadialSturmianClock:
        """Clock of 3**odds / 2**steps, from this same pumped factor grammar."""
        return RadialSturmianClock(HomogeneousGrowthScale(self.odds, self.steps))

    def radial_leading_binary(
        self, evaluator: GrowthArithmeticEvaluator, width: int = 8
    ) -> RadialSturmianPacket:
        return self.radial_sturmian_clock.leading_binary(evaluator, width)

    @property
    def physical_ticks(self) -> int:
        return self.steps + self.odds

    @property
    def return_clock(self) -> int:
        return (
            self.position_sum - self.odds * self.first_odd
            if self.first_odd is not None
            else 0
        )

    @property
    def ray_prefix(self) -> int:
        modulus = 1 << self.precision
        return -pow(3, -self.odds, modulus) * self.value % modulus

    def verify(
        self,
        action: DyadicTerminalFieldAction,
        source: int,
        endpoint: int,
    ) -> None:
        """Bind the skew ports to the *same* source-guarded affine action."""
        modulus = 1 << self.precision
        if (
            type(action) is not DyadicTerminalFieldAction
            or not action.producer_issued
            or action.steps != self.steps
            or action.gain != 3**self.odds
            or action.offset % modulus != self.value
            or not action.certifies(source)
            or action.endpoint(source) != endpoint
            or (source - self.ray_prefix) % modulus
            != pow(2, self.steps, modulus)
            * pow(3, -self.odds, modulus)
            * endpoint
            % modulus
        ):
            raise ValueError("skew-cylinder ports disagree with the certified action")


def _powered_skew_factor(
    motif: tuple[int, ...],
    count: int,
    precision: int,
) -> SkewQuadraticClock:
    """Build a powered source-free factor under the active query workspace."""
    if (
        type(motif) is not tuple
        or not motif
        or any(type(bit) is not int or bit not in (0, 1) for bit in motif)
        or type(count) is not int
        or count < 1
    ):
        raise ValueError("skew clock factor requires a nonempty powered motif")
    word = SkewQuadraticClock.identity(precision)
    for bit in motif:
        word = word.then(SkewQuadraticClock.atom(bit, precision))
    return word.power(count)


__all__ = ["SkewQuadraticClock"]

"""Finite source-independent fractional branch actions and exact guards."""

from bisect import bisect_right
from dataclasses import dataclass
from fractions import Fraction
from functools import cache

BRANCH_BLOCK_TICKS = 8
BRANCH_BLOCK_GAIN = 3**BRANCH_BLOCK_TICKS
BRANCH_BLOCK_MODULUS = 2**BRANCH_BLOCK_TICKS
BRANCH_CHART_SCRATCH_BITS = 128 * 1024


@cache
def branch_chart() -> tuple[tuple[int, ...], tuple[tuple[int, int, int], ...]]:
    """Compile complete eight-tick actions and their exact input intervals."""
    actions = [(0, 0, 1)]
    modulus = 1
    for _ in range(BRANCH_BLOCK_TICKS):
        following: list[tuple[int, int, int]] = []
        for innovation, lower, upper in actions:
            for bit in (0, 1):
                next_innovation = 3 * innovation + bit * modulus
                next_lower = max(3 * lower, next_innovation)
                next_upper = min(3 * upper, 2 * next_innovation + 2 * modulus)
                if 2 * next_lower < next_upper:
                    following.append((next_innovation, next_lower, next_upper))
        actions = following
        modulus *= 2
    actions.sort(key=lambda action: action[1])
    return tuple(2 * action[1] for action in actions), tuple(actions)


@dataclass(slots=True)
class FractionalPath:
    """Finite CF projection with the complete fractional guard.

    At extent t the map is (gain*x - innovation)/modulus, with
    gain = 3**t and modulus = 2**t. The guard is half-open, using
    numerators lower and upper over gain and 2*gain respectively.
    """

    extent: int = 0
    gain: int = 1
    modulus: int = 1
    innovation: int = 0
    lower: int = 0
    upper: int = 1
    chart: tuple[tuple[int, ...], tuple[tuple[int, int, int], ...]] | None = None

    def endpoint(self, source: Fraction) -> tuple[int, int]:
        return (
            self.gain * source.numerator - self.innovation * source.denominator,
            self.modulus * source.denominator,
        )

    def extend(self, low: Fraction, high: Fraction, horizon: int) -> None:
        left_n, left_d = self.endpoint(low)
        right_n, right_d = self.endpoint(high)
        while self.extent < horizon and left_n >= 0 and 2 * right_n <= right_d:
            remaining = horizon - self.extent
            if self.chart is not None and remaining >= BRANCH_BLOCK_TICKS:
                keys, actions = self.chart
                position = (
                    bisect_right(keys, 2 * BRANCH_BLOCK_GAIN * left_n // left_d) - 1
                )
                if position >= 0:
                    innovation, lower, upper = actions[position]
                    if (
                        BRANCH_BLOCK_GAIN * left_n >= lower * left_d
                        and 2 * BRANCH_BLOCK_GAIN * right_n <= upper * right_d
                    ):
                        gain = BRANCH_BLOCK_GAIN
                        modulus = BRANCH_BLOCK_MODULUS
                        left_n = gain * left_n - innovation * left_d
                        right_n = gain * right_n - innovation * right_d
                        left_d *= modulus
                        right_d *= modulus
                        old_innovation = self.innovation
                        old_modulus = self.modulus
                        self.innovation = (
                            gain * old_innovation + old_modulus * innovation
                        )
                        self.gain *= gain
                        self.modulus *= modulus
                        self.extent += BRANCH_BLOCK_TICKS
                        self.lower = max(
                            gain * self.lower,
                            gain * old_innovation + old_modulus * lower,
                        )
                        self.upper = min(
                            gain * self.upper,
                            2 * gain * old_innovation + old_modulus * upper,
                        )
                        continue
            ticks = max_zero_run(right_n, right_d, remaining)
            if ticks:
                scale: int = 3**ticks
                offset = 0
            elif 3 * left_n >= left_d:
                # The admitted odd map reaches [0, 1/4), so its
                # next step is even when the request includes it.
                ticks, scale, offset = (1, 3, 1) if remaining == 1 else (2, 9, 3)
            else:
                break

            left_n = scale * left_n - offset * left_d
            right_n = scale * right_n - offset * right_d
            left_d <<= ticks
            right_d <<= ticks
            self.innovation = scale * self.innovation + self.modulus * offset
            self.gain *= scale
            self.modulus <<= ticks
            self.extent += ticks
            # The previous guard and the last endpoint imply all bounds
            # of the selected zero run or odd/zero pair.
            self.lower = max(scale * self.lower, self.innovation)
            self.upper = min(scale * self.upper, 2 * self.innovation + self.modulus)

    def contains(self, low: Fraction, high: Fraction) -> bool:
        return (
            self.lower * low.denominator <= low.numerator * self.gain
            and high.numerator * (2 * self.gain) <= self.upper * high.denominator
        )

    def residue(self) -> int:
        # Invert the base before powering the certified gain 3**extent.
        inverse_gain = pow(3, -self.extent, self.modulus)
        return (-self.innovation * inverse_gain) % self.modulus


def max_zero_run(numerator: int, denominator: int, remaining: int) -> int:
    # Cancel the common factor of two in the first two admissible
    # endpoints. Most calls finish at zero or one tick.
    if 3 * numerator > denominator:
        return 0
    if remaining == 1 or 9 * numerator > denominator << 1:
        return 1
    low, high = 2, min(4, remaining)
    while low < high and (3**high) * numerator <= denominator << (high - 1):
        low, high = high, min(2 * high, remaining)
    while low < high:
        middle = (low + high + 1) // 2
        if (3**middle) * numerator <= denominator << (middle - 1):
            low = middle
        else:
            high = middle - 1
    return low

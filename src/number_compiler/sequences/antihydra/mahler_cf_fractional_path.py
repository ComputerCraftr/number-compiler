"""Finite source-independent fractional branch actions and exact guards."""

from bisect import bisect_right
from dataclasses import dataclass
from fractions import Fraction
from functools import cache
from io import BytesIO
from struct import Struct

BRANCH_BLOCK_TICKS = 8
BRANCH_BLOCK_GAIN = 3**BRANCH_BLOCK_TICKS
BRANCH_BLOCK_MODULUS = 2**BRANCH_BLOCK_TICKS
BRANCH_CHART_SCRATCH_BITS = 96 * 1024
PACKED_CHART_SCRATCH_BITS = 128 * 1024
_PACKED_ROW = Struct("=III")
_SHORT_RECORDS = 40
_WIDE_TICKS = 16
_WIDE_GAIN = 3**_WIDE_TICKS


def _build_branch_chart(horizons: tuple[int, ...]) -> bytes:
    """Enumerate viable guards in increasing inlet order into fixed-width rows."""
    output = BytesIO()
    for horizon in horizons:
        stack = [(0, 0, 0, 1)]
        while stack:
            tick, innovation, lower, upper = stack.pop()
            if tick == horizon:
                output.write(_PACKED_ROW.pack(2 * lower, innovation, upper))
                continue
            modulus = 1 << tick
            for bit in (1, 0):
                next_innovation = 3 * innovation + bit * modulus
                next_lower = max(3 * lower, next_innovation)
                next_upper = min(3 * upper, 2 * next_innovation + 2 * modulus)
                if 2 * next_lower < next_upper:
                    stack.append((tick + 1, next_innovation, next_lower, next_upper))
    return output.getvalue()


@cache
def branch_chart() -> tuple[tuple[int, ...], bytes]:
    """Compile eight-tick actions and their exact input intervals."""
    rows = _build_branch_chart((BRANCH_BLOCK_TICKS,))
    return tuple(key for key, _, _ in _PACKED_ROW.iter_unpack(rows)), rows


@cache
def packed_branch_chart() -> bytes:
    """Build immutable ordered 8- and 16-tick guards within the chart reservation."""
    return _build_branch_chart((BRANCH_BLOCK_TICKS, _WIDE_TICKS))


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
    chart: tuple[tuple[int, ...], bytes] | None = None
    packed_chart: bytes | None = None

    def endpoint(self, source: Fraction) -> tuple[int, int]:
        return (
            self.gain * source.numerator - self.innovation * source.denominator,
            self.modulus * source.denominator,
        )

    def extend(self, low: Fraction, high: Fraction, horizon: int) -> None:
        left_n, left_d = self.endpoint(low)
        right_n, right_d = self.endpoint(high)
        packed = self.packed_chart
        packed_rows = memoryview(packed).cast("I") if packed is not None else None
        short_keys = None
        wide_keys = None
        if packed_rows is not None:
            short_keys = packed_rows[: 3 * _SHORT_RECORDS : 3]
            wide_keys = packed_rows[3 * _SHORT_RECORDS :: 3]
        while self.extent < horizon and left_n >= 0 and 2 * right_n <= right_d:
            remaining = horizon - self.extent
            match = None
            if (
                packed_rows is not None
                and short_keys is not None
                and wide_keys is not None
            ):
                for ticks, begin, gain, packed_keys in (
                    (_WIDE_TICKS, _SHORT_RECORDS, _WIDE_GAIN, wide_keys),
                    (BRANCH_BLOCK_TICKS, 0, BRANCH_BLOCK_GAIN, short_keys),
                ):
                    if remaining < ticks:
                        continue
                    selector = 2 * gain * left_n // left_d
                    position = bisect_right(packed_keys, selector) - 1
                    if position >= 0:
                        key, innovation, upper = _PACKED_ROW.unpack_from(
                            packed_rows, (begin + position) * _PACKED_ROW.size
                        )
                        if selector >= key and 2 * gain * right_n <= upper * right_d:
                            match = (ticks, gain, innovation, key // 2, upper)
                            break
            elif self.chart is not None and remaining >= BRANCH_BLOCK_TICKS:
                keys, actions = self.chart
                selector = 2 * BRANCH_BLOCK_GAIN * left_n // left_d
                position = bisect_right(keys, selector) - 1
                if position >= 0:
                    key, innovation, upper = _PACKED_ROW.unpack_from(
                        actions, position * _PACKED_ROW.size
                    )
                    lower = key // 2
                    if (
                        selector >= key
                        and 2 * BRANCH_BLOCK_GAIN * right_n <= upper * right_d
                    ):
                        match = (
                            BRANCH_BLOCK_TICKS,
                            BRANCH_BLOCK_GAIN,
                            innovation,
                            lower,
                            upper,
                        )
            if match is not None:
                ticks, gain, innovation, lower, upper = match
                modulus = 1 << ticks
                left_n = gain * left_n - innovation * left_d
                right_n = gain * right_n - innovation * right_d
                left_d *= modulus
                right_d *= modulus
                old_innovation = self.innovation
                old_modulus = self.modulus
                self.innovation = gain * old_innovation + old_modulus * innovation
                self.gain *= gain
                self.modulus *= modulus
                self.extent += ticks
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
        # The action already owns the odd gain 3**extent. Each Newton
        # multiplication squares the inverse defect and doubles precision.
        inverse = 1
        precision = 1
        while precision < self.extent:
            precision = min(2 * precision, self.extent)
            mask = (1 << precision) - 1
            inverse = (inverse * (2 - inverse * (self.gain & mask))) & mask
        return (-self.innovation * inverse) & (self.modulus - 1)


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

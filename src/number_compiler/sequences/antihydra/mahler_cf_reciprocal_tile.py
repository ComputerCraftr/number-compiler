"""Source-bound reciprocal row intervals and ordered decimal actions."""

from dataclasses import dataclass, field

from number_compiler.arithmetic.fields.ordered_matrix import (
    Matrix2,
    append_decimal_value,
)
from number_compiler.sequences.antihydra.mahler_cf_low_period import (
    SETTLED_TENS_ACTION,
    settled_low_action,
)


def reciprocal_row_interval(q: int, t: int, width: int, start: int, count: int) -> int:
    """Restrict the lifted source at its moving cut before digit decoding."""
    # The checked reciprocal split equals q * 5**t. Restrict this
    # source directly instead of reconstructing both sides of the cut.
    skip = width - start - count
    if t == 0:
        first: int = q // 10**skip % 10**count
        return first
    interval: int = (q * 5**t) // 10**skip % 10**count
    return interval


@dataclass(frozen=True, slots=True)
class ReciprocalTile:
    """One original source and a demanded row-major interval."""

    quotient: int
    widths: tuple[int, ...]
    start: int
    length: int
    first_exponent: int | None = None
    product: Matrix2 = field(init=False)

    def __post_init__(self) -> None:
        object.__setattr__(self, "product", self.segment(0, self.length))

    def segment(self, begin: int, length: int) -> Matrix2:
        if length == 0:
            return Matrix2.identity()
        start = begin + self.start
        row = 0
        while start >= self.widths[row]:
            start -= self.widths[row]
            row += 1
        entries = (1, 0, 0, 1)
        remaining = length
        while row < len(self.widths):
            width = self.widths[row]
            count = min(remaining, width - start)
            exponent = (
                None if self.first_exponent is None else self.first_exponent + row
            )
            # Only an interval ending at the physical low edge admits the
            # settled suffix action directly; a moving cut uses the exact path.
            suffix_count = (
                min(4, count, width, exponent)
                if exponent is not None and start + count == width
                else 0
            )
            action = (
                settled_low_action(exponent, suffix_count)
                if exponent is not None and suffix_count
                else None
            )
            if (
                exponent is not None
                and exponent >= 2
                and width >= 2
                and start + count == width - 1
            ):
                # A clipped prefix ending on the settled tens digit of 25.
                suffix_count = 1
                action = SETTLED_TENS_ACTION
            prefix_count = count - suffix_count
            if prefix_count:
                value = reciprocal_row_interval(
                    self.quotient, row, width, start, prefix_count
                )
                entries = append_decimal_value(value, 10 ** (prefix_count - 1), entries)
            if action is not None:
                e, f, g, h = action
                a, b, c, d = entries
                entries = (a * e + b * g, a * f + b * h, c * e + d * g, c * f + d * h)
            remaining -= count
            if remaining == 0:
                return Matrix2(entries)
            start = 0
            row += 1
        raise ArithmeticError("ordered segment exceeded the authenticated tile")

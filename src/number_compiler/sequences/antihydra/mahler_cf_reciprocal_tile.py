"""Source-bound reciprocal row intervals and ordered decimal actions."""

import os
from dataclasses import dataclass, field
from functools import cache
from importlib import import_module
from typing import Protocol, cast

from number_compiler.arithmetic.fields.ordered_matrix import (
    Matrix2,
    MatrixEntries,
    append_decimal_value,
    multiply_entries,
)
from number_compiler.sequences.antihydra.mahler_cf_low_period import (
    SETTLED_TENS_ACTION,
    settled_low_action,
)


class _NativeContinuant(Protocol):
    def ordered_product(self, value: int, width: int) -> tuple[int, int, int, int]: ...


@cache
def _native_continuant() -> _NativeContinuant | None:
    try:
        return cast(
            _NativeContinuant, import_module("number_compiler.kernels._cf_continuant")
        )
    except ModuleNotFoundError as error:
        if error.name != "number_compiler.kernels._cf_continuant":
            raise
        return None


def reciprocal_row_interval(q: int, t: int, width: int, start: int, count: int) -> int:
    """Restrict the lifted source at its moving cut before digit decoding."""
    skip = width - start - count
    if skip >= t:
        # Cancel 5**t against the discarded decimal places before multiplying.
        # The binary cut keeps the carry into the requested upper band.
        upper: int = (q >> t) // 10 ** (skip - t)
    else:
        upper = (q * 5 ** (t - skip)) >> skip
    modulus: int = 10**count
    return upper % modulus


@dataclass(frozen=True, slots=True)
class ReciprocalTile:
    """One original source and a demanded row-major interval."""

    quotient: int
    widths: tuple[int, ...]
    start: int
    length: int
    first_exponent: int | None = None
    product: Matrix2 = field(init=False)
    # This bounded response belongs to the issued tile, never to a shared
    # semantic key. The owner's staging reservation covers its integer limbs.
    first_row_prefix: tuple[int, MatrixEntries] | None = field(init=False)
    _building: bool = field(init=False, default=True, repr=False)

    def __post_init__(self) -> None:
        object.__setattr__(self, "first_row_prefix", None)
        object.__setattr__(self, "_building", len(self.widths) == 2)
        object.__setattr__(self, "product", self.segment(0, self.length))
        object.__setattr__(self, "_building", False)

    @property
    def sealed(self) -> bool:
        return not self._building

    def segment(self, begin: int, length: int) -> Matrix2:
        if length == 0:
            return Matrix2.identity()
        if not self._building and begin == 0:
            prefix = self.first_row_prefix
            if prefix is not None and prefix[0] == length:
                return Matrix2(prefix[1])
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
                min(6, count, width, exponent)
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
                native = (
                    _native_continuant()
                    if 4 <= prefix_count <= 32
                    and os.environ.get("NUMBER_COMPILER_ENABLE_CF_CONTINUANT") == "1"
                    else None
                )
                if native is not None and prefix_count > 16:
                    # Split at an exact decimal place and append the first
                    # complete source-free ordered word before its remainder.
                    head, value = divmod(value, 10 ** (prefix_count - 16))
                    head_action = native.ordered_product(head, 16)
                    if entries == (1, 0, 0, 1):
                        entries = head_action
                    else:
                        entries = multiply_entries(entries, head_action)
                    prefix_count -= 16
                if native is None or prefix_count < 4:
                    entries = append_decimal_value(
                        value, 10 ** (prefix_count - 1), entries
                    )
                else:
                    entries = multiply_entries(
                        entries, native.ordered_product(value, prefix_count)
                    )
            if action is not None:
                entries = multiply_entries(entries, action)
            remaining -= count
            if self._building and row == 0 and start + count == width:
                object.__setattr__(self, "first_row_prefix", (count, entries))
            if remaining == 0:
                return Matrix2(entries)
            start = 0
            row += 1
        raise ArithmeticError("ordered segment exceeded the authenticated tile")

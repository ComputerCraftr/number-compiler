"""Exact two-generation 5rev10 executor on four-bit decimal digit lanes.

All physical rows are represented as LSD-first BCD integers.  No digit
reversal or base conversion occurs inside the two-generation loop.  The
intermediate one-step result is checked using the reversal of its padded
digit action, *without* constructing that reverse word.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.fields.two_adic import v2_positive

_CHUNK = 250  # valid even with Python's smallest permitted decimal limit


def _digits(packed: int) -> int:
    return max(1, (packed.bit_length() + 3) // 4)


def _strip_zero_nibbles(packed: int) -> int:
    if packed:
        packed >>= 4 * (v2_positive(packed) // 4)
    return packed


def decimal_to_packed(value: int) -> int:
    """Decimal integer -> BCD; chunk when Python's decimal limit is active."""
    try:
        return int(str(value), 16)
    except ValueError:
        if not value:
            return 0
        base = 10**_CHUNK
        result = 0
        offset = 0
        while value:
            value, remainder = divmod(value, base)
            result |= int(f"{remainder:0{_CHUNK}d}", 16) << (4 * offset)
            offset += _CHUNK
        return result


def packed_to_decimal(packed: int) -> int:
    """BCD -> decimal integer, without modifying the interpreter's limit."""
    digits = format(packed, "x")
    try:
        return int(digits, 10)
    except ValueError:
        value = 0
        for offset in range(0, len(digits), _CHUNK):
            segment = digits[offset : offset + _CHUNK]
            value = value * 10 ** len(segment) + int(segment, 10)
        return value


class ExactBitBudget:
    __slots__ = (
        "bits",
        "safe_width",
        "impossible_width",
        "_limit_digits",
        "_limit_bcd",
    )

    def __init__(self, bits: int) -> None:
        self.bits = bits
        # 10**3 < 2**10 and 2**3 < 10 give conservative integral bounds.
        # Widths between them use an exact comparison to the bit limit.
        self.safe_width = 3 * (bits // 10)
        self.impossible_width = bits // 3 + 2
        self._limit_digits: str | None = None
        self._limit_bcd: int | None = None

    def limit(self) -> str:
        if self._limit_digits is None:
            value = (1 << self.bits) - 1
            # The source/endpoint conversions must also honor Python's
            # decimal-digit limit without modifying interpreter globals.
            try:
                self._limit_digits = str(value)
            except ValueError:
                base = 10**_CHUNK
                pieces: list[str] = []
                while value:
                    value, remainder = divmod(value, base)
                    pieces.append(f"{remainder:0{_CHUNK}d}")
                if not pieces:
                    self._limit_digits = "0"
                else:
                    pieces[-1] = str(int(pieces[-1]))
                    self._limit_digits = "".join(reversed(pieces))
        return self._limit_digits

    def check_width(self, width: int) -> bool:
        if width <= self.safe_width:
            return False
        if width >= self.impossible_width:
            raise BlockContextBudgetExceeded(
                "five-reversal next state exceeds its admitted bit budget"
            )
        return True

    def check_even(self, packed: int) -> None:
        if not self.check_width(_digits(packed)):
            return
        if self._limit_bcd is None:
            self._limit_bcd = int(self.limit(), 16)
        if packed > self._limit_bcd:
            raise BlockContextBudgetExceeded(
                "five-reversal next state exceeds its admitted bit budget"
            )

    def check_odd(self, conjugated: int, physical_width: int) -> None:
        if not self.check_width(physical_width):
            return
        bound = self.limit()
        if physical_width != len(bound):
            if physical_width > len(bound):
                raise BlockContextBudgetExceeded(
                    "five-reversal next state exceeds its admitted bit budget"
                )
            return
        # The LSD-first conjugated digits are the *MSD-first* physical
        # digits, possibly followed by zeros in the physical word.  Compare
        # their ordered digits without reversing or expanding a physical row.
        digits = conjugated
        for bound_digit in bound:
            digit = digits & 15
            if digit != ord(bound_digit) - 48:
                if digit > ord(bound_digit) - 48:
                    raise BlockContextBudgetExceeded(
                        "five-reversal next state exceeds its admitted bit budget"
                    )
                return
            digits >>= 4


def _lane_masks(capacity: int) -> tuple[int, int]:
    ones = ((1 << (4 * capacity)) - 1) // 15
    return ones, 14 * ones


def _conjugated_five(packed: int, ones: int, evens: int) -> int:
    """Padded rev(5*rev(x)): q5(d_i)+r5(d_(i-1)) per BCD lane."""
    return ((packed & evens) >> 1) + 80 * (packed & ones)


def _multiply_five(packed: int, ones: int, evens: int) -> int:
    """Decimal 5*x in BCD: r5(d_i)+q5(d_(i-1)), carry independent."""
    return 5 * (packed & ones) + 8 * (packed & evens)


@dataclass(slots=True)
class PackedFiveWork:
    """Mutable local work ledger; charged by the source owner on all exits."""

    attempted: int = 0
    digit_reads: int = 0
    executed_pairs: int = 0
    bitplane_pairs: int = 0


def validate_packed_five_input(
    seed: int, steps: int, max_state_bits: int, work: PackedFiveWork
) -> None:
    """Authenticate the common physical input and its local work owner."""
    if type(seed) is not int or seed < 0:
        raise ValueError("packed five-reversal needs a nonnegative seed")
    if type(steps) is not int or steps < 0:
        raise ValueError("packed five-reversal needs nonnegative steps")
    if type(max_state_bits) is not int or max_state_bits < 1:
        raise ValueError("packed five-reversal needs a positive bit budget")
    if type(work) is not PackedFiveWork:
        raise TypeError("packed five-reversal requires its local work ledger")
    if seed.bit_length() > max_state_bits:
        raise BlockContextBudgetExceeded("five-reversal input exceeds bit budget")


def execute_packed_five(
    seed: int,
    steps: int,
    max_state_bits: int,
    work: PackedFiveWork,
    *,
    reserve_capacity: Callable[[int], None] | None = None,
) -> int:
    """Run exact physical pairs with state checks before each publication.

    The source owner charges attempted work and completed digit reads even
    when a later state-bit check fails. No history of decimal words is kept.
    """
    validate_packed_five_input(seed, steps, max_state_bits, work)
    if steps == 0:
        return seed

    # Reserve enough capacity for the initial BCD word *before* conversion.
    # Subsequent growth reserves additional scratch before mask allocation.
    capacity = max(8, (seed.bit_length() + 2) // 3 + 5)
    if reserve_capacity is not None:
        reserve_capacity(capacity)
    packed = decimal_to_packed(seed)
    budget = ExactBitBudget(max_state_bits)
    ones, evens = _lane_masks(capacity)

    def ensure_capacity(width: int) -> None:
        nonlocal capacity, ones, evens
        if width + 3 >= capacity:
            capacity = max(capacity * 2, width + 4)
            if reserve_capacity is not None:
                reserve_capacity(capacity)
            ones, evens = _lane_masks(capacity)

    for _ in range(steps // 2):
        width = _digits(packed)
        ensure_capacity(width)
        conjugated = _strip_zero_nibbles(_conjugated_five(packed, ones, evens))
        nonzero_source = _strip_zero_nibbles(packed)
        first_width = (
            _digits(nonzero_source) + (nonzero_source & 15 >= 2)
            if nonzero_source
            else 1
        )
        work.attempted += 1
        budget.check_odd(conjugated, first_width)
        work.digit_reads += width
        work.attempted += 1
        packed = _multiply_five(conjugated, ones, evens)
        work.executed_pairs += 1
        budget.check_even(packed)
        work.digit_reads += first_width
    if steps % 2:
        width = _digits(packed)
        ensure_capacity(width)
        # The only reversal in the entire program is the optional final
        # one-generation step.  No intermediate power is materialized.
        reflected = int(format(packed, "x")[::-1], 16)
        work.attempted += 1
        packed = _multiply_five(reflected, ones, evens)
        budget.check_even(packed)
        work.digit_reads += width
    return packed_to_decimal(packed)

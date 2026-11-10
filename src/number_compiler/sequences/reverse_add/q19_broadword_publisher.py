"""Exact source-derived Q19 broadword publisher for growing reverse/add.

A complete reverse/add successor depends on each symmetric pair sum, not on
which source digit contributed it. The sums are stored in six-bit lanes, and
the two directed carry sweeps use packed prefix operations. Physical decimal
digits are reconstructed only for the demanded endpoint.

This is an exact successor-closed spatial quotient. Its temporal loop remains
linear in the requested generation; it does not assert a future period.
"""

from __future__ import annotations

from collections.abc import Callable, Sequence
from dataclasses import dataclass


def _lane_masks(count: int) -> tuple[int, int]:
    if type(count) is not int or count < 1:
        raise ValueError("carry lanes must be nonempty")
    ones = ((1 << (6 * count)) - 1) // 63
    return ones, (1 << (6 * count)) - 1


def _prefix_carries(
    forced: int,
    propagate: int,
    count: int,
    *,
    reversed_order: bool = False,
) -> int:
    """Compute all Boolean carry outputs by parallel prefix doubling."""
    result = forced
    live = propagate
    displacement = 6
    while displacement < 6 * count:
        if reversed_order:
            result |= live & (result >> displacement)
            live &= live >> displacement
        else:
            result |= live & (result << displacement)
            live &= live << displacement
        displacement <<= 1
    return result


@dataclass(frozen=True, slots=True, init=False)
class PackedQ19:
    """Pair sums and optional center for one physical decimal source."""

    pairs: int
    count: int
    center: int | None

    def __init__(self, pairs: int, count: int, center: int | None) -> None:
        self._validate_shape(pairs, count, center)
        if count:
            ones, _lane_mask = _lane_masks(count)
            high_bits = ones << 5
            # First reject lanes >= 32. With that established, adding 13 to
            # every six-bit lane sets bit 5 exactly for values 19 through 31.
            if pairs & high_bits or (pairs + 13 * ones) & high_bits:
                raise ValueError("invalid packed Q19 pair lane")
        object.__setattr__(self, "pairs", pairs)
        object.__setattr__(self, "count", count)
        object.__setattr__(self, "center", center)

    @staticmethod
    def _validate_shape(pairs: int, count: int, center: int | None) -> None:
        if (
            type(pairs) is not int
            or type(count) is not int
            or pairs < 0
            or count < 0
            or pairs.bit_length() > 6 * count
        ):
            raise ValueError("invalid packed Q19 pair extent")
        if center is not None and (type(center) is not int or not 0 <= center <= 9):
            raise ValueError("invalid packed Q19 center digit")
        if count == 0 and center is None:
            raise ValueError("packed Q19 state must contain a digit")
        # Lane zero is the outermost reflected pair (the units and leading
        # digits). Its sum must be positive for a canonical positive-width
        # decimal source; inner pair lanes may validly be zero.
        if count > 0 and (pairs & 63) == 0:
            raise ValueError("packed Q19 state has a zero leading pair")

    @classmethod
    def _from_trusted(cls, pairs: int, count: int, center: int | None) -> PackedQ19:
        """Build a successor whose lanes were produced by checked arithmetic."""
        cls._validate_shape(pairs, count, center)
        result = object.__new__(cls)
        object.__setattr__(result, "pairs", pairs)
        object.__setattr__(result, "count", count)
        object.__setattr__(result, "center", center)
        return result

    @classmethod
    def from_digits(cls, digits_lsd: Sequence[int]) -> PackedQ19:
        width = len(digits_lsd)
        if width < 1 or any(
            type(digit) is not int or not 0 <= digit <= 9 for digit in digits_lsd
        ):
            raise ValueError("Q19 source requires canonical decimal digits")
        if width > 1 and digits_lsd[-1] == 0:
            raise ValueError("Q19 source has a leading zero")
        count = width // 2
        pairs = sum(
            (digits_lsd[index] + digits_lsd[width - 1 - index]) << (6 * index)
            for index in range(count)
        )
        center = digits_lsd[count] if width & 1 else None
        return cls(pairs, count, center)

    @property
    def width(self) -> int:
        return 2 * self.count + int(self.center is not None)

    def advance(
        self, *, emit_digits: bool = False
    ) -> tuple[PackedQ19, tuple[int, ...] | None]:
        """Apply one exact width-skewed successor and optionally emit digits.

        The carries travel in opposite directions and meet at the center.
        When the most-significant carry creates a new digit, the symmetric
        pairing shifts by one cell and the target is rebuilt with that birth.
        """
        if type(emit_digits) is not bool:
            raise TypeError("Q19 physical endpoint selection must be Boolean")
        ones, lane_mask = _lane_masks(self.count) if self.count else (0, 0)
        return self._advance_with_masks(ones, lane_mask, emit_digits=emit_digits)

    def advance_repeated(
        self,
        steps: int,
        *,
        before_step: Callable[[int, int], None] | None = None,
    ) -> PackedQ19:
        """Apply a bounded sequence while reusing masks at each pair width.

        The callback receives the current lane count and prefix-round count
        immediately before each physical transition. It supports honest
        caller-owned work accounting without exposing unchecked packed masks.
        """
        if type(steps) is not int or steps < 0:
            raise ValueError("Q19 repeated transition count must be nonnegative")
        if before_step is not None and not callable(before_step):
            raise TypeError("Q19 work observer must be callable")

        frame = self
        ones, lane_mask = _lane_masks(frame.count) if frame.count else (0, 0)
        for _ in range(steps):
            rounds = (frame.count - 1).bit_length() if frame.count else 0
            if before_step is not None:
                before_step(frame.count, rounds)
            previous_count = frame.count
            frame, _digits = frame._advance_with_masks(ones, lane_mask)
            if frame.count != previous_count:
                ones, lane_mask = _lane_masks(frame.count) if frame.count else (0, 0)
        return frame

    def _advance_with_masks(
        self,
        ones: int,
        lane_mask: int,
        *,
        emit_digits: bool = False,
    ) -> tuple[PackedQ19, tuple[int, ...] | None]:
        """Advance with request-local masks for the current pair width."""
        count = self.count
        center = self.center
        if count == 0:
            if center is None:
                raise AssertionError("an empty Q19 frame has no digit")
            total = 2 * center
            growth, digit = divmod(total, 10)
            target = (
                PackedQ19._from_trusted(digit + 1, 1, None)
                if growth
                else PackedQ19._from_trusted(0, 0, digit)
            )
            emitted = (digit, 1) if growth else (digit,)
            return target, emitted if emit_digits else None

        source = self.pairs
        # Since s<=18, the bit-5 threshold comparison cannot spill lanes.
        threshold_bit = ones << 5
        forced = ((source + 22 * ones) & threshold_bit) >> 5
        propagate = (((source + 23 * ones) & threshold_bit) >> 5) ^ forced

        lower_out = _prefix_carries(forced, propagate, count)
        lower_in = (lower_out << 6) & ones
        inner_carry = (lower_out >> (6 * (count - 1))) & 1
        center_digit: int | None = None
        if center is not None:
            middle = 2 * center + inner_carry
            inner_carry, center_digit = divmod(middle, 10)

        inward_bit = 1 << (6 * (count - 1))
        upper_out = _prefix_carries(
            forced | (propagate & (inward_bit if inner_carry else 0)),
            propagate,
            count,
            reversed_order=True,
        )
        upper_in = (upper_out >> 6) | (inward_bit if inner_carry else 0)
        growth = upper_out & 1

        lower_digits = source + lower_in - 10 * lower_out
        upper_digits = source + upper_in - 10 * upper_out
        if growth:
            projected = lower_digits + ((upper_digits << 6) & lane_mask) + 1
            top_inner = (upper_digits >> (6 * (count - 1))) & 63
            if center is None:
                target = PackedQ19._from_trusted(projected, count, top_inner)
            else:
                if center_digit is None:
                    raise AssertionError("width birth lost its center emission")
                target = PackedQ19._from_trusted(
                    projected | ((center_digit + top_inner) << (6 * count)),
                    count + 1,
                    None,
                )
        else:
            target = PackedQ19._from_trusted(
                lower_digits + upper_digits, count, center_digit
            )

        digits: tuple[int, ...] | None = None
        if emit_digits:
            low = tuple((lower_digits >> (6 * index)) & 63 for index in range(count))
            high = tuple((upper_digits >> (6 * index)) & 63 for index in range(count))
            digits = (
                low + (() if center_digit is None else (center_digit,)) + high[::-1]
            )
            if growth:
                digits += (1,)
        return target, digits


__all__ = ["PackedQ19"]

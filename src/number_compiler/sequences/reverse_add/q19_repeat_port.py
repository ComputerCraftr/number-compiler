"""Lossless *local* repeated-digit Q19 ports derived from addition carries.

The ordinary Q19 pair-sum state intentionally forgets which reflected source
contributed each pair. That is sufficient for the physical successor but NOT
for the same-column equality mask. Keep only its two necessary source
sidebands: positions containing 0 and 9. The repeating mask is then

    (reverse(zero_source) & ~incoming_carry) |
    (reverse(nine_source) & incoming_carry).

This is an exact one-step digit/action identity, not a certificate to repeat
an entire future Q19 temporal program. No physical source is invented or
recovered from a homogeneous 2**q * 11**g residue class.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass

from .q19_broadword_publisher import PackedQ19, reverse_dense_bits


@dataclass(frozen=True, slots=True)
class Q19RepeatAction:
    """One source step's generator reuse mask, with lazy digit-value detail.

    Neither the Boolean mask nor its optional ten exact digit submasks imply
    an all-future carry-source period. Value extraction visits only repeated
    positions and is not performed by the mask-only default transition.
    """

    width: int
    same_lsd: int
    carry_in_lsd: int
    source_pairs: int
    source_center: int | None
    reflected_nine_lsd: int

    def __post_init__(self) -> None:
        if type(self.width) is not int or self.width < 1:
            raise ValueError("repetition mask width must be positive")
        mask = (1 << self.width) - 1
        for value in (self.same_lsd, self.carry_in_lsd, self.reflected_nine_lsd):
            if type(value) is not int or value < 0 or value & ~mask:
                raise ValueError("repetition action mask exceeds source width")
        if type(self.source_pairs) is not int or self.source_pairs < 0:
            raise ValueError("invalid repeated-digit pair source")
        if self.source_center is not None and not 0 <= self.source_center <= 9:
            raise ValueError("invalid repeated-digit center")

    @property
    def reusable_single_digit_generators(self) -> int:
        return self.same_lsd.bit_count()

    def symbol_at(self, j: int) -> int | None:
        if type(j) is not int or not 0 <= j < self.width:
            raise IndexError("repeated generator position outside source")
        bit = 1 << j
        if not (self.same_lsd & bit):
            return None
        count = self.width // 2
        if self.source_center is not None and j == count:
            return self.source_center
        pair_sum = (self.source_pairs >> (6 * min(j, self.width - 1 - j))) & 63
        source_value = pair_sum - (9 if self.reflected_nine_lsd & bit else 0)
        if not 0 <= source_value <= 9:
            raise AssertionError(
                "Q19 repeated digit inconsistent with reflected source"
            )
        return source_value

    @property
    def value_masks(self) -> tuple[int, ...]:
        """Ten exact generator masks; evaluated only by a value consumer."""
        values = [0] * 10
        todo = self.same_lsd
        while todo:
            bit = todo & -todo
            j = bit.bit_length() - 1
            digit = self.symbol_at(j)
            if digit is None:
                raise AssertionError("repeated position lost its source digit")
            values[digit] |= bit
            todo ^= bit
        return tuple(values)


@dataclass(frozen=True, slots=True, init=False)
class Q19RepeatPortState:
    """Successor-closed Q19 pair sums + the *required* 0/9 source sidebands."""

    frame: PackedQ19
    zero_lsd: int
    nine_lsd: int

    @classmethod
    def _from_trusted(
        cls, frame: PackedQ19, zero_lsd: int, nine_lsd: int
    ) -> Q19RepeatPortState:
        width = frame.width
        mask = (1 << width) - 1
        if (
            type(zero_lsd) is not int
            or type(nine_lsd) is not int
            or zero_lsd < 0
            or nine_lsd < 0
            or (zero_lsd | nine_lsd) & ~mask
            or zero_lsd & nine_lsd
        ):
            raise ValueError("illegal zero/nine source sideband")
        result = object.__new__(cls)
        object.__setattr__(result, "frame", frame)
        object.__setattr__(result, "zero_lsd", zero_lsd)
        object.__setattr__(result, "nine_lsd", nine_lsd)
        return result

    @classmethod
    def from_digits(cls, digits_lsd: Sequence[int]) -> Q19RepeatPortState:
        frame = PackedQ19.from_digits(digits_lsd)
        zero = sum(1 << i for i, d in enumerate(digits_lsd) if d == 0)
        nine = sum(1 << i for i, d in enumerate(digits_lsd) if d == 9)
        return cls._from_trusted(frame, zero, nine)

    @classmethod
    def from_two_five_carry_planes(
        cls,
        carry_two: int,
        remainder_five: tuple[int, int, int],
        width: int,
    ) -> Q19RepeatPortState:
        """No decimal row: consume d = 5*c2 + r5 directly as Boolean planes."""
        frame = PackedQ19.from_two_five_carry_planes(carry_two, remainder_five, width)
        r0, r1, r2 = remainder_five
        mask = (1 << width) - 1
        zero = (~(carry_two | r0 | r1 | r2)) & mask
        nine = carry_two & r2 & (~(r0 | r1)) & mask
        return cls._from_trusted(frame, zero, nine)

    @classmethod
    def from_bcd_planes(
        cls, planes: tuple[int, int, int, int], width: int
    ) -> Q19RepeatPortState:
        """Issue source sidebands from one validated BCD plane window."""
        frame = PackedQ19.from_bcd_planes(planes, width)
        p0, p1, p2, p3 = planes
        mask = (1 << width) - 1
        zero = ~(p0 | p1 | p2 | p3) & mask
        nine = p0 & p3 & ~(p1 | p2) & mask
        return cls._from_trusted(frame, zero, nine)

    def advance(
        self, *, emit_digits: bool = False
    ) -> tuple[Q19RepeatPortState, Q19RepeatAction, tuple[int, ...] | None]:
        """Issue the equality/action partition from actual carry inlets.

        No full previous or next decimal row is constructed unless the caller
        explicitly requests the public endpoint digits.
        """
        if type(emit_digits) is not bool:
            raise TypeError("emit_digits must be Boolean")
        frame = self.frame
        target, digits, ports = frame.advance_with_ports(emit_digits=emit_digits)
        width = frame.width
        old_mask = (1 << width) - 1
        reflected_zero = reverse_dense_bits(self.zero_lsd, width)
        reflected_nine = reverse_dense_bits(self.nine_lsd, width)
        cin = ports.carry_in_lsd
        same = ((reflected_zero & ~cin) | (reflected_nine & cin)) & old_mask
        action = Q19RepeatAction(
            width, same, cin, frame.pairs, frame.center, reflected_nine
        )
        return (
            type(self)._from_trusted(target, ports.next_zero_lsd, ports.next_nine_lsd),
            action,
            digits,
        )


__all__ = ["Q19RepeatAction", "Q19RepeatPortState"]

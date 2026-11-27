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


def _is_tuple(value: object) -> bool:
    return isinstance(value, tuple)


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


_BYTE_REVERSE = bytes(int(f"{b:08b}"[::-1], 2) for b in range(256))


def reverse_dense_bits(bits: int, width: int) -> int:
    """Reflect a packed Boolean digit plane without visiting decimal columns."""
    if type(width) is not int or width < 0:
        raise ValueError("bit-plane width must be nonnegative")
    if type(bits) is not int or bits < 0 or bits >> width:
        raise ValueError("bit plane exceeds its width")
    if not width:
        return 0
    nbytes = (width + 7) // 8
    return int.from_bytes(
        bits.to_bytes(nbytes, "little").translate(_BYTE_REVERSE), "big"
    ) >> (8 * nbytes - width)


def _compaction_steps(count: int) -> tuple[tuple[int, int], ...]:
    """Build width-defined masks for the current operation."""
    if count <= 0:
        return ()
    steps: list[tuple[int, int]] = []
    group = 1
    while group < count:
        merged = 2 * group
        stride = 6 * merged
        blocks = (count + merged - 1) // merged
        every_block = ((1 << (stride * blocks)) - 1) // ((1 << stride) - 1)
        mask = every_block * ((1 << merged) - 1)
        steps.append((5 * group, mask))
        group = merged
    return tuple(steps)


def _compact_six_lanes(bits: int, count: int) -> int:
    """PEXT the low bit of each 6-bit Q19 lane via logarithmic butterflies."""
    if not count:
        return 0
    for shift, mask in _compaction_steps(count):
        bits = (bits | (bits >> shift)) & mask
    return bits & ((1 << count) - 1)


def _equal_six_lanes(word: int, count: int, value: int) -> int:
    """Dense Boolean mask of Q19 packed decimal digit lanes equal to value."""
    if not count:
        return 0
    ones, _ = _lane_masks(count)
    delta = word ^ (value * ones)
    mismatch = delta
    for shift in (1, 2, 3, 4, 5):
        mismatch |= delta >> shift
    return _compact_six_lanes(ones & ~mismatch, count)


@dataclass(frozen=True, slots=True)
class Q19TransitionPorts:
    """One physical Q19 step's carry inlet and successor extreme digit planes."""

    carry_in_lsd: int
    next_zero_lsd: int
    next_nine_lsd: int


def bcd_digit_at(planes: tuple[int, int, int, int], position: int) -> int:
    """Read one digit from already admitted BCD planes."""
    ones, twos, fours, eights = planes
    return (
        ((ones >> position) & 1)
        | (((twos >> position) & 1) << 1)
        | (((fours >> position) & 1) << 2)
        | (((eights >> position) & 1) << 3)
    )


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

    @classmethod
    def from_record(cls, value: object) -> PackedQ19:
        """Decode the full arithmetic field after its cache issuer was checked."""
        from number_compiler.arithmetic.contracts.input_validation import (
            is_exact_object_tuple,
        )

        if is_exact_object_tuple(value) and len(value) == 3:
            pairs, count, center = value
            if (
                type(pairs) is int
                and type(count) is int
                and (center is None or type(center) is int)
            ):
                return cls(pairs, count, center)
        raise ValueError("invalid packed Q19 record")

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

    @classmethod
    def from_joint_outputs(cls, ordinary: int, xor: int) -> PackedQ19:
        """Admit Q19 only after both outputs recover a reflected source pair."""
        from number_compiler.arithmetic.carry.joint_output_inverse import (
            recover_joint_operands,
        )
        from number_compiler.arithmetic.fields.radix import digits_lsd

        source, reflected = recover_joint_operands(ordinary, xor)
        digits = digits_lsd(source, 10)
        exact_reflection = 0
        for digit in digits:
            exact_reflection = 10 * exact_reflection + digit
        if reflected != exact_reflection:
            raise ValueError("joint outputs do not share a decimal reflection source")
        return cls.from_digits(digits)

    @classmethod
    def from_bcd_planes(
        cls, planes: tuple[int, int, int, int], width: int
    ) -> PackedQ19:
        """Consume a fixed-width Boolean BCD source without digit-row assembly.

        The scalar modulus/multiplier phase is not itself a physical
        reverse/add action.  This bridge only supplies the exact current
        Q19 pair sums; ``advance`` owns the physical successor.
        """
        if type(width) is not int or width < 1 or len(planes) != 4:
            raise ValueError("invalid Boolean-ring source width")
        if any(type(b) is not int or b < 0 or b >> width for b in planes):
            raise ValueError("Boolean-ring source plane exceeds physical width")
        # A packed BCD nibble >= 10 has its 8-bit set with its 4- or 2-bit.
        if planes[3] & (planes[2] | planes[1]):
            raise ValueError("Boolean-ring source contains an illegal BCD digit")

        if bcd_digit_at(planes, width - 1) == 0:
            raise ValueError("Boolean-ring source has a leading zero")
        count = width // 2
        pairs = 0
        for j in range(count):
            pair = bcd_digit_at(planes, j) + bcd_digit_at(planes, width - 1 - j)
            pairs |= pair << (6 * j)
        center = bcd_digit_at(planes, count) if width & 1 else None
        return cls(pairs, count, center)

    @classmethod
    def from_two_five_carry_planes(
        cls,
        binary_two_carries: int,
        complementary_five_remainders: tuple[int, int, int],
        width: int,
    ) -> PackedQ19:
        """Source-owned Q19 pair input from *both* lossless carry tracks.

        Each source decimal digit is d=5*c2+r5 (0<=r5<=4).
        Neither the binary carry sheet alone nor the packed sum of
        unrelated carry/no-carry observers is enough to select d.
        Q19 consumes these two tracks directly, without a decimal word.
        """
        if type(width) is not int or width < 1:
            raise ValueError("invalid complementary-sheet source width")
        mask = (1 << width) - 1
        if (
            type(binary_two_carries) is not int
            or binary_two_carries < 0
            or binary_two_carries & ~mask
        ):
            raise ValueError("invalid binary multiplier-two carry plane")
        if (
            not _is_tuple(complementary_five_remainders)
            or len(complementary_five_remainders) != 3
        ):
            raise ValueError("three base-five remainder bit planes are required")
        r0, r1, r2 = complementary_five_remainders
        if any(type(r) is not int or r < 0 or r & ~mask for r in (r0, r1, r2)) or r2 & (
            r0 | r1
        ):
            raise ValueError("base-five remainder bit planes contain an illegal digit")

        def at(j: int) -> int:
            return (
                5 * ((binary_two_carries >> j) & 1)
                + ((r0 >> j) & 1)
                + 2 * ((r1 >> j) & 1)
                + 4 * ((r2 >> j) & 1)
            )

        if at(width - 1) == 0:
            raise ValueError("two-sheet source has a leading zero")
        count = width // 2
        pairs = 0
        for j in range(count):
            pairs |= (at(j) + at(width - 1 - j)) << (6 * j)
        center = at(count) if width & 1 else None
        return cls(pairs, count, center)

    @property
    def width(self) -> int:
        return 2 * self.count + int(self.center is not None)

    def next_is_palindrome(self) -> bool:
        """Decide the next decimal palindrome from the complete pair field."""
        if self.count == 0:
            assert self.center is not None
            return self.center < 5
        outer = self.pairs & 63
        if outer < 10:
            if self.center is not None and self.center >= 5:
                return False
            ones, _ = _lane_masks(self.count)
            return not ((self.pairs + 22 * ones) & (ones << 5))
        if outer != 11 or self.center not in (None, 0):
            return False
        ones, _ = _lane_masks(self.count)
        return self.pairs == 11 * (self.pairs & ones)

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
        target, digits, _ports = self._advance_with_masks(
            ones, lane_mask, emit_digits=emit_digits
        )
        return target, digits

    def advance_with_ports(
        self, *, emit_digits: bool = False
    ) -> tuple[PackedQ19, tuple[int, ...] | None, Q19TransitionPorts]:
        """Advance once and return the physical carry and digit sidebands."""
        if type(emit_digits) is not bool:
            raise TypeError("Q19 physical endpoint selection must be Boolean")
        ones, lane_mask = _lane_masks(self.count) if self.count else (0, 0)
        target, digits, ports = self._advance_with_masks(
            ones, lane_mask, emit_digits=emit_digits, emit_ports=True
        )
        if ports is None:
            raise AssertionError("Q19 physical transition failed to issue carry ports")
        return target, digits, ports

    def advance_repeated(
        self,
        steps: int,
        *,
        before_step: Callable[[int, int], None] | None = None,
    ) -> PackedQ19:
        """Apply a bounded sequence while reusing masks at each pair width.

        The callback receives the logical lane count and prefix-round charge
        before each represented transition. The admitted homogeneous prefix
        uses one multiplication with zero carry rounds; its legacy callback
        count is bounded by four. Remaining nonlinear transitions are exact.
        """
        if type(steps) is not int or steps < 0:
            raise ValueError("Q19 repeated transition count must be nonnegative")
        if before_step is not None and not callable(before_step):
            raise TypeError("Q19 work observer must be callable")

        frame = self
        ones, lane_mask = _lane_masks(frame.count) if frame.count else (0, 0)
        if not steps:
            return frame
        if not frame.count and frame.center == 0 and before_step is None:
            return frame  # the zero homogeneous state is an exact fixed point
        # Resolve the maximal initial carry-free run algebraically. For a
        # nonzero decimal word it has at most four ticks, so this guard has
        # fixed cost. The entire pair field is multiplied by 2**quiet once.
        # The legacy observer still receives its bounded logical accounting
        # callbacks; no intermediate pair/forcing rows are constructed.
        if (
            steps > 1
            and (frame.center is None or frame.center < 5)
            and not ((frame.pairs + 22 * ones) & (ones << 5))
        ):
            quiet = 1
            while quiet < min(steps, 4):
                limit = 9 >> quiet
                if (frame.center or 0) * 2 > limit or (
                    frame.pairs + (31 - limit) * ones
                ) & (ones << 5):
                    break
                quiet += 1
            if before_step is not None:
                for _ in range(quiet):  # at most four logical observer calls
                    before_step(frame.count, 0)
            frame = PackedQ19._from_trusted(
                frame.pairs << quiet,
                frame.count,
                None if frame.center is None else frame.center << quiet,
            )
            steps -= quiet
        for _ in range(steps):
            rounds = (frame.count - 1).bit_length() if frame.count else 0
            if before_step is not None:
                before_step(frame.count, rounds)
            previous_count = frame.count
            frame, _digits, _ports = frame._advance_with_masks(ones, lane_mask)
            if frame.count != previous_count:
                ones, lane_mask = _lane_masks(frame.count) if frame.count else (0, 0)
        return frame

    def _advance_with_masks(
        self,
        ones: int,
        lane_mask: int,
        *,
        emit_digits: bool = False,
        emit_ports: bool = False,
    ) -> tuple[PackedQ19, tuple[int, ...] | None, Q19TransitionPorts | None]:
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
            center_ports = (
                Q19TransitionPorts(0, int(digit == 0), int(digit == 9))
                if emit_ports
                else None
            )
            return target, emitted if emit_digits else None, center_ports

        source = self.pairs
        # Since s<=18, the bit-5 threshold comparison cannot spill lanes.
        threshold_bit = ones << 5
        forced = ((source + 22 * ones) & threshold_bit) >> 5
        # With no generating coefficient and an initially zero carry, all
        # forward and reflected carry ports are identically zero, even on
        # runs of 9s. E=0: the exact pair action is just multiplication by 2.
        if (
            not forced
            and (center is None or center < 5)
            and not emit_digits
            and not emit_ports
        ):
            return (
                PackedQ19._from_trusted(
                    source << 1, count, None if center is None else 2 * center
                ),
                None,
                None,
            )
        propagate = (((source + 23 * ones) & threshold_bit) >> 5) ^ forced

        # A radix-64 addition carries directly between packed lanes. Adding
        # 54 makes a lane overflow exactly when pair + incoming carry >= 10.
        lower_out = (~(source + 54 * ones) & threshold_bit) >> 5
        lower_in = (lower_out << 6) & ones
        inner_carry = (lower_out >> (6 * (count - 1))) & 1
        center_in = inner_carry
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
        ports: Q19TransitionPorts | None = None
        if emit_ports:
            lower_cin = _compact_six_lanes(lower_in & ones, count)
            upper_cin = _compact_six_lanes(upper_in & ones, count)
            high_shift = count + int(center is not None)
            cin = lower_cin | (reverse_dense_bits(upper_cin, count) << high_shift)
            if center is not None:
                cin |= center_in << count

            def extremes(value: int) -> int:
                low = _equal_six_lanes(lower_digits, count, value)
                high = _equal_six_lanes(upper_digits, count, value)
                both = low | (reverse_dense_bits(high, count) << high_shift)
                if center_digit == value:
                    both |= 1 << count
                return both

            ports = Q19TransitionPorts(cin, extremes(0), extremes(9))
        return target, digits, ports


__all__ = ["PackedQ19", "Q19TransitionPorts"]

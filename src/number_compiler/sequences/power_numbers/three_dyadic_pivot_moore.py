"""Bounded 2-adic pivot observations for the dyadic three-power source.

The observer derives finite windows from the exact recurrence
``u_(t+1) = u_t + 2^(t+1) * u_t^2`` for
``3^(2^t) = 1 + 2^(t+2) * u_t``.  Fixed low windows stabilize without work
proportional to a large level.  A moving window is explicit and refuses before
allocating when its requested precision exceeds the bound.  These local ports
do not determine the global Fermat fold or a prime decision.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.sequences.power_numbers.three_dyadic_boolean_counter import (
    two_adic_unit_binomial,
)

if TYPE_CHECKING:
    from number_compiler.sequences.power_numbers.three_dyadic_boolean_counter import (
        DyadicBooleanCounterWindow,
    )

MAX_PIVOT_PRECISION = 4_096
DEFAULT_PIVOT_OFFSETS = (0, 1, 2, 3, 5, 6)


def _level(value: int) -> int:
    value = require_integer(value, "dyadic source level", 1)
    if value.bit_length() > MAX_PIVOT_PRECISION:
        raise ValueError(("dyadic-source-level-budget", MAX_PIVOT_PRECISION))
    return value


def _precision(value: int) -> int:
    return require_integer(value, "dyadic pivot precision", 1, MAX_PIVOT_PRECISION)


def _unit_residue(level: int, precision: int) -> int:
    """Exact, non-iterative 2-adic unit via truncated binomial powers.

    This replaces chronological recurrence pumping with the bounded
    coefficient quotient.  In particular a huge level needs no level-sized
    modular-square sequence to answer a small requested window.
    """
    return two_adic_unit_binomial(level, precision)


def _next_unit_residue(level: int, unit: int, precision: int) -> int:
    if level + 1 >= precision:
        return unit
    mask = (1 << precision) - 1
    return (unit + ((unit * unit) << (level + 1))) & mask


@dataclass(frozen=True, slots=True)
class DyadicPivotOffsets:
    """Exact low-pivot and normalized-unit coordinates at one level."""

    level: int

    def __post_init__(self) -> None:
        _level(self.level)

    @property
    def low_pivot(self) -> int:
        return self.level + 2

    @property
    def unit_flip_offset(self) -> int:
        return self.level + 1

    @property
    def unit_flip_source_coordinate(self) -> int:
        """Coordinate of the first unit-change bit, not a full-word XOR claim."""
        return 2 * self.level + 3


@dataclass(frozen=True, slots=True)
class GuardedUnitPivotRun:
    """Uniform changed interval in aligned unit coordinates only."""

    unit_start: int
    length: int
    expected_bit: int

    def __post_init__(self) -> None:
        require_integer(self.unit_start, "unit run start", 0)
        require_integer(self.length, "unit run length", 1)
        require_integer(self.expected_bit, "unit run expected bit", 0, 1)
        if (
            self.unit_start.bit_length() > MAX_PIVOT_PRECISION
            or self.length.bit_length() > MAX_PIVOT_PRECISION
            or (self.unit_start + self.length).bit_length() > MAX_PIVOT_PRECISION
        ):
            raise ValueError("unit run exceeds its source-coordinate budget")


@dataclass(frozen=True, slots=True)
class UnitInnovationWindow:
    """Demanded normalized-unit words and their exact aligned XOR mask."""

    level: int
    width: int
    unit_offset: int
    current_bits: int
    next_bits: int
    xor_mask: int
    runs: tuple[GuardedUnitPivotRun, ...]

    def __post_init__(self) -> None:
        _level(self.level)
        _precision(self.width)
        require_integer(self.unit_offset, "unit window offset", 0)
        if self.unit_offset.bit_length() > MAX_PIVOT_PRECISION:
            raise ValueError("unit window offset exceeds its coordinate budget")
        bound = 1 << self.width
        for name, value in (
            ("current unit window", self.current_bits),
            ("next unit window", self.next_bits),
            ("unit XOR mask", self.xor_mask),
        ):
            require_integer(value, name, 0, bound - 1)
        if self.xor_mask != self.current_bits ^ self.next_bits:
            raise ValueError("unit innovation mask does not match its two windows")
        if type(self.runs) is not tuple or any(
            type(run) is not GuardedUnitPivotRun for run in self.runs
        ):
            raise TypeError("unit pivot runs must be exact guarded records")
        if self.runs != _runs_from_mask(
            self.current_bits, self.xor_mask, self.width, self.unit_offset
        ):
            raise ValueError("unit pivot runs do not match the guarded XOR mask")


def _runs_from_mask(
    current: int, xor_mask: int, width: int, offset: int
) -> tuple[GuardedUnitPivotRun, ...]:
    result: list[GuardedUnitPivotRun] = []
    position = 0
    while position < width:
        if not (xor_mask >> position) & 1:
            position += 1
            continue
        expected = (current >> position) & 1
        start = position
        position += 1
        while (
            position < width
            and (xor_mask >> position) & 1
            and ((current >> position) & 1) == expected
        ):
            position += 1
        result.append(GuardedUnitPivotRun(offset + start, position - start, expected))
    return tuple(result)


def fixed_unit_innovation_window(level: int, width: int) -> UnitInnovationWindow:
    """Observe fixed low unit bits with cost independent of a huge level."""
    selected_level = _level(level)
    selected_width = _precision(width)
    current = _unit_residue(selected_level, selected_width)
    following = _next_unit_residue(selected_level, current, selected_width)
    mask = current ^ following
    return UnitInnovationWindow(
        selected_level,
        selected_width,
        0,
        current,
        following,
        mask,
        _runs_from_mask(current, mask, selected_width, 0),
    )


def moving_unit_innovation_window(level: int, width: int) -> UnitInnovationWindow:
    """Observe the window beginning at unit offset ``level+1`` under a hard cap."""
    selected_level = _level(level)
    selected_width = _precision(width)
    precision = selected_level + 1 + selected_width
    if precision > MAX_PIVOT_PRECISION:
        raise ValueError(
            ("moving-pivot-precision-budget", precision, MAX_PIVOT_PRECISION)
        )
    current_unit = _unit_residue(selected_level, precision)
    next_unit = _next_unit_residue(selected_level, current_unit, precision)
    offset = selected_level + 1
    mask = (1 << selected_width) - 1
    current = (current_unit >> offset) & mask
    following = (next_unit >> offset) & mask
    xor_mask = current ^ following
    return UnitInnovationWindow(
        selected_level,
        selected_width,
        offset,
        current,
        following,
        xor_mask,
        _runs_from_mask(current, xor_mask, selected_width, offset),
    )


@dataclass(frozen=True, slots=True)
class PivotMooreObservation:
    """Exact source-local ports at selected offsets from the low pivot."""

    level: int
    offsets: tuple[int, ...]
    source_bits: tuple[int, ...]
    tripling_carries: tuple[int, ...]
    innovation_borrows: tuple[int, ...]
    successive_innovation_borrows: tuple[int, ...]
    aligned_unit_xor_mask: int

    def __post_init__(self) -> None:
        _level(self.level)
        if type(self.offsets) is not tuple or not self.offsets:
            raise ValueError("pivot observation requires a fixed nonempty offset tuple")
        for offset in self.offsets:
            require_integer(offset, "pivot observation offset", 0)
        if (
            tuple(sorted(set(self.offsets))) != self.offsets
            or self.offsets[-1] >= MAX_PIVOT_PRECISION
        ):
            raise ValueError("pivot observation offsets exceed their fixed profile")
        expected_length = len(self.offsets)
        for values in (
            self.source_bits,
            self.tripling_carries,
            self.innovation_borrows,
            self.successive_innovation_borrows,
        ):
            if type(values) is not tuple or len(values) != expected_length:
                raise ValueError(
                    "pivot output fields must align with requested offsets"
                )
        for bit in self.source_bits:
            require_integer(bit, "pivot source bit", 0, 1)
        for carry in self.tripling_carries:
            require_integer(carry, "tripling carry", 0, 2)
        for bit in self.innovation_borrows + self.successive_innovation_borrows:
            require_integer(bit, "innovation borrow", 0, 1)
        require_integer(
            self.aligned_unit_xor_mask,
            "aligned unit XOR mask",
            0,
            (1 << (self.offsets[-1] + 1)) - 1,
        )


@dataclass(frozen=True, slots=True)
class DyadicPivotMoore:
    """Pointed fixed-offset observer with an external symbolic level."""

    level: int
    offsets: tuple[int, ...] = DEFAULT_PIVOT_OFFSETS

    def __post_init__(self) -> None:
        _level(self.level)
        if type(self.offsets) is not tuple or not self.offsets:
            raise ValueError("pivot observer offsets must be a nonempty exact tuple")
        for offset in self.offsets:
            require_integer(offset, "pivot observer offset", 0)
        if tuple(sorted(set(self.offsets))) != self.offsets:
            raise ValueError("pivot offsets must be strictly increasing")
        if self.offsets[-1] >= MAX_PIVOT_PRECISION:
            raise ValueError("pivot offset exceeds the fixed observation budget")

    @property
    def geometry(self) -> DyadicPivotOffsets:
        return DyadicPivotOffsets(self.level)

    @property
    def stationary_from(self) -> int:
        """Conservative recurrence bound for this observer profile."""
        return self.offsets[-1] + 1

    @property
    def action_depth(self) -> int:
        """Observer-local transient depth; no minimality is claimed."""
        return max(0, self.stationary_from - self.level)

    @property
    def action_id(self) -> str:
        profile = ",".join(str(offset) for offset in self.offsets)
        return f"Q{self.action_depth}[{profile}]"

    def advance(self, steps: int) -> DyadicPivotMoore:
        steps = require_integer(steps, "pivot advance", 0)
        return DyadicPivotMoore(self.level + steps, self.offsets)

    def observe(self) -> PivotMooreObservation:
        """Project source-local carry/borrow fields without building ``3**2**t``."""
        precision = self.offsets[-1] + 1
        current_unit = _unit_residue(self.level, precision)
        next_unit = _next_unit_residue(self.level, current_unit, precision)
        later_unit = _next_unit_residue(self.level + 1, next_unit, precision)
        aligned_xor = current_unit ^ next_unit
        source_bits = tuple((current_unit >> offset) & 1 for offset in self.offsets)

        tripling_carry = 0  # The source prefix is 1, then zeros up to the pivot.
        tripling: list[int] = []
        innovation_borrow = 0
        innovation: list[int] = []
        v_current = (2 * next_unit - current_unit) & ((1 << precision) - 1)
        v_next = (2 * later_unit - next_unit) & ((1 << precision) - 1)
        successive_borrow = 0
        successive: list[int] = []
        offset_set = set(self.offsets)
        max_offset = self.offsets[-1]
        for offset in range(max_offset + 1):
            current_bit = (current_unit >> offset) & 1
            next_bit = 0 if offset == 0 else (next_unit >> (offset - 1)) & 1
            carry_sum = 3 * current_bit + tripling_carry
            tripling_carry = carry_sum >> 1
            diff = next_bit - current_bit - innovation_borrow
            innovation_borrow = int(diff < 0)

            later_innovation_bit = (2 * v_next >> offset) & 1
            current_innovation_bit = (v_current >> offset) & 1
            innovation_diff = (
                later_innovation_bit - current_innovation_bit - successive_borrow
            )
            successive_borrow = int(innovation_diff < 0)
            if offset in offset_set:
                tripling.append(tripling_carry)
                innovation.append(innovation_borrow)
                successive.append(successive_borrow)
        return PivotMooreObservation(
            self.level,
            self.offsets,
            source_bits,
            tuple(tripling),
            tuple(innovation),
            tuple(successive),
            aligned_xor & ((1 << precision) - 1),
        )

    def fixed_unit_window(self, width: int) -> UnitInnovationWindow:
        return fixed_unit_innovation_window(self.level, width)

    def moving_unit_window(self, width: int) -> UnitInnovationWindow:
        return moving_unit_innovation_window(self.level, width)

    def boolean_counter(
        self, width: int, *, fermat_width: int, offset: int = 0
    ) -> DyadicBooleanCounterWindow:
        """Demand the full two-port add/XOR/fold action at a moving pivot.

        The returned signed positional-class totals cover *only* the
        authenticated window, not all high bits of the Fermat source.
        """
        from number_compiler.sequences.power_numbers.three_dyadic_boolean_counter import (
            demand_dyadic_boolean_counter,
        )

        return demand_dyadic_boolean_counter(
            self.level, width, fermat_width=fermat_width, offset=offset
        )


__all__ = [
    "DEFAULT_PIVOT_OFFSETS",
    "MAX_PIVOT_PRECISION",
    "DyadicPivotMoore",
    "DyadicPivotOffsets",
    "GuardedUnitPivotRun",
    "PivotMooreObservation",
    "UnitInnovationWindow",
    "fixed_unit_innovation_window",
    "moving_unit_innovation_window",
]

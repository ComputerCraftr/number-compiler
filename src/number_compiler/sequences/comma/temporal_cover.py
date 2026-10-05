"""Exact finite temporal covers and weighted comma-port jumps.

The 86-state even-response key is ``(leading, folded_digit)``.  A single
admissible sheet bit reconstructs the physical port when the key is one of
the four doubled fibers.  Temporal actions and exact occurrence weights are
kept separate. These are fixed-sector punctured-port actions: ``steps``
counts port moves, and ``weight`` counts diagonal dwell rows. Neither is a
literal sequence index or a decimal-exponent increment. The 181/14 endpoint
projections do not preserve the full harmonic/reset observer.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from .arithmetic import (
    CycleTransfer,
    comma_port_dwell,
    comma_port_next,
    comma_port_previous,
    cycle_transfer,
)

WorkCharge = Callable[[int], None]
BitsCharge = Callable[[int], None]


def _validate_port(leading: int, digit: int) -> None:
    if (
        type(leading) is not int
        or not 1 <= leading <= 9
        or type(digit) is not int
        or not 0 <= digit <= 9
    ):
        raise ValueError("comma temporal port requires leading 1..9 and digit 0..9")


def _charge(
    charge_work: WorkCharge | None,
    charge_bits: BitsCharge | None,
    work: int,
    *operands: int,
) -> None:
    if charge_work is not None:
        charge_work(work)
    if charge_bits is not None:
        charge_bits(sum(value.bit_length() for value in operands) + 8 * len(operands))


def _fold_digit(leading: int, digit: int) -> int:
    return digit - 5 if leading == 5 and digit > 5 else digit


@dataclass(frozen=True, slots=True)
class TemporalPortCover:
    """A resumable exact port over the 86 complete-even response classes.

    ``(leading, folded_digit)`` is the 86-state key. ``sheet`` is constrained
    to the image of physical ports; it is not a free bit on singleton fibers.
    """

    leading: int
    folded_digit: int
    sheet: bool

    def __post_init__(self) -> None:
        if (
            type(self.leading) is not int
            or not 1 <= self.leading <= 9
            or type(self.folded_digit) is not int
            or not 0 <= self.folded_digit <= 9
            or type(self.sheet) is not bool
        ):
            raise ValueError("invalid comma temporal cover coordinates")
        digit = self.digit
        if _fold_digit(self.leading, digit) != self.folded_digit:
            raise ValueError("comma temporal cover is not in the physical image")
        if self.sheet != (self.leading <= digit):
            raise ValueError("comma temporal sheet disagrees with its physical port")

    @classmethod
    def from_port(
        cls,
        leading: int,
        digit: int,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> TemporalPortCover:
        _validate_port(leading, digit)
        _charge(charge_work, charge_bits, 1, leading, digit)
        return cls(leading, _fold_digit(leading, digit), leading <= digit)

    @property
    def digit(self) -> int:
        if self.leading == 5 and 1 <= self.folded_digit <= 4 and self.sheet:
            return self.folded_digit + 5
        return self.folded_digit

    @property
    def even_key(self) -> tuple[int, int]:
        """The complete-even semantic key, without occurrence sheet data."""
        return self.leading, self.folded_digit

    @property
    def centered_defect(self) -> int:
        digit = self.digit
        return digit + comma_port_previous(self.leading, digit) - 9

    def step(
        self,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> TemporalPortCover:
        # Charge the arithmetic transition separately from result admission.
        _charge(charge_work, charge_bits, 1, self.leading, self.digit)
        return TemporalPortCover.from_port(
            self.leading,
            comma_port_next(self.leading, self.digit),
            charge_work=charge_work,
            charge_bits=charge_bits,
        )


@dataclass(frozen=True, slots=True)
class PortTime:
    """Unary temporal class: ``None`` is zero; 0..179 encode positive time."""

    positive_offset: int | None

    def __post_init__(self) -> None:
        if self.positive_offset is not None and (
            type(self.positive_offset) is not int or not 0 <= self.positive_offset < 180
        ):
            raise ValueError("positive comma time offset must be in 0..179")


def port_time_for_duration(
    duration: int,
    *,
    charge_work: WorkCharge | None = None,
    charge_bits: BitsCharge | None = None,
) -> PortTime:
    if type(duration) is not int or duration < 0:
        raise ValueError("comma temporal duration must be a nonnegative integer")
    _charge(charge_work, charge_bits, 1, duration)
    if duration == 0:
        return PortTime(None)
    return PortTime((duration - 1) % 180)


def compose_port_times(
    left: PortTime,
    right: PortTime,
    *,
    charge_work: WorkCharge | None = None,
    charge_bits: BitsCharge | None = None,
) -> PortTime:
    if type(left) is not PortTime or type(right) is not PortTime:
        raise ValueError("comma time composition requires admitted PortTime values")
    _charge(
        charge_work,
        charge_bits,
        1,
        left.positive_offset or 0,
        right.positive_offset or 0,
    )
    if left.positive_offset is None:
        return right
    if right.positive_offset is None:
        return left
    return PortTime((left.positive_offset + right.positive_offset + 1) % 180)


@dataclass(frozen=True, slots=True)
class PortDyadicTime:
    """A 14-state normalization of the exact unary port action only."""

    code: int

    def __post_init__(self) -> None:
        if type(self.code) is not int or not 0 <= self.code < 14:
            raise ValueError("comma dyadic time code must be in 0..13")


def dyadic_time_for_level(
    level: int,
    *,
    charge_work: WorkCharge | None = None,
    charge_bits: BitsCharge | None = None,
) -> PortDyadicTime:
    if type(level) is not int or level < 0:
        raise ValueError("comma dyadic level must be a nonnegative integer")
    _charge(charge_work, charge_bits, 1, level)
    if level < 2:
        return PortDyadicTime(level)
    return PortDyadicTime(2 + (level - 2) % 12)


def square_dyadic_time(
    action: PortDyadicTime,
    *,
    charge_work: WorkCharge | None = None,
    charge_bits: BitsCharge | None = None,
) -> PortDyadicTime:
    if type(action) is not PortDyadicTime:
        raise ValueError("comma dyadic squaring requires a PortDyadicTime")
    _charge(charge_work, charge_bits, 1, action.code)
    if action.code < 2:
        return PortDyadicTime(action.code + 1)
    return PortDyadicTime(2 + (action.code - 1) % 12)


def dyadic_time_semantics(
    action: PortDyadicTime,
    *,
    charge_work: WorkCharge | None = None,
    charge_bits: BitsCharge | None = None,
) -> PortTime:
    """Project a normalized dyadic level to the bounded unary port action."""
    if type(action) is not PortDyadicTime:
        raise ValueError("comma dyadic semantics requires a PortDyadicTime")
    _charge(charge_work, charge_bits, 1, action.code)
    if action.code < 2:
        return PortTime(action.code)
    exponent = action.code
    return PortTime((pow(2, exponent) - 1) % 180)


def _cycle_length_from_transfer(digit: int, transfer: CycleTransfer) -> int:
    divisor = 10 // transfer.period
    length = transfer.period - int(digit % divisor == 0)
    if not 1 <= length <= 9:
        raise ArithmeticError("punctured comma period escaped its admitted bound")
    return length


def _apply_positive_prefix(
    leading: int,
    digit: int,
    steps: int,
    *,
    charge_work: WorkCharge | None,
    charge_bits: BitsCharge | None,
) -> int:
    _charge(charge_work, charge_bits, 3, leading, digit, steps)
    first = comma_port_next(leading, digit)
    transfer = cycle_transfer(leading, first)
    cycle_length = _cycle_length_from_transfer(first, transfer)
    remainder = (steps - 1) % cycle_length
    current = first
    for _ in range(remainder):
        _charge(charge_work, charge_bits, 1, leading, current)
        current = comma_port_next(leading, current)
    return current


def apply_port_time(
    leading: int,
    digit: int,
    action: PortTime,
    *,
    charge_work: WorkCharge | None = None,
    charge_bits: BitsCharge | None = None,
) -> int:
    _validate_port(leading, digit)
    if type(action) is not PortTime:
        raise ValueError("comma temporal application requires a PortTime")
    _charge(charge_work, charge_bits, 1, leading, digit)
    if action.positive_offset is None:
        return digit
    steps = action.positive_offset + 1
    _charge(charge_work, charge_bits, 1, leading, digit, steps)
    return _apply_positive_prefix(
        leading,
        digit,
        steps,
        charge_work=charge_work,
        charge_bits=charge_bits,
    )


def apply_dyadic_time(
    cover: TemporalPortCover,
    action: PortDyadicTime,
    *,
    charge_work: WorkCharge | None = None,
    charge_bits: BitsCharge | None = None,
) -> TemporalPortCover:
    if type(cover) is not TemporalPortCover or type(action) is not PortDyadicTime:
        raise ValueError("comma dyadic application requires admitted action and cover")
    return advance_temporal_cover(
        cover,
        dyadic_time_semantics(
            action,
            charge_work=charge_work,
            charge_bits=charge_bits,
        ),
        charge_work=charge_work,
        charge_bits=charge_bits,
    )


def advance_temporal_cover(
    cover: TemporalPortCover,
    action: PortTime,
    *,
    charge_work: WorkCharge | None = None,
    charge_bits: BitsCharge | None = None,
) -> TemporalPortCover:
    if type(cover) is not TemporalPortCover or type(action) is not PortTime:
        raise ValueError(
            "comma temporal application requires admitted action and cover"
        )
    if action.positive_offset is None:
        _charge(charge_work, charge_bits, 1, cover.leading, cover.digit)
        return cover
    # Endpoint calculation and newly allocated cover admission are distinct work.
    digit = apply_port_time(
        cover.leading,
        cover.digit,
        action,
        charge_work=charge_work,
        charge_bits=charge_bits,
    )
    return TemporalPortCover.from_port(
        cover.leading,
        digit,
        charge_work=charge_work,
        charge_bits=charge_bits,
    )


@dataclass(frozen=True, slots=True)
class WeightedPortResult:
    """Exact endpoint and additive dwell cocycle for a requested prefix."""

    endpoint: int
    weight: int
    complete_cycles: int
    tail_steps: int


def advance_weighted_port(
    leading: int,
    digit: int,
    steps: int,
    *,
    charge_work: WorkCharge | None = None,
    charge_bits: BitsCharge | None = None,
) -> WeightedPortResult:
    """Advance a weighted port in bounded work, preserving the exact cocycle.

    Positive horizons use one startup transition, one exact cycle division,
    and at most eight tail transitions.  The arbitrary-size cycle count is
    occurrence weight data; no path or duration-sized table is constructed.
    """
    _validate_port(leading, digit)
    if type(steps) is not int or steps < 0:
        raise ValueError("comma weighted steps must be a nonnegative integer")
    _charge(charge_work, charge_bits, 2, leading, digit, steps)
    if steps == 0:
        return WeightedPortResult(digit, 0, 0, 0)

    first = comma_port_next(leading, digit)
    weight = comma_port_dwell(leading, digit)
    _charge(charge_work, charge_bits, 3, leading, first, steps)
    cycle = cycle_transfer(leading, first)
    cycle_length = _cycle_length_from_transfer(first, cycle)
    _charge(charge_work, charge_bits, 2, steps, cycle_length, cycle.displacement)
    cycle_weight, remainder = divmod(steps - 1, cycle_length)
    per_cycle_weight, residue = divmod(cycle.displacement, 10)
    if residue:
        raise ArithmeticError("comma cycle cocycle is not an integer decade weight")
    current = first
    _charge(charge_work, charge_bits, 2, cycle_weight, per_cycle_weight)
    weight += cycle_weight * per_cycle_weight
    for _ in range(remainder):
        _charge(charge_work, charge_bits, 1, leading, current, weight)
        weight += comma_port_dwell(leading, current)
        current = comma_port_next(leading, current)
    return WeightedPortResult(current, weight, cycle_weight, remainder)


__all__ = [
    "PortDyadicTime",
    "PortTime",
    "TemporalPortCover",
    "WeightedPortResult",
    "advance_temporal_cover",
    "advance_weighted_port",
    "apply_dyadic_time",
    "apply_port_time",
    "compose_port_times",
    "dyadic_time_for_level",
    "dyadic_time_semantics",
    "port_time_for_duration",
    "square_dyadic_time",
]

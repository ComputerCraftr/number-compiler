"""Exact decimal comma-child and guarded cyclotomic-sector arithmetic.

The periodic transfer is a statement about one fixed leading-digit sector.
It is never used to decide which child of a fork has an infinite future.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd

from number_compiler.arithmetic.fields.consumer_pullback import PrefixSafety


@dataclass(frozen=True, slots=True)
class DecimalSector:
    leading: int
    scale: int
    exponent: int
    boundary: int
    digit: int
    headroom: int


@dataclass(frozen=True, slots=True)
class CycleTransfer:
    leading: int
    entering_digit: int
    period: int
    displacement: int
    maximum_guard: int


def _decimal_scale(value: int) -> tuple[int, int]:
    if type(value) is not int or value <= 0:
        raise ValueError("comma value must be a positive integer")
    # A bit-length estimate avoids converting an arbitrarily large integer to
    # a decimal string (and avoids Python's int-to-string digit limit).
    exponent = ((value.bit_length() - 1) * 30103) // 100000
    scale = pow(10, exponent)
    while value < scale:
        scale //= 10
        exponent -= 1
    while value >= scale * 10:
        scale *= 10
        exponent += 1
    return scale, exponent


def leading_digit(value: int) -> int:
    scale, _ = _decimal_scale(value)
    return value // scale


def decimal_sector(value: int) -> DecimalSector:
    scale, exponent = _decimal_scale(value)
    leading = value // scale
    boundary = (leading + 1) * scale if leading < 9 else 10 * scale
    return DecimalSector(
        leading, scale, exponent, boundary, value % 10, boundary - value
    )


def comma_children(value: int) -> tuple[int, ...]:
    """Enumerate all nine exact children, in numerical order.

    This bounded primitive is used at startup and near a seam. The powered
    interior path uses :func:`safe_complete_cycles` instead.
    """
    digit = value % 10
    children = tuple(
        value + 10 * digit + new_leading
        for new_leading in range(1, 10)
        if leading_digit(value + 10 * digit + new_leading) == new_leading
    )
    return children


def cycle_transfer(leading: int, entering_digit: int) -> CycleTransfer:
    if type(leading) is not int or not 1 <= leading <= 9:
        raise ValueError("cycle leading digit must be 1 through 9")
    if type(entering_digit) is not int or not 0 <= entering_digit <= 9:
        raise ValueError("cycle phase must be 0 through 9")
    period = 10 // gcd(leading, 10)
    digit = entering_digit
    safety = PrefixSafety()
    for _ in range(period):
        # For f<9, only the f+1 child can appear across the next sector
        # boundary. In the 9-sector, q_9 is the larger of the two possible
        # seam jumps and guards the power-of-ten crossing.
        guard_digit = leading + 1 if leading < 9 else 9
        step = 10 * digit + leading
        safety = safety.then(PrefixSafety(-step, -(10 * digit + guard_digit)))
        digit = (digit + leading) % 10
    if digit != entering_digit:
        raise AssertionError("decimal phase did not close after its period")
    return CycleTransfer(
        leading, entering_digit, period, -safety.delta, -safety.minimum
    )


def safe_complete_cycles(
    value: int, transfer: CycleTransfer, remaining_steps: int
) -> int:
    """Largest admitted count of entire phase cycles before a sector seam.

    Strict inequality keeps every child in the same sector throughout the
    skipped block, including at a potential fork equality.
    """
    if type(remaining_steps) is not int or remaining_steps < 0:
        raise ValueError("remaining steps must be nonnegative")
    sector = decimal_sector(value)
    if sector.leading != transfer.leading or sector.digit != transfer.entering_digit:
        raise ValueError("cycle transfer has another entering cylinder")
    by_target = remaining_steps // transfer.period
    safety = PrefixSafety(-transfer.displacement, -transfer.maximum_guard)
    failure = safety.first_failing_copy(sector.boundary - 1 - value, by_target)
    return by_target if failure is None else failure


__all__ = [
    "CycleTransfer",
    "DecimalSector",
    "comma_children",
    "cycle_transfer",
    "decimal_sector",
    "leading_digit",
    "safe_complete_cycles",
]

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
    return _decimal_sector_from_scale(value, scale, exponent)


def _decimal_sector_from_scale(value: int, scale: int, exponent: int) -> DecimalSector:
    """Use an already authenticated decimal scale for a monotone sector walk."""
    if (
        type(value) is not int
        or type(scale) is not int
        or type(exponent) is not int
        or scale <= 0
        or exponent < 0
        or not scale <= value < 10 * scale
    ):
        raise ValueError("decimal sector scale does not contain its value")
    leading = value // scale
    boundary = (leading + 1) * scale if leading < 9 else 10 * scale
    return DecimalSector(
        leading, scale, exponent, boundary, value % 10, boundary - value
    )


def _large_sector_children(value: int, sector: DecimalSector) -> tuple[int, ...]:
    """Classify children from the authentic sector of ``value`` for exponent >= 2.

    Callers must obtain ``sector`` from :func:`decimal_sector` for this value.
    This internal primitive avoids nine candidate leading-digit decompositions.
    """
    f, d, h = sector.leading, sector.digit, sector.headroom
    if f < 9:
        low = value + 10 * d + f
        high = low + 1
        if h > 10 * d + f + 1:
            return (low,)
        if h == 10 * d + f + 1:
            return (low, high)
        return (high,)
    if h > 10 * d + 9:
        return (value + 10 * d + 9,)
    if h <= 10 * d + 1:
        return (value + 10 * d + 1,)
    return ()


def comma_children(value: int) -> tuple[int, ...]:
    """Return the exact children in numerical order.

    Large sectors use the exact tropical seam rule. Only startup values below
    100 need the bounded nine-candidate search.
    """
    sector = decimal_sector(value)
    if sector.exponent >= 2:
        return _large_sector_children(value, sector)
    digit = sector.digit
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
    divisor = gcd(leading, 10)
    period = 10 // divisor
    residue = entering_digit % divisor
    # The phase visits every digit in this residue class exactly once.  Each
    # literal increment is 10*d + leading, so the whole orbit has this sum.
    displacement = (
        10 * (period * residue + divisor * period * (period - 1) // 2)
        + period * leading
    )
    # At every prefix the strict interior guard is its next displacement
    # plus one for sectors 1..8 and plus zero for sector 9.  Increments are
    # positive; the final prefix therefore has the maximum guard.
    return CycleTransfer(
        leading,
        entering_digit,
        period,
        displacement,
        displacement + int(leading < 9),
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

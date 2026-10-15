"""Exact scalar reverse-pair oracle shared by independent tests."""

from devtools.verification.oracles.sequence_arithmetic import (
    reference_successor,
)

__all__ = ("literal_decimal_borrow_tape", "reference_successor")


def literal_decimal_borrow_tape(
    minuend: int, subtrahend: int, width: int
) -> tuple[int, int]:
    """Independent LSD-first decimal subtraction mask and final borrow."""
    if any(type(value) is not int or value < 0 for value in (minuend, subtrahend)):
        raise ValueError("borrow oracle operands must be nonnegative integers")
    if type(width) is not int or width < 0:
        raise ValueError("borrow oracle width must be a nonnegative integer")
    mask = 0
    place = 10
    for index in range(width):
        if minuend % place < subtrahend % place:
            mask |= 1 << index
        place *= 10
    return mask, int(minuend < subtrahend)


def symmetric_reference_successor(
    full: tuple[int, ...], base: int = 10
) -> tuple[int, ...]:
    result = reference_successor(full, base)
    assert result == result[::-1]
    return result


def reference_power(
    values: tuple[int, ...], base: int, steps: int
) -> tuple[tuple[int, ...], list[int], list[int]]:
    expected = values
    widths = [len(values)]
    growths: list[int] = []
    for _ in range(steps):
        following = symmetric_reference_successor(expected, base)
        growths.append(len(following) - len(expected))
        widths.append(len(following))
        expected = following
    return expected, growths, widths

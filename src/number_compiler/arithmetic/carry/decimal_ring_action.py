"""Exact one- and two-column decimal ring actions on complete halos."""

from __future__ import annotations


def centered_short_ring(
    word: tuple[int, ...], multiplier: int, steps: int
) -> tuple[int, ...]:
    """Power the centered two-sheet action, preserving both zero lifts."""
    if (
        len(word) not in (1, 2)
        or any(type(digit) is not int or not 0 <= digit <= 9 for digit in word)
        or type(multiplier) is not int
        or multiplier not in (2, 5)
        or type(steps) is not int
        or steps < 0
    ):
        raise ValueError("invalid centered decimal ring action")
    value = word[0] + 10 * word[-1]
    if value not in (0, 99):
        exponent = steps if multiplier == 2 else -steps
        value = value * pow(4, exponent % 15, 99) % 99
    return (value % 10, value // 10)[: len(word)]

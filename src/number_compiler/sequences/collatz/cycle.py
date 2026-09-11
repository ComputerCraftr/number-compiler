"""Certified source recognition for the Collatz ``1 -> 4 -> 2`` cycle."""

from collections.abc import Sequence


def fixed_cycle_target(source: Sequence[int], steps: int) -> int | None:
    """Return the certified cycle phase for an exact canonical binary source."""
    if type(steps) is not int or steps < 0:
        raise ValueError("Collatz cycle steps require a nonnegative exact integer")
    digits = tuple(source)
    starts = {(1,): (1, 4, 2), (0, 1): (2, 1, 4), (0, 0, 1): (4, 2, 1)}
    cycle = starts.get(digits)
    return None if cycle is None else cycle[steps % 3]


__all__ = ["fixed_cycle_target"]

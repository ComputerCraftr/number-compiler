"""Balanced finite sequence reductions shared by grammar experiments."""

from __future__ import annotations

from collections.abc import Callable, Sequence
from typing import TypeVar

T = TypeVar("T")


def balanced_reduce(
    values: Sequence[T],
    combine: Callable[[T, T], T],
    empty: Callable[[], T] | None = None,
) -> T:
    """Reduce adjacent pairs by levels, retaining an odd item at each level."""
    level = list(values)
    if not level:
        if empty is None:
            raise IndexError("cannot reduce an empty sequence")
        return empty()
    while len(level) > 1:
        level = [
            combine(level[index], level[index + 1])
            if index + 1 < len(level)
            else level[index]
            for index in range(0, len(level), 2)
        ]
    return level[0]

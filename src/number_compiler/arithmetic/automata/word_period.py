"""Linear equality-based period searches on an already available finite word.

The result describes only the supplied word. It grants no authority to extend
a source beyond that word, and never generates source symbols itself.
"""

from __future__ import annotations

from collections.abc import Sequence


def _prefix_matches(values: Sequence[object]) -> tuple[list[int], int]:
    """Z lengths and the number of actual symbol equality comparisons."""
    size = len(values)
    matches = [0] * size
    left = right = comparisons = 0
    for position in range(1, size):
        if position < right:
            matches[position] = min(right - position, matches[position - left])
        while position + matches[position] < size:
            comparisons += 1
            if values[matches[position]] != values[position + matches[position]]:
                break
            matches[position] += 1
        endpoint = position + matches[position]
        if endpoint > right:
            left, right = position, endpoint
    return matches, comparisons


def primitive_period(values: Sequence[object]) -> tuple[int, int]:
    """Return the shortest exact tiling period and charged comparisons.

    Empty words have period zero. A nonempty word without a smaller tiling
    period has its own length as period.
    """
    size = len(values)
    matches, comparisons = _prefix_matches(values)
    for period in range(1, size):
        if size % period == 0 and matches[period] == size - period:
            return period, comparisons
    return size, comparisons


def finite_suffix_period(
    values: Sequence[object], *, min_repeats: int = 3
) -> tuple[tuple[int, int] | None, int]:
    """Return (earliest start, smallest period) and charged comparisons.

    Period takes precedence over start, matching a period-first exhaustive
    search. The suffix can finish partway through its final repeated motif,
    but must contain at least ``min_repeats`` complete periods.

    On the reversed word, Z[p] is the longest equality run between a suffix
    and its shift by p. Thus n-p-Z[p] is the earliest p-periodic suffix start.
    """
    if type(min_repeats) is not int or min_repeats < 2:
        raise ValueError("finite suffix search requires at least two repeats")
    size = len(values)
    matches, comparisons = _prefix_matches(tuple(reversed(values)))
    for period in range(1, size // min_repeats + 1):
        extent = period + matches[period]
        if extent >= min_repeats * period:
            return (size - extent, period), comparisons
    return None, comparisons

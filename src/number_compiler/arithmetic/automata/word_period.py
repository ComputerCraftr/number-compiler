"""Linear equality-based period searches on an already available finite word.

The result describes only the supplied word. It grants no authority to extend
a source beyond that word, and never generates source symbols itself.
"""

from __future__ import annotations

from collections.abc import Callable, Sequence
from typing import Protocol, Self, TypeVar


class _Ordered(Protocol):
    def __lt__(self, other: Self, /) -> bool: ...


class _HashableOrdered(_Ordered, Protocol):
    def __hash__(self) -> int: ...


_OrderedItem = TypeVar("_OrderedItem", bound=_Ordered)
_GuardKey = TypeVar("_GuardKey", bound=_HashableOrdered)
_Port = TypeVar("_Port")


def least_rotation_index(values: Sequence[_OrderedItem]) -> int:
    """Return the first least rotation using a linear number of comparisons."""
    size = len(values)
    if not size:
        raise ValueError("cannot rotate an empty word")
    first, second, matched = 0, 1, 0
    while first < size and second < size and matched < size:
        left = values[(first + matched) % size]
        right = values[(second + matched) % size]
        if left == right:
            matched += 1
            continue
        if left < right:
            second += matched + 1
            if second == first:
                second += 1
        else:
            first += matched + 1
            if first == second:
                first += 1
        matched = 0
    return min(first, second)


def _rotation_entry_phase(offset: int, period: int) -> int:
    return (-offset) % period


def canonical_primitive_text_rotation(word: str) -> tuple[str, int, int]:
    """Canonicalize a primitive text word whose symbols are complete ports."""
    if type(word) is not str or not word:
        raise ValueError("cannot rotate an empty text word")
    period, comparisons = primitive_period(word)
    primitive = word[:period]
    offset = least_rotation_index(primitive)
    return (
        primitive[offset:] + primitive[:offset],
        _rotation_entry_phase(offset, period),
        comparisons,
    )


def canonical_primitive_rotation(
    values: Sequence[_Port], *, guard_key: Callable[[_Port], _GuardKey]
) -> tuple[tuple[_Port, ...], int, int]:
    """Canonicalize a complete guarded word and preserve its physical entry.

    The phase locates the original first port in the canonical primitive word.
    The key describes the complete guarded port, including its transition and
    output distinctions. Source and repetition checks remain with the issuer.
    """
    if not values:
        raise ValueError("cannot rotate an empty word")
    ports = tuple(values)
    period, comparisons = primitive_period(ports)
    primitive = ports[:period]
    keys = tuple(guard_key(port) for port in primitive)
    represented: dict[_GuardKey, _Port] = {}
    for key, port in zip(keys, primitive, strict=True):
        if key in represented and represented[key] != port:
            raise ValueError("guard key does not distinguish complete ports")
        represented[key] = port
    offset = least_rotation_index(keys)
    return (
        primitive[offset:] + primitive[:offset],
        _rotation_entry_phase(offset, period),
        comparisons,
    )


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

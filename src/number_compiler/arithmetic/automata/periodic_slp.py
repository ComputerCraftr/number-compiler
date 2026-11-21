"""Compile an explicitly supplied periodic word into an existing SLP arena."""

from __future__ import annotations

from collections.abc import Sequence
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from number_compiler.arithmetic.automata.slp import SLPArena


def periodic_word(
    arena: SLPArena, period: Sequence[int], count: int, *, phase: int = 0
) -> int:
    """Build ``count`` ordered symbols; the caller authenticates periodicity."""
    if not period:
        raise ValueError("periodic SLP needs a nonempty period")
    if type(count) is not int or count < 0:
        raise ValueError("periodic SLP length must be nonnegative")
    if type(phase) is not int:
        raise TypeError("periodic SLP phase must be an integer")
    if not count:
        return arena.empty_id
    if len(period) == 1:
        return arena.repeat(arena.terminal(period[0]), count)
    offset = phase % len(period)
    first = min(count, len(period) - offset) if offset else 0
    parts: list[int] = []
    if first:
        parts.append(arena.word(period[offset : offset + first]))
    copies, tail = divmod(count - first, len(period))
    if copies:
        parts.append(arena.repeat(arena.word(period), copies))
    if tail:
        parts.append(arena.word(period[:tail]))
    return arena.concat_many(parts)

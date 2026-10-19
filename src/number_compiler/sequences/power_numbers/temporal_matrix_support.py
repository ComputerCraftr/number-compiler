"""Small shared helpers for source-bound power-number matrix observations."""

from __future__ import annotations

from typing import Protocol, TypeVar


class _Ticked(Protocol):
    @property
    def tick(self) -> int: ...


_Puncture = TypeVar("_Puncture", bound=_Ticked)


def dyadic_puncture_offsets(steps: int) -> tuple[int, ...]:
    """Return unique endpoints and dyadic interior checks for a bounded span."""
    if type(steps) is not int or steps < 1:
        raise ValueError("matrix span must be a positive integer")
    offsets = {0, steps}
    tick = 1
    while tick < steps:
        offsets.add(tick)
        tick <<= 1
    return tuple(sorted(offsets))


def join_puncture_provenance(
    first: tuple[_Puncture, ...],
    later: tuple[_Puncture, ...],
    *,
    first_offset: int,
    total_steps: int,
) -> tuple[_Puncture, ...]:
    """Join authenticated punctures, retaining compact dyadic checkpoints.

    The shared seam must already have been validated by the action owner.
    If both child summaries contain every canonical parent dyadic checkpoint,
    retain only those checkpoints. Otherwise preserve the full child union as
    provenance; never invent a puncture by replaying the source action.
    """
    if (
        type(first) is not tuple
        or not first
        or type(later) is not tuple
        or not later
        or type(first_offset) is not int
        or first_offset < 0
        or type(total_steps) is not int
        or total_steps < 1
    ):
        raise ValueError("invalid child puncture summaries")
    first_ticks = tuple(point.tick for point in first)
    later_ticks = tuple(point.tick for point in later)
    if (
        any(type(tick) is not int for tick in first_ticks + later_ticks)
        or first_ticks != tuple(sorted(set(first_ticks)))
        or later_ticks != tuple(sorted(set(later_ticks)))
        or first_ticks[0] != first_offset
        or first_ticks[-1] != later_ticks[0]
        or later_ticks[-1] != first_offset + total_steps
    ):
        raise ValueError("child puncture clocks are not adjacent and ordered")
    joined = first + later[1:]
    by_tick = {point.tick: point for point in joined}
    target_ticks = tuple(
        first_offset + offset for offset in dyadic_puncture_offsets(total_steps)
    )
    if all(tick in by_tick for tick in target_ticks):
        return tuple(by_tick[tick] for tick in target_ticks)
    return joined


__all__ = ("dyadic_puncture_offsets", "join_puncture_provenance")

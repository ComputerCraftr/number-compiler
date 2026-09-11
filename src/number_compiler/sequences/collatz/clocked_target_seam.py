"""Canonical publication seam for completed accelerated Collatz targets."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.sequences.collatz.inverse_three_clock import InverseThreeClock


@dataclass(frozen=True, slots=True)
class ClockedTargetSeam:
    """Exact target payload and exact accelerated tick after a consumed action."""

    accelerated_tick: int
    target: int

    def __post_init__(self) -> None:
        if any(
            type(value) is not int for value in (self.accelerated_tick, self.target)
        ):
            raise TypeError("clocked target seam fields require exact integers")
        if self.accelerated_tick < 0 or self.target <= 0 or not self.target & 1:
            raise ValueError(self)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("collatz-clocked-target-seam", self.accelerated_tick, self.target)

    def clock(self, precision: int) -> InverseThreeClock:
        """Project the exact tick only when a finite spatial view is demanded."""
        return InverseThreeClock(precision, self.accelerated_tick)


class ClockedTargetSeamArena:
    """Intern completed targets after all transition provenance is consumed."""

    def __init__(self, *, max_entries: int = 65_536) -> None:
        if type(max_entries) is not int or max_entries <= 0:
            raise ValueError("clocked target seam budget must be a positive integer")
        self.max_entries = max_entries
        self._seams: dict[tuple[object, ...], ClockedTargetSeam] = {}
        self.requests = 0
        self.cache_hits = 0

    def publish(self, *, accelerated_tick: int, target: int) -> ClockedTargetSeam:
        self.requests += 1
        candidate = ClockedTargetSeam(accelerated_tick, target)
        found = self._seams.get(candidate.canonical_key)
        if found is not None:
            self.cache_hits += 1
            return found
        if len(self._seams) >= self.max_entries:
            raise ValueError("clocked target seam budget exceeded")
        self._seams[candidate.canonical_key] = candidate
        return candidate

    @property
    def retained_seams(self) -> int:
        return len(self._seams)


__all__ = ["ClockedTargetSeam", "ClockedTargetSeamArena"]

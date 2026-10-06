"""Source-independent temporal weights shared by family adapters."""

from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True, slots=True)
class TemporalCocycle:
    physical_ticks: int = 0
    event_weight: int = 0
    frame_shift: int = 0

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (
                self.physical_ticks,
                self.event_weight,
                self.frame_shift,
            )
        ):
            raise TypeError("temporal cocycles require exact integers")
        if self.physical_ticks < 0 or self.event_weight < 0:
            raise ValueError("temporal cocycle weights cannot be negative")


__all__ = ["TemporalCocycle"]

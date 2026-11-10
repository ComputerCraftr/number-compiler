"""Successor-sum and predecessor fields for one bounded dyadic window."""

from __future__ import annotations

from dataclasses import dataclass
from typing import NamedTuple


class FieldWindowPrefixState(NamedTuple):
    steps: int
    gain: int
    offset: int
    sum_gain: int
    sum_offset: int
    previous_gain: int
    previous_offset: int
    odd_symbols: int


class EndpointWindowPrefixState(NamedTuple):
    steps: int
    gain: int
    offset: int
    odd_symbols: int


@dataclass(slots=True)
class WindowFieldAccumulator:
    sum_gain: int = 0
    sum_offset: int = 0
    previous_gain: int = 0
    previous_offset: int = 0

    def advance(
        self,
        previous_gain: int,
        previous_offset: int,
        gain: int,
        offset: int,
    ) -> int:
        """Advance one issued normalized symbol and report operand work."""
        old_values = (
            self.sum_gain,
            self.sum_offset,
            self.previous_gain,
            self.previous_offset,
        )
        self.previous_gain = previous_gain
        self.previous_offset = previous_offset
        self.sum_gain = (self.sum_gain << 1) + gain
        self.sum_offset = (self.sum_offset << 1) + offset
        return sum(value.bit_length() for value in old_values) + sum(
            value.bit_length()
            for value in (
                self.sum_gain,
                self.sum_offset,
                self.previous_gain,
                self.previous_offset,
            )
        )

    def prefix_state(
        self, steps: int, gain: int, offset: int, odd_symbols: int
    ) -> FieldWindowPrefixState:
        """Freeze the action's optional same-pass checkpoint fields."""
        return FieldWindowPrefixState(
            steps,
            gain,
            offset,
            self.sum_gain,
            self.sum_offset,
            self.previous_gain,
            self.previous_offset,
            odd_symbols,
        )


__all__ = [
    "EndpointWindowPrefixState",
    "FieldWindowPrefixState",
    "WindowFieldAccumulator",
]

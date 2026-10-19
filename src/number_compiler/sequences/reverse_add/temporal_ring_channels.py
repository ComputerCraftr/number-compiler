"""Typed output channels for finite reverse/add temporal rings.

The five decimal pair bands are owned by the arithmetic partition. This
family-owned enum supplies only the additional temporal outputs. Values are
wire spellings; they are never parsed back into an execution channel.
"""

from __future__ import annotations

from enum import Enum
from typing import Protocol, TypeAlias

from number_compiler.arithmetic.fields.decimal_pair_partition import (
    DECIMAL_PAIR_BANDS,
    DecimalPairBand,
)


class ReverseTemporalRingChannel(Enum):
    """Additional reverse/add ring outputs beyond the five pair bands."""

    F5 = "f5"
    LOW_CARRY = "low_carry"
    REFLECTED_CARRY = "reflected_carry"
    RAW_BORROW = "raw_borrow"
    CARRY_XOR = "carry_xor"
    CARRY_BORROW_XOR = "carry_borrow_xor"
    LOW_BIRTH = "low_birth"
    LOW_DEATH = "low_death"
    HIGH_BIRTH = "high_birth"
    HIGH_DEATH = "high_death"


TemporalRingChannel: TypeAlias = DecimalPairBand | ReverseTemporalRingChannel

TEMPORAL_RING_CHANNELS: tuple[TemporalRingChannel, ...] = (
    *DECIMAL_PAIR_BANDS,
    *tuple(ReverseTemporalRingChannel),
)

TEMPORAL_RING_BOOLEAN_CHANNELS: tuple[TemporalRingChannel, ...] = (
    *DECIMAL_PAIR_BANDS,
    ReverseTemporalRingChannel.CARRY_XOR,
    ReverseTemporalRingChannel.CARRY_BORROW_XOR,
    ReverseTemporalRingChannel.LOW_BIRTH,
    ReverseTemporalRingChannel.LOW_DEATH,
    ReverseTemporalRingChannel.HIGH_BIRTH,
    ReverseTemporalRingChannel.HIGH_DEATH,
)


class InwardOrbitView(Protocol):
    """Exact correlated output rows retained by an inward orbit."""

    @property
    def pair_f5(self) -> tuple[tuple[int, ...], ...]: ...

    @property
    def low_carries(self) -> tuple[tuple[int, ...], ...]: ...

    @property
    def reflected_carries(self) -> tuple[tuple[int, ...], ...]: ...

    @property
    def raw_innovation_borrow(self) -> tuple[tuple[int, ...], ...]: ...

    @property
    def reflected_xor(self) -> tuple[tuple[int, ...], ...]: ...

    @property
    def carry_borrow_xor(self) -> tuple[tuple[int, ...], ...]: ...

    @property
    def low_birth(self) -> tuple[tuple[int, ...], ...]: ...

    @property
    def low_death(self) -> tuple[tuple[int, ...], ...]: ...

    @property
    def reflected_birth(self) -> tuple[tuple[int, ...], ...]: ...

    @property
    def reflected_death(self) -> tuple[tuple[int, ...], ...]: ...

    @property
    def selected_bands(self) -> tuple[tuple[DecimalPairBand, ...], ...]: ...


def ring_channel_wire_name(channel: TemporalRingChannel) -> str:
    """Return the stable observation spelling for a validated typed channel."""
    if type(channel) is DecimalPairBand:
        return channel.value
    if type(channel) is ReverseTemporalRingChannel:
        return channel.value
    raise TypeError("temporal ring channels must use their typed identity")


def checked_temporal_ring_channel(value: object) -> TemporalRingChannel:
    """Validate a channel arriving through an untyped runtime boundary."""
    if type(value) is DecimalPairBand:
        return value
    if type(value) is ReverseTemporalRingChannel:
        return value
    raise TypeError("temporal ring channel requires a typed identity")


def ring_channel_lanes(
    orbit: InwardOrbitView, channel: TemporalRingChannel
) -> tuple[int | None, ...]:
    """Project one channel to its forced finite lanes without string dispatch."""
    if type(channel) is DecimalPairBand:
        projected: list[int | None] = []
        for row in orbit.selected_bands:
            values = {int(channel is band) for band in row}
            projected.append(next(iter(values)) if len(values) == 1 else None)
        return tuple(projected)
    if type(channel) is not ReverseTemporalRingChannel:
        raise TypeError("temporal ring channels must use their typed identity")
    match channel:
        case ReverseTemporalRingChannel.F5:
            rows = orbit.pair_f5
        case ReverseTemporalRingChannel.LOW_CARRY:
            rows = orbit.low_carries
        case ReverseTemporalRingChannel.REFLECTED_CARRY:
            rows = orbit.reflected_carries
        case ReverseTemporalRingChannel.RAW_BORROW:
            rows = orbit.raw_innovation_borrow
        case ReverseTemporalRingChannel.CARRY_XOR:
            rows = orbit.reflected_xor
        case ReverseTemporalRingChannel.CARRY_BORROW_XOR:
            rows = orbit.carry_borrow_xor
        case ReverseTemporalRingChannel.LOW_BIRTH:
            rows = orbit.low_birth
        case ReverseTemporalRingChannel.LOW_DEATH:
            rows = orbit.low_death
        case ReverseTemporalRingChannel.HIGH_BIRTH:
            rows = orbit.reflected_birth
        case ReverseTemporalRingChannel.HIGH_DEATH:
            rows = orbit.reflected_death
    return tuple(row[0] if len(row) == 1 else None for row in rows)


__all__ = [
    "ReverseTemporalRingChannel",
    "TEMPORAL_RING_BOOLEAN_CHANNELS",
    "TEMPORAL_RING_CHANNELS",
    "TemporalRingChannel",
    "checked_temporal_ring_channel",
    "ring_channel_lanes",
    "ring_channel_wire_name",
]

"""Canonical five-band projection of a decimal symmetric pair sum.

This is the five-observation partition used by bank projections.  It is not
the reverse/add seven-band successor partition, and it carries no temporal,
carry, or source authority by itself.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final


class DecimalPairBand(Enum):
    """Typed identity for one of the five decimal pair observation bands."""

    LT_LOW = "lt_low"
    LT_HIGH = "lt_high"
    EQ = "eq"
    GT_LOW = "gt_low"
    GT_HIGH = "gt_high"


DECIMAL_PAIR_BANDS = tuple(DecimalPairBand)
DECIMAL_PAIR_BAND_NAMES = tuple(band.value for band in DECIMAL_PAIR_BANDS)
_DECIMAL_PAIR_BAND_ENDS: Final[tuple[int, ...]] = (4, 8, 9, 14, 18)
_DECIMAL_PAIR_BAND_MEMBERS: Final[tuple[tuple[int, ...], ...]] = tuple(
    tuple(range(start, end + 1))
    for start, end in zip(
        (0, *(previous + 1 for previous in _DECIMAL_PAIR_BAND_ENDS[:-1])),
        _DECIMAL_PAIR_BAND_ENDS,
        strict=True,
    )
)


def decimal_pair_band_members(band: DecimalPairBand) -> tuple[int, ...]:
    """Return the canonical coefficient members of one five-band class."""
    if type(band) is not DecimalPairBand:
        raise TypeError("pair-band membership requires a DecimalPairBand")
    return _DECIMAL_PAIR_BAND_MEMBERS[DECIMAL_PAIR_BANDS.index(band)]


@dataclass(frozen=True, slots=True)
class DecimalPairPartition:
    """Exact residue and one-hot five-band projection for a pair sum."""

    band: DecimalPairBand
    f5: int
    masks: tuple[int, int, int, int, int]

    def mask(self, band: DecimalPairBand) -> int:
        if type(band) is not DecimalPairBand:
            raise TypeError("pair-band selection requires a DecimalPairBand")
        return self.masks[DECIMAL_PAIR_BANDS.index(band)]


@dataclass(frozen=True, slots=True)
class DecimalPairWordProjection:
    """Aligned five-band and F5 observations for a validated pair word."""

    bands: tuple[
        tuple[int, ...],
        tuple[int, ...],
        tuple[int, ...],
        tuple[int, ...],
        tuple[int, ...],
    ]
    f5: tuple[int, ...]

    def band(self, band: DecimalPairBand) -> tuple[int, ...]:
        if type(band) is not DecimalPairBand:
            raise TypeError("pair-band selection requires a DecimalPairBand")
        return self.bands[DECIMAL_PAIR_BANDS.index(band)]

    def wire_channels(self) -> dict[str, tuple[int, ...]]:
        """Serialize typed bands using the established observation spellings."""
        channels = {
            band.value: self.bands[index]
            for index, band in enumerate(DECIMAL_PAIR_BANDS)
        }
        channels["f5"] = self.f5
        return channels


def decimal_pair_partition(pair_sum: int) -> DecimalPairPartition:
    """Classify one admitted exact decimal pair sum without string dispatch."""
    band = decimal_pair_band(pair_sum)
    masks = (
        int(band is DecimalPairBand.LT_LOW),
        int(band is DecimalPairBand.LT_HIGH),
        int(band is DecimalPairBand.EQ),
        int(band is DecimalPairBand.GT_LOW),
        int(band is DecimalPairBand.GT_HIGH),
    )
    return DecimalPairPartition(band, pair_sum % 5, masks)


def decimal_pair_band(pair_sum: object) -> DecimalPairBand:
    """Return only the typed band, avoiding allocation of a projection record."""
    if type(pair_sum) is not int or not 0 <= pair_sum <= 18:
        raise ValueError("pair coefficient must be in radix-19 alphabet")
    if pair_sum <= _DECIMAL_PAIR_BAND_ENDS[0]:
        return DecimalPairBand.LT_LOW
    if pair_sum <= _DECIMAL_PAIR_BAND_ENDS[1]:
        return DecimalPairBand.LT_HIGH
    if pair_sum == _DECIMAL_PAIR_BAND_ENDS[2]:
        return DecimalPairBand.EQ
    if pair_sum <= _DECIMAL_PAIR_BAND_ENDS[3]:
        return DecimalPairBand.GT_LOW
    return DecimalPairBand.GT_HIGH


def decimal_pair_word_projection(
    pair_word: tuple[int, ...],
) -> DecimalPairWordProjection:
    """Project aligned five-band masks and F5 residues from an exact pair word."""
    lt_low: list[int] = []
    lt_high: list[int] = []
    eq: list[int] = []
    gt_low: list[int] = []
    gt_high: list[int] = []
    f5: list[int] = []
    for pair_sum in pair_word:
        band = decimal_pair_band(pair_sum)
        lt_low.append(int(band is DecimalPairBand.LT_LOW))
        lt_high.append(int(band is DecimalPairBand.LT_HIGH))
        eq.append(int(band is DecimalPairBand.EQ))
        gt_low.append(int(band is DecimalPairBand.GT_LOW))
        gt_high.append(int(band is DecimalPairBand.GT_HIGH))
        f5.append(pair_sum % 5)
    return DecimalPairWordProjection(
        (tuple(lt_low), tuple(lt_high), tuple(eq), tuple(gt_low), tuple(gt_high)),
        tuple(f5),
    )


__all__ = [
    "DECIMAL_PAIR_BANDS",
    "DECIMAL_PAIR_BAND_NAMES",
    "DecimalPairBand",
    "DecimalPairPartition",
    "DecimalPairWordProjection",
    "decimal_pair_band",
    "decimal_pair_band_members",
    "decimal_pair_partition",
    "decimal_pair_word_projection",
]

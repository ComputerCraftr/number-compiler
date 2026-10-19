"""The shared decimal pair projection has one exact typed partition."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.fields.decimal_pair_partition import (
    DECIMAL_PAIR_BAND_NAMES,
    DECIMAL_PAIR_BANDS,
    DecimalPairBand,
    decimal_pair_band,
    decimal_pair_band_members,
    decimal_pair_partition,
    decimal_pair_word_projection,
)


def test_every_pair_sum_has_the_exact_band_and_f5_projection() -> None:
    expected = (
        DecimalPairBand.LT_LOW,
        DecimalPairBand.LT_LOW,
        DecimalPairBand.LT_LOW,
        DecimalPairBand.LT_LOW,
        DecimalPairBand.LT_LOW,
        DecimalPairBand.LT_HIGH,
        DecimalPairBand.LT_HIGH,
        DecimalPairBand.LT_HIGH,
        DecimalPairBand.LT_HIGH,
        DecimalPairBand.EQ,
        DecimalPairBand.GT_LOW,
        DecimalPairBand.GT_LOW,
        DecimalPairBand.GT_LOW,
        DecimalPairBand.GT_LOW,
        DecimalPairBand.GT_LOW,
        DecimalPairBand.GT_HIGH,
        DecimalPairBand.GT_HIGH,
        DecimalPairBand.GT_HIGH,
        DecimalPairBand.GT_HIGH,
    )
    assert DECIMAL_PAIR_BANDS == (
        DecimalPairBand.LT_LOW,
        DecimalPairBand.LT_HIGH,
        DecimalPairBand.EQ,
        DecimalPairBand.GT_LOW,
        DecimalPairBand.GT_HIGH,
    )
    assert DECIMAL_PAIR_BAND_NAMES == tuple(band.value for band in DECIMAL_PAIR_BANDS)
    assert tuple(decimal_pair_band(value) for value in range(19)) == expected
    members = tuple(decimal_pair_band_members(band) for band in DECIMAL_PAIR_BANDS)
    assert members == (
        (0, 1, 2, 3, 4),
        (5, 6, 7, 8),
        (9,),
        (10, 11, 12, 13, 14),
        (15, 16, 17, 18),
    )
    assert tuple(value for group in members for value in group) == tuple(range(19))
    for value, band in enumerate(expected):
        partition = decimal_pair_partition(value)
        assert partition.band is band
        assert partition.f5 == value % 5
        assert sum(partition.masks) == 1
        assert partition.mask(band) == 1


def test_word_projection_preserves_wire_names_from_typed_bands() -> None:
    projection = decimal_pair_word_projection((0, 4, 5, 8, 9, 14, 15, 18))
    assert projection.wire_channels() == {
        "lt_low": (1, 1, 0, 0, 0, 0, 0, 0),
        "lt_high": (0, 0, 1, 1, 0, 0, 0, 0),
        "eq": (0, 0, 0, 0, 1, 0, 0, 0),
        "gt_low": (0, 0, 0, 0, 0, 1, 0, 0),
        "gt_high": (0, 0, 0, 0, 0, 0, 1, 1),
        "f5": (0, 4, 0, 3, 4, 4, 0, 3),
    }
    assert projection.band(DecimalPairBand.EQ) == (0, 0, 0, 0, 1, 0, 0, 0)


@pytest.mark.parametrize("value", (True, False, -1, 19, 1.0))
def test_pair_projection_rejects_non_admitted_values(value: object) -> None:
    with pytest.raises(ValueError):
        decimal_pair_band(value)

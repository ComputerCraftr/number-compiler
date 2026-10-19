"""Independent character-sum oracle for the signed Boolean observation."""

import pytest

from number_compiler.arithmetic.fields.walsh import walsh64_signed


@pytest.mark.parametrize(
    "mask",
    (0, (1 << 64) - 1, 0xAAAAAAAAAAAAAAAA, 0x0123456789ABCDEF)
    + tuple(1 << index for index in range(64)),
)
def test_signed_walsh_matches_character_sum(mask: int) -> None:
    expected = tuple(
        sum(
            (-1 if (mask >> position) & 1 else 1)
            * (-1 if (frequency & position).bit_count() & 1 else 1)
            for position in range(64)
        )
        for frequency in range(64)
    )
    assert walsh64_signed(mask) == expected


@pytest.mark.parametrize("mask", (-1, 1 << 64, True))
def test_signed_walsh_retains_exact_bounded_input_admission(mask: int) -> None:
    with pytest.raises(ValueError):
        walsh64_signed(mask)

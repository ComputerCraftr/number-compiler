"""Exhaustive decimal arithmetic checks for the shared reflected cell law."""

import pytest

from number_compiler.arithmetic.carry.reflected_h_power import (
    padded_h_cell,
    padded_h_kernel,
)

pytestmark = pytest.mark.validation


@pytest.mark.parametrize("multiplier", (2, 5))
def test_every_ordered_reflected_neighborhood(multiplier: int) -> None:
    compiled = padded_h_kernel(multiplier)
    for previous in range(100):
        for current in range(100):
            ordinary = multiplier * (100 * current + previous)
            carry_from_tens = multiplier * (ordinary // 10 % 10)
            carry_from_hundreds = multiplier * (ordinary // 100 % 10)
            carry_from_thousands = multiplier * (ordinary // 1000 % 10)
            low = carry_from_hundreds // 10 + carry_from_tens % 10
            high = carry_from_thousands // 10 + carry_from_hundreds % 10
            expected = 10 * high + low
            assert padded_h_cell(previous, current, multiplier) == expected
            assert compiled(previous, current) == expected

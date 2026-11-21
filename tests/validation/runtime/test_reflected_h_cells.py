"""Exhaustive local check of both padded reflected carry rules."""

import pytest

from number_compiler.arithmetic.carry.reflected_h_power import (
    padded_h_cell,
    padded_h_kernel,
)


@pytest.mark.parametrize("multiplier", (2, 5))
def test_all_padded_base100_cells_match_integer_arithmetic(multiplier: int) -> None:
    compiled = padded_h_kernel(multiplier)
    for previous in range(100):
        for current in range(100):
            product = multiplier * (previous + 100 * current)
            previous_digit = 0
            reflected = 0
            place = 1
            for _ in range(5):
                product, digit = divmod(product, 10)
                reflected += (
                    multiplier * digit // 10 + multiplier * previous_digit % 10
                ) * place
                previous_digit = digit
                place *= 10
            expected = reflected // 100 % 100
            assert padded_h_cell(previous, current, multiplier) == expected
            assert compiled(previous, current) == expected

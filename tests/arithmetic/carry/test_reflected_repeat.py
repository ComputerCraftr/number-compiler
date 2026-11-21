"""Check carry-sheet labels against independent decimal multiplication."""

import pytest

from number_compiler.arithmetic.carry.reflected_repeat import repeated_input_digit


@pytest.mark.parametrize("multiplier", (2, 5))
def test_carry_sheet_repeat_matches_decimal_digit(multiplier: int) -> None:
    for digit in range(10):
        for incoming in range(multiplier):
            expected = (multiplier * digit + incoming) % 10 == digit
            assert repeated_input_digit(multiplier, digit, incoming) == expected


def test_carry_sheet_repeat_rejects_boolean_carry() -> None:
    with pytest.raises(ValueError, match="incoming carry"):
        repeated_input_digit(2, 0, False)

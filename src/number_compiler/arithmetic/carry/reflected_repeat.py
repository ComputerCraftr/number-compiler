"""Repeat predicates for aligned decimal multiplication carry sheets."""

from __future__ import annotations


def repeated_input_digit(multiplier: int, digit: int, incoming: int) -> bool:
    """Decide whether a decimal input digit repeats in the multiplication frame.

    ``incoming`` is the preceding multiplication carry. Physical coordinates
    of a reflected source require a separate reversal before comparison.
    """
    if type(multiplier) is not int or multiplier not in (2, 5):
        raise ValueError("multiplier must be 2 or 5")
    if type(digit) is not int or not 0 <= digit <= 9:
        raise ValueError("digit must be decimal")
    if type(incoming) is not int or not 0 <= incoming < multiplier:
        raise ValueError("incoming carry is outside the multiplier alphabet")
    quotient, remainder = divmod(digit, 10 // multiplier)
    output_half = (multiplier * remainder + incoming) // 2
    if multiplier == 5:
        return quotient == output_half and incoming % 2 == 0
    return (quotient == 0 and incoming == 0 and output_half == 0) or (
        quotient == 1 and incoming == 1 and output_half == 4
    )

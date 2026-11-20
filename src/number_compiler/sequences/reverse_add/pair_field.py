"""Original-source symmetric pair encoding for reverse/add."""

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.radix import digits_lsd


def pair_field_from_integer(value: int, base: int) -> tuple[int, ...]:
    """Encode an original nonnegative seed as symmetric digit sums."""

    value = require_integer(value, "seed", 0)
    base = require_integer(base, "base", 2)
    return pair_field_from_digits(digits_lsd(value, base))


def pair_field_from_digits(digits: tuple[int, ...]) -> tuple[int, ...]:
    if type(digits) is not tuple or not digits:
        raise ValueError("reverse pair source requires original digits")
    return tuple(digits[index] + digits[-index - 1] for index in range(len(digits)))

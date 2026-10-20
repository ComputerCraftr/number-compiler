"""Bounded public regressions alongside the separate exhaustive orbit matrix."""

import pytest

from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


@pytest.mark.parametrize("base", (2, 3, 4, 5, 10))
def test_small_public_reverse_point_width_and_lowering(base: int) -> None:
    seed = base * base + base - 1
    expected = seed
    for _ in range(3):
        remaining, reflected = expected, 0
        while remaining:
            remaining, digit = divmod(remaining, base)
            reflected = reflected * base + digit
        expected += reflected
    digits: list[int] = []
    remaining = expected
    while remaining:
        remaining, digit = divmod(remaining, base)
        digits.append(digit)

    term = ReverseAddPoweredTerm(seed, 3, base=base)
    assert [term.digit(i) for i in range(len(digits))] == digits
    assert term.width() == len(digits)
    assert term.materialize(max_bits=1000) == expected

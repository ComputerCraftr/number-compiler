"""Ordered source carries, not phase counts, feed the next spatial layer."""

import pytest

from number_compiler.arithmetic.fields.ordered_tripling_carry import (
    OrderedTriplingCarry,
)


@pytest.mark.parametrize("base", [2, 5, 7, 10, 11])
def test_ordered_carry_matches_literal_and_conditional_source(base: int) -> None:
    for position in (0, 1, 3):
        program = OrderedTriplingCarry(base, position, 17, 9)
        boundary = base**position
        literal = 3**17
        conditional = [d * boundary + literal % boundary for d in range(base)]
        for offset in range(9):
            sample = program.sample(offset)
            assert sample.digit == literal // boundary % base
            assert sample.incoming == 3 * (literal % boundary) // boundary
            assert sample.outgoing == 3 * (literal % (base * boundary)) // (
                base * boundary
            )
            assert sample.successor_digit == 3 * literal // boundary % base
            for digit, value in enumerate(conditional):
                row = program.conditional_sample(digit, offset)
                assert row.digit == value // boundary % base
                assert row.outgoing == 3 * (value % (base * boundary)) // (
                    base * boundary
                )
                conditional[digit] *= 3
            literal *= 3


def test_ordered_carry_split_and_large_period_repeat() -> None:
    source = OrderedTriplingCarry(10, 8, 21, 10**12)
    left, right = source.split(10**11 + 7)
    assert left.duration + right.duration == source.duration
    assert right.sample(0) == source.sample(left.duration)
    repeats, tail = source.cycle_decomposition
    assert repeats * source.period + tail == source.duration
    assert source.sample(source.period) == source.sample(0)
    assert (
        OrderedTriplingCarry.at_dyadic_phase(10, 2, 15, 4).sample(0).digit
        == pow(3, 2**15, 1000) // 100
    )
    carries = [
        tuple(
            OrderedTriplingCarry.at_dyadic_phase(10, 2, level, 4).sample(i).outgoing
            for i in range(4)
        )
        for level in (15, 31)
    ]
    assert carries == [(2, 0, 2, 1), (1, 0, 0, 2)]


@pytest.mark.parametrize(
    "args", [(True, 0, 0, 1), (10, 64, 0, 1), (10, 0, -1, 1), (10, 0, 0, -1)]
)
def test_ordered_carry_rejects_invalid_boundaries(
    args: tuple[int, int, int, int],
) -> None:
    with pytest.raises(ValueError):
        OrderedTriplingCarry(*args)

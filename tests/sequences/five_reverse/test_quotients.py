from __future__ import annotations

import pytest

from number_compiler.sequences.five_reverse.quotients import (
    MovingCutBudgetExceeded,
    digit_field225,
    h_power_mod,
    physical_low_band_from_h,
)


def _reverse10(value: int) -> int:
    return int(str(value)[::-1])


def _digit_field(value: int) -> int:
    return int("".join(str(5 * int(digit)) for digit in str(value)))


def _h(value: int) -> int:
    parity: int = sum(
        (digit & 1) * 10**index for index, digit in enumerate(_digits(value))
    )
    return (value + 99 * parity) // 2


def _digits(value: int) -> tuple[int, ...]:
    return tuple(int(digit) for digit in str(value)[::-1])


def test_mod225_field_power_matches_independent_physical_recurrence() -> None:
    for seed in range(1, 50):
        value = seed
        for generation in range(9):
            state = digit_field225(seed, generation)
            assert state.residue == _digit_field(value) % 225
            next_value = 5 * _reverse10(value)
            assert (
                state.next_mod1125(leading_source_digit=int(str(value)[0]))
                == _digit_field(next_value) % 1125
            )
            value = next_value


def test_mod225_field_successor_and_power_are_compositional() -> None:
    state = digit_field225(196, 37)
    assert state.successor() == digit_field225(196, 38)
    assert state.power(29) == digit_field225(196, 66)
    assert digit_field225(196, 0).residue == 80


def test_h_fixed_precision_power_matches_integer_operator() -> None:
    for source in range(1, 80):
        value = source
        for exponent in range(10):
            for places in range(1, 6):
                assert h_power_mod(source, exponent, places) == value % 10**places
            value = _h(5 * value)


@pytest.mark.parametrize("generation", range(1, 32))
def test_moving_cut_matches_exact_physical_low_band(generation: int) -> None:
    value = 196
    for _ in range(generation):
        value = 5 * _reverse10(value)
    assert physical_low_band_from_h(196, generation, 4) == value % 10_000


def test_moving_cut_refuses_when_precision_budget_is_insufficient() -> None:
    with pytest.raises(MovingCutBudgetExceeded):
        physical_low_band_from_h(196, 511, 4, max_places=8)

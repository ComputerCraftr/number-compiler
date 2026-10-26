"""Raw ×15 clock arithmetic remains symbolic until explicitly demanded."""

import pytest

from number_compiler.arithmetic.carry.fifteen_radix_clock import (
    PowerOfTwoAffineTotal,
    fifteen_raw_power_clock,
)


@pytest.mark.parametrize(
    ("source", "depth", "period_exponent", "carry_total"),
    [
        (4, 1, 0, 0),
        (2, 3, 1, 14),
        (1, 4, 1, 14),
        (125, 5, 1, 7),
        (1, 5, 1, 21),
        (1, 6, 2, 35),
        (1, 7, 3, 49),
        (1, 8, 4, 105),
    ],
)
def test_small_raw_fifteen_period_and_carry_total_cases(
    source: int, depth: int, period_exponent: int, carry_total: int
) -> None:
    clock = fifteen_raw_power_clock(source, depth)
    period: int = 1 << period_exponent
    modulus: int = pow(10, depth)
    state: int = pow(15, clock.first_stable_exponent, modulus) * source % modulus
    reference_total: int = 0
    for _ in range(period):
        reference_total += 15 * state // modulus
        state = 15 * state % modulus

    assert clock.period_power_of_two_exponent == period_exponent
    assert reference_total == carry_total
    assert clock.carry_total.materialize(maximum_bits=32) == reference_total
    assert clock.next_depth_period_exponent == (period_exponent + (carry_total & 1))


def test_raw_fifteen_carry_closed_form_covers_both_phase_signs() -> None:
    negative = fifteen_raw_power_clock(125, 5)
    positive = fifteen_raw_power_clock(1, 5)

    assert negative.phase_residue_mod32 is not None
    assert negative.phase_residue_mod32 < 16
    assert negative.carry_total.materialize(maximum_bits=8) == 7
    assert positive.phase_residue_mod32 is not None
    assert positive.phase_residue_mod32 >= 16
    assert positive.carry_total.materialize(maximum_bits=8) == 21


def test_raw_fifteen_source_clock_has_an_explicit_five_adic_transient() -> None:
    clock = fifteen_raw_power_clock(5**3, 5)

    assert clock.first_stable_exponent == 2
    assert not clock.settled_at(1)
    assert clock.settled_at(2)
    assert clock.settled_at(10)


def test_raw_fifteen_clock_keeps_large_period_and_total_symbolic() -> None:
    clock = fifteen_raw_power_clock(1, 35)

    assert clock.period_power_of_two_exponent == 31
    assert clock.period(maximum_bits=32) == 1 << 31
    assert clock.carry_total == PowerOfTwoAffineTotal(7, 31, 7)
    assert clock.carry_total.parity == 1
    assert clock.carry_total.materialize(maximum_bits=35) == 15_032_385_543
    assert clock.next_depth_period_exponent == 32


def test_astronomical_raw_fifteen_clock_does_not_materialize_by_default() -> None:
    clock = fifteen_raw_power_clock(1, 1 << 31)

    assert clock.period_power_of_two_exponent == (1 << 31) - 4
    assert clock.carry_total.parity == 1
    with pytest.raises(ValueError, match="symbolic representation"):
        clock.period(maximum_bits=128)
    with pytest.raises(ValueError, match="symbolic representation"):
        clock.carry_total.materialize(maximum_bits=128)


@pytest.mark.parametrize(
    "source,depth,error",
    [
        (0, 1, ValueError),
        (True, 1, TypeError),
        (1, 0, ValueError),
        (1, True, TypeError),
    ],
)
def test_raw_fifteen_clock_rejects_nonpositive_or_nonexact_inputs(
    source: int, depth: int, error: type[Exception]
) -> None:
    with pytest.raises(error):
        fifteen_raw_power_clock(source, depth)


def test_symbolic_total_requires_a_sufficient_explicit_budget() -> None:
    total = PowerOfTwoAffineTotal(7, 31, 7)
    zero_coefficient = PowerOfTwoAffineTotal(0, 1 << 31, 9)

    with pytest.raises(ValueError, match="symbolic representation"):
        total.materialize(maximum_bits=32)
    assert total.materialize(maximum_bits=35) == 15_032_385_543
    assert zero_coefficient.materialize(maximum_bits=4) == 9


def test_modified_clock_descriptor_is_rejected_at_its_consumer_boundary() -> None:
    clock = fifteen_raw_power_clock(1, 5)
    object.__setattr__(clock, "period_power_of_two_exponent", 18)

    with pytest.raises(ValueError, match="inconsistent"):
        clock.validate()

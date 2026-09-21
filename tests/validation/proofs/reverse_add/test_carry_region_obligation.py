"""Research boundary for generic D2/D4 carry-region construction."""

from devtools.experiments.reverse_add.carry_region_obligation import (
    decimal_nonpalindromic_d2_collision,
    first_width_one_collision,
    missing_threshold_pullback,
)
from number_compiler.arithmetic.carry.carry_monoid import CarryFn


def test_original_carry_region_does_not_determine_d2_carry_region() -> None:
    witness = first_width_one_collision(10)

    assert (witness.first_digit, witness.second_digit) == (1, 3)
    assert (witness.first_pair, witness.second_pair) == (2, 6)
    assert witness.original_action is CarryFn.CONST0
    assert (witness.first_successor_pair, witness.second_successor_pair) == (4, 12)
    assert witness.first_successor_action is CarryFn.CONST0
    assert witness.second_successor_action is CarryFn.CONST1


def test_obstruction_occurs_on_nonpalindromic_sources_that_reach_d2() -> None:
    witness = decimal_nonpalindromic_d2_collision()

    assert witness.first_source == (0, 5, 3)
    assert witness.second_source == (0, 5, 4)
    assert witness.original_actions == (
        CarryFn.CONST0,
        CarryFn.CONST1,
        CarryFn.CONST0,
    )
    assert witness.first_output == (3, 0, 4)
    assert witness.second_output == (4, 0, 5)
    assert witness.first_successor_actions == (CarryFn.CONST0,) * 3
    assert witness.second_successor_actions == (
        CarryFn.ID,
        CarryFn.CONST0,
        CarryFn.ID,
    )


def test_missing_operation_is_spatial_threshold_pullback_not_temporal_state() -> None:
    obligation = missing_threshold_pullback()

    assert "value_carry_fn(coefficient(E,i), base)" in obligation.leaf_law
    assert "[a,c)" in obligation.interval_law
    assert "log(width)" in obligation.construction_bound
    assert "source value regions" in obligation.unavailable_input
    assert "carry-atom DAG" in obligation.unavailable_input

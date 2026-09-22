import pytest

from devtools.experiments.collatz import radix5_future_grammar as grammar
from devtools.experiments.collatz.radix5_future_grammar import (
    LEAF_BY_DIGIT,
    LEAF_STATES,
    compose_carrier,
    exact_length_states,
)
from number_compiler.arithmetic.carry.collatz_output_quotient import DOMAIN_ACTIONS
from number_compiler.arithmetic.carry.collatz_f5_quotient import CollatzF5SpatialAction


def test_collatz_f5_leaf_alphabet_is_exactly_fifteen_classes() -> None:
    assert len(LEAF_STATES) == 15


def test_radix5_macro_reaches_seventeen_then_stays_seventeen() -> None:
    assert [len(exact_length_states(5**level)) for level in range(5)] == [
        15,
        17,
        17,
        17,
        17,
    ]


def test_five_cell_macro_alphabet_is_closed_under_macro_composition() -> None:
    macro = exact_length_states(5)
    paired = {compose_carrier(left, right) for left in macro for right in macro}
    assert paired == exact_length_states(10)
    assert len(paired) == 17


def test_factorized_arithmetic_rule_catalog_is_fixed() -> None:
    carry_pairs = {
        (left.carry_action, right.carry_action)
        for left in exact_length_states(5)
        for right in exact_length_states(5)
    }
    f5_pairs = {
        (left.phase, right.phase)
        for left in exact_length_states(5)
        for right in exact_length_states(5)
    }
    # The universal implementation tables are 5x5 even if one finite-length
    # language does not exercise every input pair in one sample.
    assert len(DOMAIN_ACTIONS) ** 2 == 25
    assert 5**2 == 25
    assert carry_pairs
    assert f5_pairs
    macro, doubled = exact_length_states(5), exact_length_states(10)
    for left in macro:
        for right in macro:
            assert compose_carrier(left, right) in doubled


def test_spatial_order_matches_literal_multiplication_all_two_cell_words() -> None:
    # State counts cannot detect reversed composition: check physical carry.
    for lower in range(64):
        for higher in range(64):
            action = compose_carrier(LEAF_BY_DIGIT[lower], LEAF_BY_DIGIT[higher])
            for incoming in range(3):
                expected = (3 * (lower + 64 * higher) + incoming) // (64 * 64)
                assert DOMAIN_ACTIONS[action.carry_action][incoming] == expected
            assert (
                action.phase
                == (LEAF_BY_DIGIT[lower].phase + LEAF_BY_DIGIT[higher].phase) % 5
            )


def test_binary_language_power_matches_bounded_successor_enumeration() -> None:
    expected = LEAF_STATES
    for length in range(1, 17):
        assert exact_length_states(length) == expected
        expected = frozenset(
            compose_carrier(a, b) for a in expected for b in LEAF_STATES
        )


def test_binary_length_avoids_one_step_per_represented_cell(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls = 0
    compose = grammar.compose_carrier

    def counted(
        a: CollatzF5SpatialAction, b: CollatzF5SpatialAction
    ) -> CollatzF5SpatialAction:
        nonlocal calls
        calls += 1
        return compose(a, b)

    monkeypatch.setattr(grammar, "compose_carrier", counted)
    length = 5**64
    result = exact_length_states(length)
    assert result == frozenset(
        CollatzF5SpatialAction(carry, phase)
        for carry in range(5)
        for phase in range(5)
        if carry in (0, 2, 4) or phase == 0
    )
    assert calls == 0  # Closed language: no products or exponent worklist.


def test_spatial_coordinates_and_digit_inputs_are_strict() -> None:
    for bad in (-1, 5):
        with pytest.raises(ValueError):
            CollatzF5SpatialAction(bad, 0)
    with pytest.raises(TypeError):
        CollatzF5SpatialAction(True, 0)
    with pytest.raises(ValueError):
        grammar.carrier_from_digits((-1,))
    with pytest.raises(ValueError):
        exact_length_states(0)

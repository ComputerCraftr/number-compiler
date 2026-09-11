from devtools.experiments.power_numbers.special_idempotent_output import (
    boolean_output_quotient_audit,
    mixed_split_endpoint_counterexample_audit,
    output_partition_successor_closure_audit,
    rank_two_quadratic_power_audit,
    raw_special_materialization_audit,
    terminal_idempotent_control_audit,
)


def test_f4_f5_m11_m13_terminal_controls_specialize_to_boolean_idempotents() -> None:
    expected = {
        ("fermat", 4): ("ALL_PASS", 0),
        ("fermat", 5): ("ALL_FAIL", 1),
        ("mersenne", 11): ("ALL_FAIL", 1),
        ("mersenne", 13): ("ALL_PASS", 0),
    }
    for key, (status, e) in expected.items():
        row = terminal_idempotent_control_audit(*key)
        assert row.status == status
        assert row.idempotent == e
        assert row.idempotent_valid
        assert row.boolean_idempotent
        assert row.expected_boolean == e
        assert row.exact_boolean_specialization
        assert row.digit_derivatives[0] == 1
        assert set(row.digit_derivatives[1:]) == {0}
        assert row.length_endpoints == (1, 1)
        assert row.carry_at_actual_idempotent == row.carry_endpoints[e]
        assert not row.candidate_derived


def test_m29_mixed_support_breaks_endpoint_digit_length_and_carry_collapse() -> None:
    row = mixed_split_endpoint_counterexample_audit()
    assert row.status == "SPLIT"
    assert row.local_orientations == (-1, -1, 1)
    assert row.idempotent == 299403836
    assert row.idempotent not in (0, 1)
    assert row.endpoint_digits == (0, 0)
    assert row.split_digit == 1
    assert row.endpoint_lengths == (1, 1)
    assert row.split_length == 29
    assert row.endpoint_carries == (-1, -1)
    assert row.split_carry == 6
    assert row.endpoint_digit_equality_unsound
    assert row.endpoint_length_equality_unsound
    assert row.endpoint_carry_equality_unsound
    assert not row.candidate_derived


def test_output_relative_partition_is_refined_before_becoming_powered_state() -> None:
    row = output_partition_successor_closure_audit()
    assert row.same_current_bit
    assert row.different_next_bit
    assert row.output_fiber_states == 2
    assert row.successor_closed_states == 3
    assert row.refinements == 1
    assert not row.output_only_partition_is_closed
    assert "successor refinement" in row.conclusion


def test_boolean_output_modes_collapse_or_guard_exactly_on_finite_proved_domain() -> (
    None
):
    collapsed = boolean_output_quotient_audit((False, True), (3, 3))
    assert collapsed.factors_through_bit
    assert collapsed.quotient_states == 1
    assert collapsed.mode == "Concrete"
    assert collapsed.derivative == 0
    assert not collapsed.source_bit_recoverable

    separating = boolean_output_quotient_audit((False, True), (3, 7))
    assert separating.quotient_states == 2
    assert separating.mode == "Guarded"
    assert separating.derivative == 4
    assert separating.source_bit_recoverable

    rejected = boolean_output_quotient_audit((False, False, True), (3, 4, 7))
    assert not rejected.factors_through_bit
    assert rejected.quotient_states is None
    assert rejected.mode is None


def test_raw_special_digits_are_theorem_bit_independent() -> None:
    for family, parameter in (
        ("fermat", 4),
        ("fermat", 5),
        ("mersenne", 11),
        ("mersenne", 13),
    ):
        row = raw_special_materialization_audit(family, parameter)
        assert row.zero_sheet_value == row.raw_value
        assert row.one_sheet_value == row.raw_value
        assert row.source_independent
        assert row.output_quotient_states == 1


def test_shared_quadratic_power_propagates_rank_two_state_exactly() -> None:
    for family, parameter, depth in (
        ("fermat", 4, 7),
        ("fermat", 5, 5),
        ("mersenne", 11, 8),
        ("mersenne", 13, 10),
    ):
        row = rank_two_quadratic_power_audit(family, parameter, depth)
        assert row.exact
        assert row.formal_zero == row.reference_zero
        assert row.formal_one == row.reference_one

from devtools.experiments.power_numbers.special_theorem_behavioral_quotient import (
    delta_hankel_rank_differential,
    theorem_behavioral_frontier,
    theorem_behavioral_quotient_audit,
    theorem_map_spec,
    two_primary_depth_comparison,
)


def test_actual_pepin_map_backward_quotient_is_exact_and_linear_on_prime_controls() -> (
    None
):
    for n in (2, 3, 4):
        audit = theorem_behavioral_quotient_audit("fermat", n)
        assert audit.seed_hits_target_at_decision
        assert audit.seed_first_hit_distance == audit.decision_steps
        assert audit.scalar_observer_hankel_rank == audit.modulus_bits - 1
        assert audit.passing_rank_equals_modulus_bits_minus_one
        assert (
            audit.decision_horizon_classes
            == audit.decision_horizon_expected_prime_classes
        )
        assert audit.decision_terminal_fiber_classes == 2
        assert audit.decision_terminal_fiber_root_count == 1 << audit.decision_steps
        assert audit.passing_terminal_fiber_roots_equal_two_to_depth
        assert (
            audit.passing_terminal_defect_degree_lower_bound
            == 1 << audit.decision_steps
        )
        assert audit.terminal_observer_classes == 2
        assert not audit.terminal_observer_successor_closed
        assert audit.terminal_observer_successor_conflicts >= 1
        assert all(row.pullback_exact for row in audit.dyadic_rows)
        assert all(row.capped_first_hit_formula_exact for row in audit.dyadic_rows)
        assert all(row.classes == row.horizon + 1 for row in audit.dyadic_rows)
        assert all(row.trace_matrix_rank == row.horizon for row in audit.dyadic_rows)


def test_actual_lucas_lehmer_map_backward_quotient_is_exact_and_linear_on_prime_controls() -> (
    None
):
    for p in (5, 7, 13):
        audit = theorem_behavioral_quotient_audit("mersenne", p)
        assert audit.seed_hits_target_at_decision
        assert audit.seed_first_hit_distance == audit.decision_steps
        assert audit.scalar_observer_hankel_rank == audit.modulus_bits - 1
        assert audit.passing_rank_equals_modulus_bits_minus_one
        assert (
            audit.decision_horizon_classes
            == audit.decision_horizon_expected_prime_classes
        )
        assert audit.decision_terminal_fiber_classes == 2
        assert audit.decision_terminal_fiber_root_count == 1 << audit.decision_steps
        assert audit.passing_terminal_fiber_roots_equal_two_to_depth
        assert (
            audit.passing_terminal_defect_degree_lower_bound
            == 1 << audit.decision_steps
        )
        assert not audit.terminal_observer_successor_closed
        assert all(row.classes == row.horizon + 1 for row in audit.dyadic_rows)
        assert all(row.trace_matrix_rank == row.horizon for row in audit.dyadic_rows)


def test_composite_m11_can_collapse_but_does_not_rescue_prime_domain_asymptotics() -> (
    None
):
    audit = theorem_behavioral_quotient_audit("mersenne", 11)
    assert not audit.seed_hits_target_at_decision
    assert audit.seed_first_hit_distance is None
    assert audit.scalar_observer_hankel_rank is None
    # The exact whole-ring trace quotient stabilizes early on this composite.
    counts = {row.horizon: row.classes for row in audit.dyadic_rows}
    assert counts == {1: 2, 2: 2, 4: 2, 8: 2}
    assert audit.decision_horizon_classes == 2
    assert audit.decision_terminal_fiber_classes == 1
    assert audit.decision_terminal_fiber_root_count == 0


def test_composed_map_descriptor_is_small_but_generic_evaluation_depth_is_not() -> None:
    for family, parameter in (("fermat", 4), ("mersenne", 13)):
        audit = theorem_behavioral_quotient_audit(family, parameter)
        assert audit.powered_descriptor_symbolic_rule_count == 1
        assert audit.generic_full_map_degree_log2 == audit.decision_steps
        assert audit.generic_multiplicative_depth_lower_bound == audit.decision_steps
        assert audit.passing_prime_field_degree_below_modulus
        assert audit.passing_full_map_depth_lower_bound_applies
        assert audit.classical_nonlinear_steps == audit.decision_steps
        assert not audit.powered_map_beats_classical_generic_depth
        assert not audit.production_promotable
        assert not audit.hidden_factor_coordinate_used
        assert not audit.bend_coordinate_used
        assert not audit.frobenius_support_coordinate_used


def test_passing_theorem_observer_impulse_has_exact_linear_hankel_rank() -> None:
    for distance in range(0, 17):
        assert delta_hankel_rank_differential(distance) == distance + 1


def test_theorem_targets_are_nonrecurrent_so_first_hit_grammar_is_sound() -> None:
    for family, parameter in (("fermat", 4), ("mersenne", 11), ("mersenne", 13)):
        assert theorem_map_spec(family, parameter).target_nonrecurrent


def test_frontier_rejects_coordinate_renaming_and_fixed_rank_fake_green() -> None:
    frontier = theorem_behavioral_frontier()
    assert frontier.hidden_coordinate_bypassed
    assert frontier.exact_backward_pullback_implemented
    assert frontier.horizon_independent_two_state_powering_rejected
    assert frontier.fixed_horizon_two_state_fiber_valid
    assert frontier.fixed_horizon_polynomial_injector_depth_linear
    assert frontier.capped_first_hit_grammar_constant_rule
    assert frontier.prime_control_classes_linear_in_horizon
    assert frontier.passing_scalar_hankel_rank_linear_in_bits
    assert frontier.generic_powered_map_depth_matches_classical
    assert frontier.fixed_rank_linear_shortcut_rejected
    assert not frontier.powered_wreath_shortcut_proved


def test_existing_two_primary_filtration_is_the_same_seed_depth_frontier_not_a_free_injector() -> (
    None
):
    f4 = two_primary_depth_comparison("fermat", 4)
    m13 = two_primary_depth_comparison("mersenne", 13)
    assert f4.behavioral_decision_classes == 16
    assert f4.conditional_two_primary_classes == 12
    assert m13.behavioral_decision_classes == 12
    assert m13.conditional_two_primary_classes == 13
    for row in (f4, m13):
        assert row.outer_character_decided
        assert not row.deeper_character_available
        assert row.conditional_classes_linear_scale
        assert row.same_source_depth_injector_missing

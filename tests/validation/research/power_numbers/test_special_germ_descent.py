from devtools.experiments.power_numbers.special_germ_descent import (
    character_support_audit,
    cyclotomic_threshold_collapse_audit,
    fermat_f5_sparse_carry_audit,
    germ_descent_frontier,
    iterated_germ_conjugacy_audit,
    mersenne_m29_mixed_orientation_audit,
    polynomial_deck_audit,
    prime_decision_orientation_truth_audit,
)


def test_polynomial_germ_is_exact_deck_quotient() -> None:
    audit = polynomial_deck_audit()
    assert audit.fermat_same_quotient
    assert audit.fermat_tangent_changes_sign
    assert audit.fermat_tangent_square_descends
    assert audit.mersenne_same_quotient
    assert audit.mersenne_tangent_changes_sign
    assert audit.mersenne_tangent_square_descends
    assert not audit.invariant_state_sees_orientation
    assert audit.anti_invariant_requires_square_root


def test_binary_powered_germ_remains_universal_squaring_conjugacy() -> None:
    for steps in range(0, 9):
        audit = iterated_germ_conjugacy_audit(3, steps)
        assert audit.exact
        assert audit.deck_same_after_iteration == (steps >= 1)
        assert audit.multiplication_depth_required_generically == steps


def test_f5_sparse_product_carries_cancel_without_recovering_local_support() -> None:
    audit = fermat_f5_sparse_carry_audit()
    assert audit.factors == (641, 6700417)
    assert audit.minimum_factor_v2 == 7
    assert audit.odd_quotients == (5, 52347)
    assert audit.minimum_depth_multiplicity == 2
    assert audit.parity_constraint_only
    assert audit.first_coefficient_v2 == 7
    assert audit.exact_sparse_product
    assert not audit.candidate_derived


def test_orientation_defect_matches_release_controls() -> None:
    expected = {
        ("fermat", 4): "ALL_PASS",
        ("fermat", 5): "ALL_FAIL",
        ("mersenne", 11): "ALL_FAIL",
        ("mersenne", 13): "ALL_PASS",
    }
    for key, status in expected.items():
        audit = prime_decision_orientation_truth_audit(*key)
        assert audit.orientation_is_involution
        assert audit.support_exact
        assert audit.result.status == status
        assert audit.candidate_derived is False
        assert audit.factor_enumeration == len(audit.local_factors)


def test_scalar_orientation_character_reproduces_even_packet_collision() -> None:
    f5 = prime_decision_orientation_truth_audit("fermat", 5)
    m11 = prime_decision_orientation_truth_audit("mersenne", 11)
    assert f5.local_orientations == (-1, -1)
    assert m11.local_orientations == (-1, -1)
    assert f5.scalar_character == 1
    assert m11.scalar_character == 1
    assert not f5.all_local_pass
    assert not m11.all_local_pass


def test_ring_valued_orientation_retains_mixed_support_and_emits_factor() -> None:
    audit = mersenne_m29_mixed_orientation_audit()
    assert audit.local_factors == (233, 1103, 2089)
    assert audit.local_orientations == (-1, -1, 1)
    assert audit.orientation_is_involution
    assert audit.result.status == "SPLIT"
    assert audit.result.gcd_packet == 2089
    assert audit.support_exact


def test_exact_all_pass_character_expansion_is_exponential_in_hidden_components() -> (
    None
):
    for rank in range(1, 7):
        audit = character_support_audit(rank)
        assert audit.orientation_vectors == 1 << rank
        assert audit.walsh_characters_required_for_exact_all_pass == 1 << rank
        assert audit.nonlinear_support_packet_avoids_collision
    assert not character_support_audit(1).product_character_collision
    assert character_support_audit(2).product_character_collision


def test_direct_two_power_cyclotomic_orbit_collapses_to_base_ring_section() -> None:
    for family, parameter in (
        ("fermat", 4),
        ("fermat", 5),
        ("mersenne", 11),
        ("mersenne", 13),
    ):
        audit = cyclotomic_threshold_collapse_audit(family, parameter)
        assert audit.quotient_orbit_order == 1
        assert audit.base_ring_section_required
        assert not audit.explicit_dense_state_compact
        assert audit.dense_character_degree_log2 == audit.conductor_log2 - 1
        assert audit.factor_enumeration == 0


def test_frontier_remains_fail_closed_without_candidate_orientation_extractor() -> None:
    frontier = germ_descent_frontier()
    assert frontier.polynomial_transport_closed
    assert not frontier.polynomial_orientation_extractor_available
    assert frontier.support_packet_closed
    assert not frontier.direct_cyclotomic_compact_extractor_available
    assert not frontier.factor_free_evaluator_available
    assert frontier.status == "UNKNOWN"

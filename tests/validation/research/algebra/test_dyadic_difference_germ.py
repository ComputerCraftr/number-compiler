import pytest

from devtools.experiments.algebra.dyadic_difference_germ_core import (
    AmbientCapacityUnavailable,
    all_split_composite_controls,
    ambient_capacity_truth,
    difference_moment_jump_audit,
    extension_frobenius_probe,
    formal_phase_frobenius_audit,
    mersenne_difference_moment_matrix,
    mixed_capacity_controls,
)
from devtools.experiments.algebra.dyadic_difference_germ_norm import (
    fermat_cyclotomic_germ_comparison,
    fermat_first_lift_norm_audit,
    fermat_gaussian_quartic_reciprocity_audit,
    fermat_historical_sign_guard,
    fermat_next_lift_guard,
    fermat_second_lift_local_truth,
    fermat_second_lift_norm_search,
)
from devtools.experiments.algebra.dyadic_difference_germ_terminal import (
    candidate_derived_splitting_weight,
    fermat_candidate_artin_guard,
    fermat_filtration_requirement_audit,
    fermat_kummer_threshold_probe,
    fermat_sparse_candidate_quotient_audit,
    fermat_sparse_kummer_base_change_audit,
    fermat_terminal_threshold_probe,
    mersenne_filtration_requirement_audit,
    mersenne_sparse_candidate_quotient_audit,
    mersenne_sparse_torus_base_change_audit,
    mersenne_terminal_threshold_probe,
    special_terminal_threshold_audit,
)
from devtools.experiments.algebra.dyadic_difference_germ_tower import (
    fermat_cyclotomic_norm_tower,
    fermat_fixed_trace_norm_shortcut,
    fermat_normalized_norm_class,
    fermat_quartic_auxiliary_holdout_guard,
)


def test_constant_degree_difference_moments_jump_without_materializing_branches() -> (
    None
):
    matrix = mersenne_difference_moment_matrix(5)
    assert len(matrix) == 6 and all(len(row) == 6 for row in matrix)
    # P0=2; P1=4d; P2=(4d)^2-2(-12d)=16d^2+24d.
    assert matrix[0] == (2, 0, 0, 0, 0, 0)
    assert matrix[1] == (0, 4, 0, 0, 0, 0)
    assert matrix[2] == (0, 24, 16, 0, 0, 0)

    audit = difference_moment_jump_audit(levels=32, max_power=5, root_d=166)
    assert audit.formal_branch_nodes == 1 << 32
    assert audit.moment_state_cells == 36
    assert audit.binary_matrix_compositions == 6
    assert audit.exact


def test_ambient_capacity_truth_matches_f4_f5_m11_m13_controls() -> None:
    f4 = ambient_capacity_truth("fermat", 4)
    f5 = ambient_capacity_truth("fermat", 5)
    m11 = ambient_capacity_truth("mersenne", 11)
    m13 = ambient_capacity_truth("mersenne", 13)

    assert f4.local_factors == (65537,)
    assert f4.local_ambient_v2 == (16,)
    assert f4.baseline_order_v2 == 5
    assert f4.local_lift_depths == (11,)

    assert f5.local_factors == (641, 6700417)
    assert f5.local_ambient_v2 == (7, 7)
    assert f5.baseline_order_v2 == 6
    assert f5.local_lift_depths == (1, 1)

    assert m11.local_factors == (23, 89)
    assert m11.local_ambient_v2 == (1, 1)
    assert m11.baseline_order_v2 == 2
    assert m11.local_lift_depths == (0, 0)

    assert m13.local_factors == (8191,)
    assert m13.local_ambient_v2 == (13,)
    assert m13.baseline_order_v2 == 2
    assert m13.local_lift_depths == (11,)

    assert f4.splitting_weight(1) == 1
    assert f5.splitting_weight(1) == 2
    assert f5.splitting_weight(2) == 0
    assert m11.splitting_weight(1) == 0
    assert m13.splitting_weight(11) == 1
    assert m13.splitting_weight(12) == 0


def test_full_on_circle_candidate_power_is_formally_blind_to_ambient_capacity() -> None:
    # F4 and F5 have radically different local lift depths, but the complete
    # N-power action on every formal lift in range is the same identity action.
    for n in (4, 5):
        for level in (1, 2, 7):
            audit = formal_phase_frobenius_audit("fermat", n, level)
            assert audit.candidate_derived
            assert audit.canonical_action == "identity"
            assert audit.candidate_exponent_residue == 1
            assert not audit.splitting_sensitive
            assert audit.factor_enumeration == audit.root_branch_enumeration == 0

    # On the reverse LL torus the global M_p exponent is canonical inversion,
    # again for both composite M11 and prime M13.
    for p in (11, 13):
        for level in (0, 1, 7):
            audit = formal_phase_frobenius_audit("mersenne", p, level)
            assert audit.canonical_action == "inversion"
            assert (
                audit.candidate_exponent_residue
                == (1 << audit.formal_order_exponent) - 1
            )
            assert not audit.splitting_sensitive


def test_off_circle_crt_valued_defect_can_emit_natural_gcds_without_factor_enumeration() -> (
    None
):
    f4 = extension_frobenius_probe("fermat", 4)
    f5 = extension_frobenius_probe("fermat", 5)
    m11 = extension_frobenius_probe("mersenne", 11)
    m13 = extension_frobenius_probe("mersenne", 13)

    assert f4.defect_zero and not f4.nontrivial_gcds
    assert m13.defect_zero and not m13.nontrivial_gcds

    assert not f5.defect_zero
    assert f5.nontrivial_gcds == (641,)
    assert not m11.defect_zero
    assert m11.nontrivial_gcds == (23,)

    for row in (f4, f5, m11, m13):
        assert row.candidate_derived
        assert row.factor_enumeration == 0
        assert row.root_branch_enumeration == 0
        assert not row.selective_capacity_query

    # The cost is recurrence-scale: Fermat exponentiation needs >= bitlength(N)
    # ring products and Mersenne needs Theta(p) products.  It is not the desired
    # logarithmic-in-parameter ambient-capacity evaluator.
    assert f4.ring_multiplications == 18
    assert f5.ring_multiplications == 34
    assert m11.ring_multiplications == 21
    assert m13.ring_multiplications == 25


def test_global_n_power_defect_is_not_equivalent_to_local_splitting() -> None:
    controls = all_split_composite_controls()
    assert len(controls) == 2
    assert all(row.all_local_algebras_split for row in controls)
    # Both all-split composite rings still have a nonzero global N-power defect.
    # Therefore nonzero defect is a compositeness/cofactor signal, not c_k.
    assert all(not row.defect_zero for row in controls)


def test_special_forms_do_not_collapse_local_capacity_to_one_hidden_scalar() -> None:
    fermat, mersenne = mixed_capacity_controls()
    assert fermat.factor_witnesses_valid
    assert fermat.local_ambient_v2 == (16, 11)
    assert fermat.local_lift_depths == (6, 1)
    assert fermat.global_special_v2 == 512

    assert mersenne.factor_witnesses_valid
    assert mersenne.supplied_factors == (233, 1103, 2089)
    assert mersenne.local_ambient_v2 == (1, 1, 3)
    assert mersenne.local_lift_depths == (0, 0, 1)
    assert mersenne.global_special_v2 == 29


def test_candidate_weight_surface_remains_fail_closed_after_negative_experiment() -> (
    None
):
    with pytest.raises(AmbientCapacityUnavailable):
        candidate_derived_splitting_weight("fermat", 5, 1)
    with pytest.raises(AmbientCapacityUnavailable):
        candidate_derived_splitting_weight("mersenne", 11, 1)


def test_gaussian_quartic_reciprocity_transcript_is_exact_but_even_packet_blind() -> (
    None
):
    f4 = fermat_gaussian_quartic_reciprocity_audit(4)
    f5 = fermat_gaussian_quartic_reciprocity_audit(5)
    f9 = fermat_gaussian_quartic_reciprocity_audit(9)

    # The complete Z[i] Euclidean descent is factor-free and tiny on this
    # structured denominator, but F4/F5 have the same aggregate phase.
    assert f4.phase_exponent == f5.phase_exponent == f9.phase_exponent == 0
    assert f4.phase_unit == f5.phase_unit == f9.phase_unit == "1"
    assert len(f4.steps) == len(f5.steps) == len(f9.steps) == 1
    assert f4.steps[0].ramified_power == f5.steps[0].ramified_power == 2
    assert not f4.natural_gcds and not f5.natural_gcds and not f9.natural_gcds
    for row in (f4, f5, f9):
        assert row.candidate_derived
        assert row.factor_enumeration == row.root_branch_enumeration == 0
        assert not row.splitting_sensitive


def test_first_fermat_transverse_root_has_exact_factor_free_norm_identity() -> None:
    for n in (4, 5, 9):
        audit = fermat_first_lift_norm_audit(n)
        assert audit.exact
        assert audit.root_square == 2
        assert audit.gaussian_norm_value == audit.gaussian_target
        assert audit.factor_enumeration == audit.root_branch_enumeration == 0
        assert audit.radix_squarings == n - 2
        assert audit.inversions == 1


def test_next_fermat_lift_guard_does_not_promote_jacobi_or_quartic_product_phase() -> (
    None
):
    f4 = fermat_next_lift_guard(4)
    f5 = fermat_next_lift_guard(5)

    # F4 has another local lift while F5 does not, but both aggregate objects
    # are +1.  The next relative norm-preimage problem must remain undecided.
    assert f4.jacobi_phase == f5.jacobi_phase == 1
    assert f4.quartic_phase_exponent == f5.quartic_phase_exponent == 0
    assert not f4.decided and not f5.decided
    assert "relative norm" in f4.next_equation
    assert f4.factor_enumeration == f5.factor_enumeration == 0
    assert f4.root_branch_enumeration == f5.root_branch_enumeration == 0


def test_second_fermat_lift_is_a_real_relative_norm_preimage_not_a_product_character() -> (
    None
):
    f3 = fermat_second_lift_norm_search(3, coefficient_bound=2)
    f4 = fermat_second_lift_norm_search(4, coefficient_bound=4)

    # Exact global relative-norm witnesses are constructed from the candidate
    # parameter alone.  No local root or factor is selected.
    assert f3.exact and f4.exact
    assert f3.target == (-4, -1, 3, 3)
    assert f4.target == (-16, -1, 15, 15)
    for row in (f3, f4):
        assert row.candidate_derived
        assert row.factor_enumeration == row.root_branch_enumeration == 0
        assert not row.negative_certificate

    # Bounded factor truth is used only to check semantics: both candidates
    # really do have the second extra local lift.
    assert fermat_second_lift_local_truth(3) == (True, (True,))
    assert fermat_second_lift_local_truth(4) == (True, (True,))


def _assert_negative_controls(
    found: tuple[bool, bool], certificates: tuple[bool, bool]
) -> None:
    assert not any(found)
    assert not any(certificates)


def _assert_negative_local_truth() -> None:
    assert fermat_second_lift_local_truth(2) == (False, (False,))
    assert fermat_second_lift_local_truth(5) == (False, (False, False))


def test_bounded_relative_norm_search_is_fail_closed_on_negative_controls() -> None:
    f2 = fermat_second_lift_norm_search(2, coefficient_bound=4)
    f5 = fermat_second_lift_norm_search(5, coefficient_bound=4)

    # The finite box finds no preimage, agreeing with audit truth, but this is
    # deliberately *not* promoted to a negative certificate.
    _assert_negative_controls(
        (f2.found, f5.found), (f2.negative_certificate, f5.negative_certificate)
    )
    _assert_negative_local_truth()


def test_old_current_phase_order_character_is_not_the_missing_germ_bit() -> None:
    f4 = fermat_cyclotomic_germ_comparison(4)
    f5 = fermat_cyclotomic_germ_comparison(5)

    # Candidate-only repeated squaring sees exactly one extra order layer in the
    # canonical first root in both candidates.  This is the old order-character
    # information carried by the phase that already exists.
    assert f4.candidate_derived_character and f5.candidate_derived_character
    assert f4.candidate_root_order_v2 == 6
    assert f5.candidate_root_order_v2 == 7
    assert f4.normalized_current_character_depth == 1
    assert f5.normalized_current_character_depth == 1

    # Local audit confirms the root order is uniform even on composite F5.
    assert f4.local_root_order_v2 == (6,)
    assert f5.local_root_order_v2 == (7, 7)
    assert f4.current_character_is_uniform_locally
    assert f5.current_character_is_uniform_locally

    # But the ambient group has room for another preimage only on F4.  Thus the
    # next Kummer/germ sign is *not* encoded by the current order character.
    assert f4.local_germ_depths == (11,)
    assert f5.local_germ_depths == (1, 1)
    assert f4.next_germ_bits == (True,)
    assert f5.next_germ_bits == (False, False)
    assert f4.all_local_next_germ
    assert not f5.all_local_next_germ
    assert not f4.character_alone_decides_next_germ
    assert not f5.character_alone_decides_next_germ


def test_historical_fermat_sign_guard_separates_radix_orientation_order_and_germ() -> (
    None
):
    guard = fermat_historical_sign_guard()
    assert guard.same_normalized_current_character
    assert not guard.same_next_germ_bit
    assert not guard.historical_radix_sign_was_depth_quotient
    assert "Kummer-preimage sign" in guard.conclusion


def test_prime_controls_explain_why_the_old_character_looked_like_the_germ() -> None:
    # On a prime Fermat modulus there is only one local component, and its group
    # order is globally known.  The old phase character therefore *can be paired*
    # with that known ambient order to infer residual capacity.  The coincidence
    # disappears as soon as the candidate ring has hidden local group orders.
    f2 = fermat_cyclotomic_germ_comparison(2)
    f3 = fermat_cyclotomic_germ_comparison(3)
    f4 = fermat_cyclotomic_germ_comparison(4)
    assert f2.local_ambient_v2 == (4,) and f2.local_germ_depths == (1,)
    assert f3.local_ambient_v2 == (8,) and f3.local_germ_depths == (4,)
    assert f4.local_ambient_v2 == (16,) and f4.local_germ_depths == (11,)
    assert all(row.normalized_current_character_depth == 1 for row in (f2, f3, f4))


def test_fermat_norm_target_normalizes_to_two_term_cyclotomic_element() -> None:
    for n in (2, 3, 4, 5, 9):
        row = fermat_normalized_norm_class(n)
        assert row.exact
        assert row.beta == (1, -row.t, 0, 0)
        assert row.fixed_unit == (0, -1, -1, -1)
        assert row.fixed_preimage_u == row.fixed_preimage_v == (-1, -1, -1, 0)
        assert row.factor_enumeration == row.root_branch_enumeration == 0


def test_fermat_t_squaring_becomes_an_exact_sparse_cyclotomic_norm_tower() -> None:
    for n in (2, 3, 4, 5, 9):
        row = fermat_cyclotomic_norm_tower(n)
        assert row.exact
        assert row.materialized_cyclotomic_coefficients == 0
        assert row.terminal_coefficient == 2
        assert row.terminal_root_order == 1 << (n + 1)
        assert row.terminal_absolute_norm == row.candidate_modulus
        assert len(row.steps) == n - 2
        assert all(step.source_terms == step.lifted_terms == 2 for step in row.steps)
        if row.steps:
            assert row.steps[0].source_coefficient == row.start_t
            assert row.steps[-1].lifted_coefficient == 2


def test_fixed_trace_shortcut_constructs_f3_f4_norm_witness_without_box_search() -> (
    None
):
    f3 = fermat_fixed_trace_norm_shortcut(3)
    f4 = fermat_fixed_trace_norm_shortcut(4)
    assert f3.exact and f4.exact
    assert f3.gaussian_square_target == (2, 0)
    assert f4.gaussian_square_target == (8, 6)
    assert f3.integer_square_roots <= 2 and f4.integer_square_roots <= 2
    assert f3.modular_fourth_root is not None and f4.modular_fourth_root is not None
    assert f3.modular_fourth_root_square == f3.expected_first_root
    assert f4.modular_fourth_root_square == f4.expected_first_root
    assert f3.candidate_derived and f4.candidate_derived
    assert not f3.negative_certificate and not f4.negative_certificate


def test_fixed_trace_shortcut_miss_is_not_promoted_to_negative_certificate() -> None:
    f2 = fermat_fixed_trace_norm_shortcut(2)
    f5 = fermat_fixed_trace_norm_shortcut(5)
    _assert_negative_controls(
        (f2.found, f5.found), (f2.negative_certificate, f5.negative_certificate)
    )
    # These misses agree with the bounded Fermat audit controls but remain only
    # misses of one fixed trace section, not a proof that the full norm conic
    # has no point.
    _assert_negative_local_truth()


def test_four_auxiliary_quartic_phase_fit_fails_on_generalized_holdout_controls() -> (
    None
):
    rows = fermat_quartic_auxiliary_holdout_guard()
    assert len(rows) == 4
    assert all(row.defeats_signature for row in rows)
    assert all(row.auxiliaries == (34, 22, 42, 5) for row in rows)

    # Independent factor-backed labels for the holdout side.  These factors are
    # audit data only; phase signatures above are computed directly from t^4+1.
    holdout_factors = {
        148: (433, 1108049),
        152: (577, 925121),
        176: (10433, 91969),
        192: (281, 1009, 4793),
    }
    for row in rows:
        t = row.right_t
        N = t**4 + 1
        factors = holdout_factors[t]
        product = 1
        bits: list[bool] = []
        for q in factors:
            product *= q
            r1 = (t + pow(t, -1, q)) % q
            bits.append(pow(r1, (q - 1) // 2, q) == 1)
        assert product == N
        assert all(bits) == row.right_all_local_truth


def test_sparse_terminal_principal_quotient_is_exactly_the_fermat_candidate_ring() -> (
    None
):
    for n in (2, 3, 4, 5, 9):
        row = fermat_sparse_candidate_quotient_audit(n)
        assert row.exact
        assert row.cyclotomic_order == 1 << (n + 1)
        assert row.cyclotomic_degree == 1 << n
        assert row.resultant == row.candidate_modulus
        assert row.quotient_cardinality == row.candidate_modulus
        assert row.linear_relation_residue == 0
        assert row.cyclotomic_relation_residue == 0


def test_sparse_quotient_base_changes_next_kummer_layer_directly_to_candidate_ring() -> (
    None
):
    for n in (2, 3, 4, 5, 9):
        row = fermat_sparse_kummer_base_change_audit(n)
        assert row.exact
        assert row.zeta8_exponent == 1 << (n - 2)
        assert row.sqrt2_image == row.canonical_first_root
        assert row.discriminant_gcd == 1
        assert row.module_rank == 2
        assert "+y iff split" in row.desired_local_artin_action
        assert row.factor_enumeration == row.root_branch_enumeration == 0


def test_fermat_terminal_all_local_threshold_is_primality_equivalent_and_histogram_is_overkill() -> (
    None
):
    for n in (2, 3, 4, 5, 9):
        row = fermat_filtration_requirement_audit(n)
        assert row.terminal_pass_iff_prime
        assert row.terminal_level == (1 << n) - n - 1
        assert row.required_local_v2 == 1 << n
        assert row.least_possible_passing_prime == row.candidate_modulus
        assert not row.full_histogram_required_for_prime_decision
        assert not row.full_histogram_required_for_pure_reconstruction_after_pass
        assert row.full_histogram_required_for_exact_composite_residual
    # On the bounded prime control, the independently enumerated image geometry
    # agrees exactly with the closed theorem that becomes available after PASS.
    assert fermat_filtration_requirement_audit(4).bounded_reference_matches_pure_theorem
    # F5 is beyond the bounded carrier gate; the theorem itself does not use it.
    assert (
        fermat_filtration_requirement_audit(5).bounded_reference_matches_pure_theorem
        is None
    )


def test_candidate_ring_global_frobenius_is_still_formally_blind_after_sparse_base_change() -> (
    None
):
    f4 = fermat_candidate_artin_guard(4)
    f5 = fermat_candidate_artin_guard(5)
    for row in (f4, f5):
        assert row.candidate_exponent_residue == 1
        assert row.global_multiplier == 1
        assert row.gcd_plus == row.candidate_modulus
        assert row.gcd_minus == 1
        assert not row.selective
        assert not row.accepted_as_local_artin
    # Yet the independently audited next germ bits differ, freezing the exact
    # reason global candidate Frobenius cannot replace local q-Frobenius.
    assert fermat_second_lift_local_truth(4) == (True, (True,))
    assert fermat_second_lift_local_truth(5) == (False, (False, False))


def test_fail_closed_kummer_threshold_api_uses_only_exact_positive_witnesses() -> None:
    for n in (2, 3, 4, 5):
        level1 = fermat_kummer_threshold_probe(n, 1)
        assert level1.status == "ALL_PASS"
        assert level1.decided and level1.all_pass
        assert level1.witness_power_residue == 2
        assert level1.factor_enumeration == level1.root_branch_enumeration == 0

    assert fermat_kummer_threshold_probe(3, 2).status == "ALL_PASS"
    assert fermat_kummer_threshold_probe(4, 2).status == "ALL_PASS"
    for n in (2, 5):
        miss = fermat_kummer_threshold_probe(n, 2)
        assert miss.status == "UNKNOWN"
        assert not miss.decided
        assert miss.gcd_packet is None

    # No unsupported higher layer is guessed from the sparse tower alone.
    assert fermat_kummer_threshold_probe(4, 3).status == "UNKNOWN"


def test_terminal_threshold_probe_is_now_the_minimal_fermat_certificate_target() -> (
    None
):
    f2 = fermat_terminal_threshold_probe(2)
    assert f2.level == 1 and f2.status == "ALL_PASS"
    # For F3/F4/F5 the terminal level lies beyond the currently constructed
    # positive sections, so the new minimal certificate surface stays unknown.
    assert fermat_terminal_threshold_probe(3).level == 4
    assert fermat_terminal_threshold_probe(3).status == "UNKNOWN"
    assert fermat_terminal_threshold_probe(4).level == 11
    assert fermat_terminal_threshold_probe(4).status == "UNKNOWN"
    assert fermat_terminal_threshold_probe(5).level == 26
    assert fermat_terminal_threshold_probe(5).status == "UNKNOWN"


def test_mersenne_terminal_all_local_threshold_is_primality_equivalent_and_histogram_is_overkill() -> (
    None
):
    m11 = mersenne_filtration_requirement_audit(11)
    m13 = mersenne_filtration_requirement_audit(13)
    for row in (m11, m13):
        assert row.terminal_level == row.exponent - 2
        assert row.baseline_order_v2 == 2
        assert row.required_local_v2 == row.exponent
        assert row.plus_branch_least_prime > row.candidate_modulus
        assert row.minus_branch_least_prime == row.candidate_modulus
        assert row.terminal_pass_iff_prime
        assert not row.full_histogram_required_for_prime_decision
        assert not row.full_histogram_required_for_pure_reconstruction_after_pass
        assert row.full_histogram_required_for_exact_composite_residual

    assert m11.bounded_reference_status == "composite"
    assert m11.bounded_reference_matches_pure_theorem is None
    assert m13.bounded_reference_status == "prime"
    assert m13.bounded_reference_matches_pure_theorem is True


def test_mersenne_terminal_probe_is_fail_closed_until_torus_selector_exists() -> None:
    assert mersenne_terminal_threshold_probe(11).level == 9
    assert mersenne_terminal_threshold_probe(11).status == "UNKNOWN"
    assert mersenne_terminal_threshold_probe(13).level == 11
    assert mersenne_terminal_threshold_probe(13).status == "UNKNOWN"


def test_common_terminal_threshold_audit_dispatches_without_changing_family_semantics() -> (
    None
):
    f4 = special_terminal_threshold_audit("fermat", 4)
    m13 = special_terminal_threshold_audit("mersenne", 13)
    assert f4.terminal_level == 11
    assert m13.terminal_level == 11
    assert f4.required_local_v2 == 16
    assert m13.required_local_v2 == 13


def test_mersenne_sparse_principal_quotient_is_exactly_the_candidate_ring_for_prime_exponents() -> (
    None
):
    for p in (3, 5, 7, 11, 13):
        row = mersenne_sparse_candidate_quotient_audit(p)
        assert row.exact
        assert row.cyclotomic_order == p
        assert row.cyclotomic_degree == p - 1
        assert row.zeta_image == 2
        assert row.resultant == (1 << p) - 1


def test_mersenne_sparse_quotient_base_changes_to_the_ll_norm_one_torus_but_global_action_is_blind() -> (
    None
):
    for p in (5, 11, 13):
        row = mersenne_sparse_torus_base_change_audit(p)
        assert row.exact
        assert row.torus_trace == 4
        assert row.torus_norm == 1
        assert row.formal_terminal_order == 1 << p
        assert row.candidate_exponent_residue == (1 << p) - 1
        assert row.candidate_action == "inversion"
        assert row.terminal_level == p - 2
        assert row.factor_enumeration == 0
        assert row.root_branch_enumeration == 0

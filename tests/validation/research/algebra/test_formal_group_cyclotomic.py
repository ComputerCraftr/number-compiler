from devtools.experiments.algebra.formal_group_cyclotomic import (
    divisibility_closure_audit,
    endpoint_norm_audit,
    finite_interval_conjugacy_audit,
    formal_exponential_denominator_audit,
    formal_group_cyclotomic_frontier,
    known_axis_additive_orbit_audit,
    lcm_closure_audit,
    norm_symmetrization_audit,
    scalar_lcm_forcing_audit,
    tangent_exponential_audit,
    translation_rotation_audit,
)
from devtools.paths import repository_root


def test_additive_translation_cannot_be_globally_conjugated_to_nontrivial_rotation() -> (
    None
):
    for key in (("fermat", 5), ("mersenne", 11), ("mersenne", 29)):
        audit = translation_rotation_audit(*key)
        assert audit.translation_order == audit.hidden_factor
        assert audit.multiplicative_group_order == audit.hidden_factor - 1
        assert audit.orders_coprime
        assert not audit.nontrivial_group_conjugacy_possible
        assert not audit.rational_semiconjugacy_to_nontrivial_scaling_possible
        assert not audit.pgl_invariants_equal
        assert audit.pgl_gap_equals_square_over_scale


def test_denominator_free_binomial_exponential_is_only_the_tangent_not_the_affine_bend_orbit() -> (
    None
):
    for key in (
        ("fermat", 4),
        ("fermat", 5),
        ("mersenne", 11),
        ("mersenne", 13),
        ("mersenne", 29),
    ):
        audit = tangent_exponential_audit(*key)
        assert audit.stride_is_unit
        assert audit.affine_0 == audit.geometric_0 == 1
        assert audit.affine_1 == audit.geometric_1
        assert audit.tangent_matches_two_points_only
        assert audit.second_order_discrepancy == audit.expected_discrepancy
        assert audit.discrepancy_gcd == 1
        assert not audit.support_preserving_projection


def test_finite_window_polynomial_conjugacy_has_exactly_linear_degree() -> None:
    for family, parameter, span in (
        ("fermat", 5, 511),
        ("mersenne", 11, 2),
        ("mersenne", 29, 200),
    ):
        audit = finite_interval_conjugacy_audit(family, parameter, span=span)
        assert audit.exact_interpolation_degree == span - 1
        assert audit.top_newton_difference != 0
        assert audit.all_newton_differences_nonzero
        assert audit.degree_grows_linearly_with_span
        assert not audit.bounded_degree_conjugacy_available


def test_formal_exponential_first_bad_denominator_is_exactly_the_hidden_factor() -> (
    None
):
    expected = {
        ("fermat", 5): (641, 5),
        ("mersenne", 11): (23, 1),
        ("mersenne", 29): (233, 4),
    }
    for key, (factor, slot) in expected.items():
        audit = formal_exponential_denominator_audit(*key)
        assert audit.hidden_factor == factor
        assert audit.bend_slot == slot
        assert audit.bend_atom == factor
        assert audit.first_nonunit_factorial_denominator == factor
        assert audit.legal_coefficients_before_failure == factor - 1
        assert audit.denominator_gcd_at_failure == factor
        assert audit.failure_equals_hidden_factor
        assert audit.failure_equals_bend_atom
        assert audit.hidden_q_adic_input_valuation == 0
        assert not audit.hidden_q_adic_log_convergent
        assert audit.two_adic_stride_valuation >= 1
        assert audit.odd_modulus_is_two_adic_unit
        assert audit.two_adic_quotient_by_modulus_is_trivial


def test_native_additive_frobenius_orbit_collapses_exactly_once_hidden_axis_is_known() -> (
    None
):
    expected = {
        ("fermat", 5): (641, 5),
        ("mersenne", 11): (23, 1),
        ("mersenne", 29): (233, 4),
    }
    for key, (factor, slot) in expected.items():
        audit = known_axis_additive_orbit_audit(*key)
        assert audit.hidden_factor == factor
        assert audit.recovered_slot == slot == audit.expected_slot
        assert audit.additive_orbit_product_mod_q == 0
        assert audit.frobenius_endpoint_mod_q == 0
        assert audit.collapse_exact
        assert audit.one_inverse_locates_bend
        assert audit.assumes_hidden_axis


def test_obvious_gaussian_and_pell_endpoint_norm_modules_have_identical_rank_profile_on_prime_and_composite_controls() -> (
    None
):
    for key in (
        ("fermat", 4),
        ("fermat", 5),
        ("mersenne", 11),
        ("mersenne", 13),
        ("mersenne", 29),
    ):
        audit = endpoint_norm_audit(*key)
        assert audit.endpoint_identity_exact
        assert audit.determinant_mod_n == 0
        assert audit.unit_minor_gcd == 1
        assert audit.witness_maps_to_zero
        assert audit.fitting_zero_is_zero_ideal
        assert audit.fitting_one_is_unit_ideal
        assert audit.rank_profile_is_universally_one


def test_quadratic_norm_symmetrization_erases_the_actual_bend_support() -> None:
    for family, parameter, factor in (
        ("fermat", 5, 641),
        ("mersenne", 11, 23),
        ("mersenne", 29, 233),
    ):
        audit = norm_symmetrization_audit(family, parameter)
        assert audit.hidden_factor == factor
        assert audit.bend_atom_gcd == factor
        assert audit.norm_value_gcd == 1
        assert not audit.hidden_factor_survives_norm


def test_self_indexed_frobenius_forcing_is_exactly_divisibility_closure_of_hidden_bend_slots() -> (
    None
):
    rows = (
        ("fermat", 5, 5),
        ("fermat", 5, 10),
        ("fermat", 5, 52347),
        ("mersenne", 29, 4),
        ("mersenne", 29, 19),
        ("mersenne", 29, 36),
    )
    for family, parameter, query in rows:
        audit = divisibility_closure_audit(family, parameter, query)
        assert audit.factor_truth_only
        assert audit.closure_theorem_exact
        assert all(
            row.whole_field_fixed == row.slot_divides_query for row in audit.rows
        )


def test_one_universal_divisibility_closure_query_reopens_linear_size_lcm_exponent() -> (
    None
):
    rows = (
        ("fermat", 5, 16),
        ("fermat", 5, 64),
        ("fermat", 5, 256),
        ("fermat", 5, 511),
        ("mersenne", 29, 16),
        ("mersenne", 29, 64),
        ("mersenne", 29, 256),
        ("mersenne", 29, 399),
    )
    for family, parameter, span in rows:
        audit = lcm_closure_audit(family, parameter, span)
        assert audit.all_slots_divide_query
        assert audit.query_descriptor_is_linear_scale_in_span
        assert audit.query_slot_bits > 0
        assert audit.exponent_bits >= audit.query_slot_bits
        assert audit.binary_power_multiplications >= audit.exponent_bits - 1
        assert not audit.polylogarithmic_in_span
    assert lcm_closure_audit("fermat", 5, 511).query_slot_bits == 742
    assert lcm_closure_audit("mersenne", 29, 399).query_slot_bits == 574


def test_fermat_lcm_forcing_is_a_real_candidate_derived_criterion_but_has_linear_window_exponent_size() -> (
    None
):
    prime = scalar_lcm_forcing_audit("fermat", 4)
    composite = scalar_lcm_forcing_audit("fermat", 5)
    assert prime.candidate_is_prime_by_truth
    assert prime.forcing_gcd == 1
    assert prime.criterion_classifies_control
    assert prime.criterion_is_general_for_family
    assert not composite.candidate_is_prime_by_truth
    assert composite.forcing_gcd == 641
    assert composite.criterion_classifies_control
    assert composite.criterion_is_general_for_family
    assert composite.exponent_bits == 749
    assert composite.binary_power_multiplications > composite.span
    assert composite.binary_power_multiplications > composite.comparison_reference_steps
    assert not composite.polylogarithmic_in_span


def test_same_scalar_lcm_forcing_is_not_a_general_mersenne_primality_criterion() -> (
    None
):
    m11 = scalar_lcm_forcing_audit("mersenne", 11)
    m13 = scalar_lcm_forcing_audit("mersenne", 13)
    m29 = scalar_lcm_forcing_audit("mersenne", 29)
    m31 = scalar_lcm_forcing_audit("mersenne", 31)
    assert m11.forcing_gcd == 23
    assert m13.forcing_gcd == 1
    assert m29.forcing_gcd == m29.modulus
    assert m31.candidate_is_prime_by_truth
    assert m31.forcing_gcd == m31.modulus
    assert not m31.criterion_classifies_control
    assert not m31.criterion_is_general_for_family
    assert not m31.polylogarithmic_in_span


def test_formal_group_cyclotomic_frontier_remains_fail_closed() -> None:
    frontier = formal_group_cyclotomic_frontier()
    assert not frontier.additive_to_multiplicative_global_conjugacy_possible
    assert not frontier.rational_semiconjugacy_possible
    assert not frontier.denominator_free_tangent_support_preserving
    assert not frontier.finite_interval_bounded_degree_conjugacy_available
    assert frontier.formal_exponential_reproduces_hidden_factor
    assert not frontier.formal_exponential_polylogarithmic_source_constructor
    assert frontier.known_axis_additive_frobenius_collapse_exact
    assert frontier.known_axis_assumes_hidden_factor
    assert not frontier.endpoint_quadratic_norm_distinguishes_prime_from_composite
    assert not frontier.norm_symmetrization_preserves_bend_support
    assert frontier.divisibility_closure_forcing_exact
    assert not frontier.lcm_closure_polylogarithmic
    assert frontier.fermat_scalar_lcm_forcing_semantically_exact
    assert not frontier.fermat_scalar_lcm_forcing_polylogarithmic
    assert not frontier.mersenne_scalar_lcm_forcing_general
    assert not frontier.production_source_extractor_available
    assert frontier.status == "UNKNOWN"


def test_formal_group_research_is_not_reachable_from_production_sources() -> None:
    root = repository_root() / "src" / "number_compiler"
    source = "\n".join(path.read_text() for path in root.glob("*.py"))
    assert "devtools.experiments.algebra.formal_group_cyclotomic" not in source
    assert "formal_group_cyclotomic" not in source

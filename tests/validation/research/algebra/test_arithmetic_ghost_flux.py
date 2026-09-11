from math import gcd

from devtools.experiments.algebra.arithmetic_ghost_flux import (
    analytic_gamma_boundary_audit,
    arithmetic_ghost_flux_block,
    arithmetic_ghost_flux_frontier,
    arithmetic_plaquette_audit,
    arithmetic_wilson_line_audit,
    baby_giant_ghost_flux_audit,
    boundary_flux_blindness_audit,
    complex_arithmetic_flux_mismatch_audit,
    divisor_current_integral_audit,
    fermat_binomial_dyadic_audit,
    finite_difference_ghost_jet_audit,
    linear_resultant_flux_audit,
    singular_delta_fourier_audit,
)
from devtools.paths import repository_root


def test_exact_ghost_flux_matches_known_transverse_singular_support() -> None:
    rows = {
        ("fermat", 4, 1, 3): 1,
        ("fermat", 5, 1, 5): 641,
        ("mersenne", 13, 1, 3): 1,
        ("mersenne", 29, 1, 4): 233,
    }
    for (family, parameter, start, span), expected in rows.items():
        block = arithmetic_ghost_flux_block(
            family,
            parameter,
            start=start,
            span=span,
        )
        assert block.support_gcd == expected
        assert gcd(block.product, block.spec.modulus) == expected
        assert block.atom_evaluations == span
        assert block.multiplications == span - 1


def test_multiplicative_line_integral_is_exact_and_fails_at_a_nonunit_boundary() -> (
    None
):
    regular = arithmetic_wilson_line_audit(
        "fermat",
        5,
        start=1,
        span=4,
        shift=1,
    )
    assert regular.boundary_width == 1
    assert regular.division_free_line_identity_exact
    assert regular.leaving_gcd == 1
    assert regular.entering_gcd == 641
    assert regular.normalized_wilson_line is not None
    assert regular.normalized_line_exact

    singular = arithmetic_wilson_line_audit(
        "fermat",
        5,
        start=5,
        span=4,
        shift=1,
    )
    assert singular.division_free_line_identity_exact
    assert singular.leaving_gcd == 641
    assert singular.normalized_wilson_line is None
    assert not singular.normalized_line_exact


def test_divisor_current_line_integral_is_exact_but_enumerates_the_interior() -> None:
    for key, expected in (
        (("fermat", 5, 1, 5), 641),
        (("mersenne", 29, 1, 399), (1 << 29) - 1),
    ):
        family, parameter, start, span = key
        audit = divisor_current_integral_audit(
            family,
            parameter,
            start=start,
            span=span,
        )
        assert audit.divisor_integral_exact
        assert audit.direct_flux_gcd == expected
        assert audit.integrated_local_gcd_product == expected
        assert audit.nonunit_atom_count >= 1
        assert audit.enumerates_interior_atoms


def test_projective_connection_is_exactly_flat_on_unit_plaquettes() -> None:
    for key in (("fermat", 5, 1, 2), ("mersenne", 29, 1, 1), ("mersenne", 13, 1, 1)):
        family, parameter, start, span = key
        audit = arithmetic_plaquette_audit(
            family,
            parameter,
            start=start,
            span=span,
        )
        assert audit.all_edges_units
        assert audit.projective_curvature_trivial
        assert audit.normalized_loop_holonomy == 1
        assert (
            audit.right_then_up_numerator * audit.up_then_right_denominator
            - audit.up_then_right_numerator * audit.right_then_up_denominator
        ) % (
            (1 << (1 << parameter)) + 1 if family == "fermat" else (1 << parameter) - 1
        ) == 0


def test_singular_corner_preserves_division_free_flat_identity_but_breaks_normalization() -> (
    None
):
    audit = arithmetic_plaquette_audit("mersenne", 29, start=1, span=2)
    assert audit.edge_gcds == (1, 1, 233)
    assert not audit.all_edges_units
    assert audit.projective_curvature_trivial
    assert audit.normalized_loop_holonomy is None


def test_flat_unit_boundary_can_be_completely_blind_to_interior_ghost_flux() -> None:
    f5 = boundary_flux_blindness_audit("fermat", 5, start=1, span=5)
    assert f5.interior_flux_gcd == 641
    assert f5.boundary_product_gcd == 1
    assert f5.boundary_atoms_units
    assert f5.flat_boundary_connection_defined
    assert f5.interior_flux_invisible_to_unit_boundary

    m29 = boundary_flux_blindness_audit("mersenne", 29, start=1, span=4)
    assert m29.interior_flux_gcd == 233
    assert m29.boundary_product_gcd == 1
    assert m29.interior_flux_invisible_to_unit_boundary


def test_rising_factorial_finite_difference_jet_has_exact_order_equal_to_span() -> None:
    for span in (1, 2, 4, 8, 16, 32, 64, 128, 256):
        audit = finite_difference_ghost_jet_audit(
            "fermat",
            5,
            start=1,
            span=span,
        )
        assert audit.closed_form_exact
        assert audit.forward_differences == audit.closed_form_differences
        assert (
            audit.top_difference
            == (pow(128, span, audit.modulus) * (factorial_mod(span, audit.modulus)))
            % audit.modulus
        )
        assert audit.top_difference_unit
        assert audit.top_difference_gcd == 1
        assert audit.formal_polynomial_degree == span
        assert audit.required_exact_jet_order == span
        assert audit.exact_newton_coefficient_count == span + 1
        assert not audit.bounded_order_jet_closed


def factorial_mod(n: int, modulus: int) -> int:
    out = 1
    for value in range(2, n + 1):
        out = out * value % modulus
    return out


def test_ordinary_complex_line_integral_has_no_zero_where_arithmetic_flux_is_nontrivial() -> (
    None
):
    for key, expected in (
        (("fermat", 5, 1, 5), 641),
        (("mersenne", 29, 1, 4), 233),
    ):
        family, parameter, start, span = key
        audit = complex_arithmetic_flux_mismatch_audit(
            family,
            parameter,
            start=start,
            span=span,
        )
        assert audit.affine_complex_root < 0
        assert audit.ordinary_complex_zero_count_on_positive_path == 0
        assert audit.arithmetic_flux_gcd == expected
        assert not audit.complex_path_sees_arithmetic_defect


def test_gamma_boundary_formula_is_exact_symbolic_compression_not_modular_evaluator() -> (
    None
):
    for key in (("fermat", 5, 1, 5), ("mersenne", 29, 1, 32)):
        family, parameter, start, span = key
        audit = analytic_gamma_boundary_audit(
            family,
            parameter,
            start=start,
            span=span,
        )
        assert audit.exact
        assert (
            audit.direct_integer_product_modulus
            == audit.rising_factorial_product_modulus
        )
        assert audit.gamma_end - audit.gamma_start == span
        assert audit.boundary_descriptor_fields == 3
        assert audit.expanded_factor_count == span
        assert not audit.modular_gamma_evaluator_available


def test_linear_resultant_is_exactly_the_same_holonomy_not_a_new_evaluator() -> None:
    for key in (("fermat", 5, 1, 5), ("mersenne", 11, 1, 2), ("mersenne", 29, 1, 8)):
        family, parameter, start, span = key
        audit = linear_resultant_flux_audit(
            family,
            parameter,
            start=start,
            span=span,
        )
        assert audit.exact
        assert audit.linear_resultant == audit.direct_product
        assert audit.support_gcd == gcd(
            audit.direct_product,
            (1 << (1 << parameter)) + 1 if family == "fermat" else (1 << parameter) - 1,
        )
        assert audit.polynomial_degree == span
        assert audit.root_evaluations_encoded == span
        assert not audit.compact_new_evaluator_supplied


def test_fermat_power_of_two_binomial_recursion_branches_to_every_leaf() -> None:
    for span in (1, 2, 4, 8, 16, 32, 64, 128, 256):
        audit = fermat_binomial_dyadic_audit(5, start=1, span=span)
        assert audit.exact
        assert audit.direct_binomial == audit.recursive_binomial
        assert audit.all_denominators_units
        assert audit.internal_splits == span - 1
        assert audit.leaf_terms == span
        assert audit.unique_leaf_offsets == span
        assert audit.denominator_inversions == span - 1
        assert audit.memo_reuse == 0
        assert not audit.bounded_binary_state_closed


def test_singular_delta_current_has_dense_exact_fourier_spectrum() -> None:
    expected = {
        ("fermat", 5): 641,
        ("mersenne", 11): 23,
        ("mersenne", 29): 233,
    }
    for key, period in expected.items():
        audit = singular_delta_fourier_audit(*key)
        assert audit.hidden_period == period
        assert audit.exact_fourier_character_count == period
        assert audit.nonzero_fourier_coefficients == period
        assert audit.spectral_density_numerator == audit.spectral_density_denominator
        assert not audit.sparse_exact_spectrum


def test_baby_giant_polynomial_view_reduces_state_but_not_actual_work() -> None:
    for key in (("fermat", 5, 1, 511), ("mersenne", 29, 1, 399)):
        family, parameter, start, span = key
        audit = baby_giant_ghost_flux_audit(
            family,
            parameter,
            start=start,
            span=span,
        )
        assert audit.exact
        assert audit.baby_giant_product == audit.direct_product
        assert audit.baby_width * audit.baby_width >= span
        assert audit.polynomial_coefficient_count == audit.baby_width + 1
        assert audit.state_sublinear_in_span
        assert not audit.actual_work_beats_linear_product
        assert (
            audit.charged_modular_multiplications > audit.direct_linear_multiplications
        )
        assert not audit.polylog_state
        assert not audit.production_evaluator_available


def test_arithmetic_stokes_research_does_not_fake_release_closure() -> None:
    frontier = arithmetic_ghost_flux_frontier()
    assert frontier.divisor_current_semantics_closed
    assert frontier.flat_unit_connection_closed
    assert not frontier.unit_boundary_recovers_interior_flux
    assert not frontier.bounded_order_finite_difference_jet_closed
    assert not frontier.linear_resultant_is_new_evaluator
    assert not frontier.fermat_dyadic_binomial_branch_collapse_closed
    assert not frontier.exact_fourier_state_sparse
    assert frontier.baby_giant_state_sublinear
    assert not frontier.baby_giant_actual_work_polylogarithmic
    assert not frontier.production_source_extractor_available
    assert frontier.status == "UNKNOWN"


def test_arithmetic_ghost_flux_research_is_not_reachable_from_production_sources() -> (
    None
):

    root = repository_root() / "src" / "number_compiler"
    source = "\n".join(path.read_text() for path in root.glob("*.py"))
    assert "devtools.experiments.algebra.arithmetic_ghost_flux" not in source
    assert "arithmetic_ghost_flux" not in source

from devtools.experiments.algebra.bend_scaling import bend_scaling_audit
from devtools.experiments.algebra.residue_refined_bend import (
    fast_multipoint_bend_audit,
    fitting_bend_support_audit,
    multipoint_engine_audit,
    residue_refined_bend_audit,
    residue_refined_bend_frontier,
)
from devtools.paths import repository_root


def test_fast_multipoint_engine_is_exact_over_composite_coefficient_rings() -> None:
    audit = multipoint_engine_audit()
    assert audit.composite_moduli_only
    assert audit.monic_division_uses_no_field_inverse
    assert audit.all_exact
    assert all(row.actual_values == row.expected_values for row in audit.cases)
    assert all(row.scalar_multiplications > 0 for row in audit.cases)


def test_residue_refined_bend_is_initial_form_cancellation_not_plain_tropical_tie() -> (
    None
):
    expected = {
        ("fermat", 5): 641,
        ("mersenne", 11): 23,
        ("mersenne", 29): 233,
    }
    for key, factor in expected.items():
        audit = residue_refined_bend_audit(*key)
        assert audit.hidden_factor == factor
        assert audit.plain_tropical_tie_on_regular
        assert audit.plain_tropical_tie_on_singular
        assert not audit.residue_refined_bend_on_regular
        assert audit.residue_refined_bend_on_singular
        assert audit.regular_initial_sum != 0
        assert audit.singular_initial_sum == 0


def test_pointwise_residue_bend_already_has_a_factor_free_gcd_detector() -> None:
    expected = {
        ("fermat", 5): 641,
        ("mersenne", 11): 23,
        ("mersenne", 29): 233,
    }
    for key, factor in expected.items():
        audit = residue_refined_bend_audit(*key)
        assert audit.pointwise_factor_free_regular_gcd == 1
        assert audit.pointwise_factor_free_singular_gcd == factor
        assert audit.pointwise_factor_free_bend_detector_exists
        assert audit.interval_location_still_unresolved_by_point_test


def test_fitting_and_annihilator_have_the_same_bend_support_on_controls() -> None:
    rows = (
        ("fermat", 4, 1, 3, 1),
        ("fermat", 5, 1, 511, 641),
        ("mersenne", 11, 1, 2, 23),
        ("mersenne", 13, 1, 3, 1),
        ("mersenne", 29, 1, 399, (1 << 29) - 1),
    )
    for family, parameter, start, span, expected in rows:
        audit = fitting_bend_support_audit(
            family,
            parameter,
            start=start,
            span=span,
        )
        assert audit.fitting_support_gcd == expected
        assert audit.support_exactly_equal
        assert audit.direct_product_equal
        assert audit.fitting_is_existing_interval_product
        assert audit.annihilator_avoids_product_but_not_leaf_scan
        assert audit.pointwise_gcd_observations_for_annihilator == span
        assert audit.product_multiplications_for_fitting == span - 1


def test_fast_multipoint_bend_batch_is_exact_and_factor_free_on_prime_and_composite_controls() -> (
    None
):
    rows = (
        ("fermat", 4, 1, 3, 1),
        ("fermat", 5, 1, 511, 641),
        ("mersenne", 11, 1, 2, 23),
        ("mersenne", 13, 1, 3, 1),
        ("mersenne", 29, 1, 399, (1 << 29) - 1),
    )
    for family, parameter, start, span, expected in rows:
        audit = fast_multipoint_bend_audit(
            family,
            parameter,
            start=start,
            span=span,
        )
        assert audit.factor_free
        assert audit.exact
        assert audit.reconstructed_product == audit.direct_product
        assert audit.bend_support_gcd == expected == audit.direct_support_gcd
        assert audit.final_support_gcds == 1
        assert audit.asymptotically_sublinear_in_span
        assert not audit.polylogarithmic_in_span


def test_full_support_m29_descends_to_a_natural_proper_block_factor() -> None:
    audit = fast_multipoint_bend_audit("mersenne", 29, start=1, span=399)
    assert audit.bend_support_gcd == audit.modulus
    assert audit.first_proper_block_gcd == 233 * 1103
    assert 1 < audit.first_proper_block_gcd < audit.modulus
    assert audit.split_descent_gcds == 1
    assert audit.split_descent_gcds < audit.span


def test_proper_f5_support_needs_only_the_final_batch_gcd() -> None:
    audit = fast_multipoint_bend_audit("fermat", 5, start=1, span=511)
    assert audit.bend_support_gcd == 641
    assert audit.first_proper_block_gcd == 641
    assert audit.final_support_gcds == 1
    assert audit.split_descent_gcds == 0


def test_fast_batch_state_is_sqrt_scale_but_bounded_controls_do_not_fake_a_work_win() -> (
    None
):
    for family, parameter, width in (("fermat", 5, 511), ("mersenne", 29, 399)):
        audit = fast_multipoint_bend_audit(family, parameter, start=1, span=width)
        assert audit.structural_state_sublinear_on_control
        assert audit.structural_state_entries < width
        assert not audit.total_ring_ops_beat_linear_on_control
        assert audit.charged_total_ring_ops > audit.direct_linear_multiplications


def test_m61_scaling_preserves_exactness_and_sublinear_structural_exponent() -> None:
    audit = bend_scaling_audit("mersenne", 61, (64, 256, 1024, 4096))
    assert audit.all_exact
    assert audit.all_state_sublinear_on_controls
    assert 0.79 < audit.theoretical_karatsuba_exponent_in_span < 0.80
    assert not audit.measured_total_ring_ops_beat_linear
    assert not audit.measured_scalar_multiplications_beat_linear
    counts = [row.charged_total_ring_ops for row in audit.rows]
    assert counts == sorted(counts)


def test_large_prime_window_remains_clear_without_leaf_gcd_enumeration() -> None:
    audit = fast_multipoint_bend_audit("mersenne", 61, start=1, span=16384)
    assert audit.exact
    assert audit.bend_support_gcd == 1
    assert audit.final_support_gcds == 1
    assert audit.split_descent_gcds == 0
    assert audit.full_blocks < audit.span
    assert audit.structural_state_entries < audit.span


def test_residue_refined_bend_frontier_does_not_claim_release_closure() -> None:
    frontier = residue_refined_bend_frontier()
    assert frontier.residue_refined_point_bend_exact
    assert frontier.factor_free_point_bend_exact
    assert frontier.fitting_support_exact
    assert frontier.annihilator_support_exact
    assert frontier.fitting_is_old_interval_product
    assert frontier.annihilator_still_linear_source_scan
    assert frontier.fast_multipoint_factor_free
    assert frontier.fast_multipoint_exact
    assert frontier.fast_multipoint_asymptotically_sublinear
    assert not frontier.fast_multipoint_polylogarithmic
    assert frontier.full_support_factor_descent_logarithmic
    assert frontier.support_only_skips_factor_descent
    assert not frontier.production_source_extractor_available
    assert frontier.status == "UNKNOWN"


def test_residue_refined_bend_research_is_not_reachable_from_production_sources() -> (
    None
):
    root = repository_root() / "src" / "number_compiler"
    source = "\n".join(path.read_text() for path in root.glob("*.py"))
    assert "devtools.experiments.algebra.residue_refined_bend" not in source
    assert "residue_refined_bend" not in source


def test_digit_only_support_observer_skips_full_support_factor_descent() -> None:
    from devtools.experiments.algebra.residue_refined_bend import (
        fast_multipoint_support_decision,
    )

    audit = fast_multipoint_support_decision("mersenne", 29, start=1, span=399)
    assert audit.bend_support_gcd == audit.modulus
    assert audit.final_support_gcds == 1
    assert audit.split_descent_gcds == 0
    assert audit.first_proper_block_gcd is None
    assert not audit.direct_control_evaluated


def test_first_bend_locator_reuses_product_tree_and_keeps_gcd_work_logarithmic() -> (
    None
):
    audit = fast_multipoint_bend_audit(
        "mersenne",
        29,
        start=1,
        span=399,
        locate_first_bend=True,
    )
    assert audit.first_bend_slot == 4
    assert audit.first_bend_gcd == 233
    # One baby-block probe plus a constant early atom prefix on this control.
    assert audit.block_locator_gcds == 1
    assert audit.leaf_locator_gcds == 4
    assert audit.block_locator_gcds + audit.leaf_locator_gcds < audit.baby_width


def test_late_f6_bend_uses_logarithmic_gcd_localization_not_sqrt_scan() -> None:
    audit = fast_multipoint_bend_audit(
        "fermat",
        6,
        start=1,
        span=2048,
        locate_first_bend=True,
    )
    assert audit.first_bend_slot == 1071
    assert audit.first_bend_gcd == 274177
    assert audit.block_locator_gcds <= 2 * max(1, audit.full_blocks.bit_length()) + 1
    assert audit.leaf_locator_gcds <= 4 + 2 * max(1, audit.baby_width.bit_length())
    assert audit.block_locator_gcds + audit.leaf_locator_gcds < audit.baby_width

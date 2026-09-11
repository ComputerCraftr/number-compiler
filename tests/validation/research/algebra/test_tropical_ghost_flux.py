from devtools.experiments.algebra.tropical_ghost_flux import (
    TropicalDivisorState,
    enriched_tropical_phase_compression_audit,
    tropical_addition_nonclosure_audit,
    tropical_axis_reconstruction_audit,
    tropical_block_composition_audit,
    tropical_divisor_semiring_audit,
    tropical_ghost_flux_frontier,
    tropical_multiplicity_lift_scaling_audit,
    tropical_saturation_deletion_audit,
    tropical_tie_cancellation_audit,
)
from devtools.paths import repository_root


def test_factor_free_divisor_lattice_is_exact_saturated_tropical_algebra() -> None:
    audit = tropical_divisor_semiring_audit(45, 3, 15)
    assert audit.factor_truth == ((3, 2), (5, 1))
    assert audit.product_divisor == 45
    assert audit.meet_divisor == 3
    assert audit.join_divisor == 15
    assert audit.local_product_heights == audit.local_expected_heights
    assert audit.saturated_multiplication_exact
    assert audit.meet_is_componentwise_min
    assert audit.join_is_componentwise_max
    assert audit.factor_free_operations

    a = TropicalDivisorState(315, 3)
    b = TropicalDivisorState(315, 5)
    c = TropicalDivisorState(315, 21)
    assert a.multiply(b).multiply(c) == a.multiply(b.multiply(c))
    assert a.meet(b).meet(c) == a.meet(b.meet(c))
    assert a.join(b).join(c) == a.join(b.join(c))
    assert a.multiply(TropicalDivisorState.one(315)) == a


def test_tropical_block_has_constant_node_state_but_still_scans_every_source_atom() -> (
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
        audit = tropical_block_composition_audit(
            family,
            parameter,
            start=start,
            span=span,
        )
        assert audit.exact
        assert audit.tropical_divisor == expected == audit.direct_flux_gcd
        assert audit.state_divisor_fields_per_node == 1
        assert audit.state_constant_size
        assert audit.leaf_source_gcds == span
        assert audit.semiring_compositions == span - 1
        assert audit.semiring_combine_gcds == span - 1
        assert audit.source_work_linear_in_span
        assert not audit.asymptotic_source_work_improved


def test_affine_ghost_is_equal_valuation_tropical_tie_cancellation() -> None:
    expected = {
        ("fermat", 5): (641, 5),
        ("mersenne", 11): (23, 1),
        ("mersenne", 29): (233, 4),
    }
    for key, (factor, slot) in expected.items():
        audit = tropical_tie_cancellation_audit(*key)
        assert audit.hidden_factor == factor
        assert audit.singular_slot == slot
        assert audit.regular_input_valuations == (0, 0)
        assert audit.singular_input_valuations == (0, 0)
        assert audit.plain_tropical_regular_sum == 0
        assert audit.plain_tropical_singular_sum == 0
        assert audit.actual_regular_sum_valuation == 0
        assert audit.actual_singular_sum_valuation >= 1
        assert audit.singular_excess_valuation >= 1
        assert audit.plain_tropical_signatures_equal
        assert not audit.plain_tropical_detects_defect
        assert audit.supertropical_tie_marks_regular
        assert audit.supertropical_tie_marks_singular
        assert not audit.supertropical_tie_distinguishes_defect
        assert audit.regular_residue_sum != 0
        assert audit.singular_residue_sum == 0
        assert audit.enriched_residue_phase_detects_defect
        assert audit.hidden_axis_required


def test_divisor_only_tropical_state_is_not_closed_under_ring_addition() -> None:
    expected = {
        ("fermat", 5): 641,
        ("mersenne", 11): 23,
        ("mersenne", 29): 233,
    }
    for key, factor in expected.items():
        audit = tropical_addition_nonclosure_audit(*key)
        assert audit.hidden_factor == factor
        assert audit.regular_input_divisors == (1, 1)
        assert audit.cancelling_input_divisors == (1, 1)
        assert audit.same_divisor_inputs
        assert audit.regular_sum_divisor == 1
        assert audit.cancelling_sum_divisor == factor
        assert audit.different_exact_sum_divisors
        assert not audit.divisor_only_addition_closed


def test_known_hidden_axes_make_tropical_flux_a_small_periodic_counting_problem() -> (
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
        audit = tropical_axis_reconstruction_audit(
            family,
            parameter,
            start=start,
            span=span,
        )
        assert audit.exact
        assert audit.reconstructed_divisor == expected == audit.direct_flux_gcd
        assert audit.interior_atom_evaluations == 0
        assert audit.compact_given_factor_axes
        assert audit.factor_truth_only
        assert not audit.factor_free_axis_discovery_available
        assert all(row.exact for row in audit.rows)

    m29 = tropical_axis_reconstruction_audit(
        "mersenne",
        29,
        start=1,
        span=399,
    )
    by_factor = {row.prime: row for row in m29.rows}
    assert by_factor[233].first_slot_residue == 4
    assert by_factor[233].q_level_hits == 2
    assert by_factor[233].full_product_valuation == 2
    assert by_factor[233].saturated_kernel_height == 1
    assert by_factor[1103].q_level_hits == 1
    assert by_factor[2089].q_level_hits == 1


def test_fully_enriched_tropical_phase_returns_to_the_original_residue_on_squarefree_controls() -> (
    None
):
    for key in (("fermat", 5), ("mersenne", 11), ("mersenne", 29)):
        audit = enriched_tropical_phase_compression_audit(*key)
        assert audit.squarefree
        assert audit.radical == audit.modulus
        assert audit.universal_leading_phase_modulus == audit.modulus
        assert audit.universal_phase_bits == audit.original_residue_bits
        assert not audit.strict_phase_state_compression
        assert audit.factor_truth_only


def test_saturated_tropical_support_cannot_reverse_after_overflow() -> None:
    for key in (("fermat", 5), ("mersenne", 11), ("mersenne", 29)):
        audit = tropical_saturation_deletion_audit(*key)
        assert audit.same_saturated_state
        assert audit.deletion_outputs_differ
        assert not audit.exact_delete_from_saturated_state_exists
        assert audit.factor_free_n_squared_lift_distinguishes


def test_factor_free_overflow_lift_grows_linearly_while_factor_indexed_counter_is_small() -> (
    None
):
    f5 = tropical_multiplicity_lift_scaling_audit(
        "fermat",
        5,
        multiplicity_horizon=511,
    )
    assert f5.exponent_in_candidate == 1
    assert f5.required_power_of_modulus == 511
    assert (
        f5.factor_free_lift_description_bits_upper_bound
        == 511 * ((1 << 32) + 1).bit_length()
    )
    assert f5.factor_free_lift_bits_linear_in_horizon
    assert (
        f5.factor_indexed_counter_bits_upper_bound
        < f5.factor_free_lift_description_bits_upper_bound
    )
    assert f5.factor_indexed_counter_requires_hidden_axis


def test_tropical_research_frontier_does_not_fake_source_closure() -> None:
    frontier = tropical_ghost_flux_frontier()
    assert frontier.divisor_semiring_closed
    assert frontier.factor_free_divisor_state_closed
    assert frontier.tropical_block_state_constant_size
    assert not frontier.tropical_block_source_work_polylogarithmic
    assert not frontier.plain_min_plus_source_detects_tie_defect
    assert frontier.enriched_residue_phase_detects_given_axis
    assert not frontier.factor_free_enriched_phase_available
    assert not frontier.fully_enriched_phase_strictly_smaller_on_squarefree_controls
    assert not frontier.divisor_only_addition_closed
    assert frontier.known_axis_flux_compact
    assert frontier.known_axis_flux_factor_truth_only
    assert not frontier.saturated_state_reversible
    assert not frontier.factor_free_overflow_state_polylogarithmic
    assert not frontier.production_source_extractor_available
    assert frontier.status == "UNKNOWN"


def test_tropical_ghost_research_is_not_reachable_from_production_sources() -> None:

    root = repository_root() / "src" / "number_compiler"
    source = "\n".join(path.read_text() for path in root.glob("*.py"))
    assert "devtools.experiments.algebra.tropical_ghost_flux" not in source
    assert "tropical_ghost_flux" not in source

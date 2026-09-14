from math import gcd

from devtools.experiments.power_numbers.special_transverse_jet import (
    SpecialJetProgressionSpec,
    build_special_jet_interval,
    dyadic_jet_translation_audit,
    fermat_jet_binomial_normal_form_audit,
    first_special_transverse_singularity,
    jet_holonomy_shift_audit,
    special_jet_window_complexity,
    special_jet_window_search_audit,
    transverse_jet_frontier,
)


def test_transverse_connection_first_pole_is_special_smallest_factor() -> None:
    expected = {
        ("fermat", 5): (5, 641, 6700417),
        ("mersenne", 11): (1, 23, 89),
        ("mersenne", 29): (4, 233, 1103 * 2089),
    }
    for key, (slot, factor, cofactor) in expected.items():
        audit = first_special_transverse_singularity(*key)
        assert audit.found
        assert audit.first_slot == slot
        assert audit.singular_index == factor
        assert audit.denominator_gcd == factor
        assert audit.coefficient_modulus is not None
        assert audit.coefficient_gcd == cofactor
        assert gcd(audit.coefficient_modulus, audit.modulus) == cofactor
        assert audit.prior_admissible_denominators_units
        assert audit.candidate_derived


def test_prime_controls_have_no_transverse_pole_before_sqrt_bound() -> None:
    for key in (("fermat", 4), ("mersenne", 13)):
        audit = first_special_transverse_singularity(*key)
        assert not audit.found
        assert audit.denominator_gcd == 1
        assert audit.coefficient_modulus is None
        assert audit.slots_tested == audit.max_slot


def test_full_special_jet_window_is_exact_noncancelling_composite_observer() -> None:
    expected = {
        ("fermat", 4): ("CLEAR", None),
        ("fermat", 5): ("SPLIT", 641),
        ("mersenne", 11): ("SPLIT", 23),
        ("mersenne", 13): ("CLEAR", None),
        # All three known factors of M29 occur below sqrt, so the root gcd is N;
        # left-first descent still yields the first proper divisor.
        ("mersenne", 29): ("FULL", 233),
    }
    for key, (status, factor) in expected.items():
        audit = special_jet_window_search_audit(*key)
        assert audit.status == status
        assert audit.proper_factor == factor
        assert audit.product_atom_evaluations == audit.candidate_count
        assert audit.product_multiplications == audit.candidate_count - 1
        assert audit.same_product_tree_work
        assert audit.same_witness_when_composite
        assert audit.factor_enumeration == 0


def test_jet_window_reinterprets_existing_special_factor_product_tree_not_new_work() -> (
    None
):
    for key in (
        ("fermat", 4),
        ("fermat", 5),
        ("mersenne", 11),
        ("mersenne", 13),
        ("mersenne", 29),
    ):
        audit = special_jet_window_search_audit(*key)
        assert audit.existing_factor_window_candidate_count == audit.candidate_count
        assert (
            audit.existing_factor_window_product_multiplications
            == audit.product_multiplications
        )
        assert (
            audit.existing_factor_window_product_depth == audit.product_parallel_depth
        )
        assert audit.same_product_tree_work


def test_one_step_holonomy_is_constant_boundary_and_exposes_nonunit_when_it_leaves() -> (
    None
):
    # F5 slots are 1+128m and the first hidden factor is slot m=5 -> 641.
    entering = jet_holonomy_shift_audit("fermat", 5, start=1, span=4, shift=1)
    assert entering.boundary_width == 1
    assert entering.overlap == 3
    assert entering.cross_identity_exact
    assert entering.inverse_update_available
    assert entering.inverse_update_exact
    assert entering.leaving_gcd == 1
    assert entering.entering_gcd == 641
    assert gcd(entering.shifted_product, entering.old_product * 0 + 4294967297) == 641

    leaving = jet_holonomy_shift_audit("fermat", 5, start=5, span=4, shift=1)
    assert leaving.boundary_width == 1
    assert leaving.cross_identity_exact
    assert leaving.leaving_gcd == 641
    assert leaving.local_forcing_is_singular
    assert not leaving.inverse_update_available
    assert not leaving.inverse_update_exact


def test_powering_translation_to_dyadic_sibling_reopens_entire_boundary() -> None:
    for exponent in range(9):
        span = 1 << exponent
        audit = dyadic_jet_translation_audit(span)
        assert audit.one_step_boundary_width == 1
        assert audit.sibling_shift == span
        assert audit.sibling_overlap == 0
        assert audit.sibling_boundary_width == span
        assert audit.reduced_ratio_numerator_degree == span
        assert audit.reduced_ratio_denominator_degree == span
        assert audit.exact_new_boundary_terms == span
        assert not audit.bounded_state_sibling_translation_closed


def test_balanced_binary_interval_has_log_depth_but_linear_total_work() -> None:
    spec = SpecialJetProgressionSpec.build("fermat", 5)
    for exponent in range(9):
        span = 1 << exponent
        block = build_special_jet_interval(spec, 1, span)
        assert block.span == span
        assert block.atom_evaluations == span
        assert block.multiplications == span - 1
        assert block.parallel_depth == exponent


def test_fermat_window_depth_is_exponential_in_compressed_index_even_before_work() -> (
    None
):
    # For F_n, floor(sqrt(F_n))=2^(2^(n-1)) and C=2^(n+2), so the
    # admissible slot count is 2^(2^(n-1)-n-2)-1 once the exponent is positive.
    for n in (4, 5, 6, 8, 10):
        audit = special_jet_window_complexity("fermat", n)
        exponent = (1 << (n - 1)) - n - 2
        expected = 0 if exponent <= 0 else (1 << exponent) - 1
        assert audit.candidate_count == expected
        assert audit.balanced_product_work == max(0, expected - 1)
        assert audit.balanced_parallel_depth == (
            0 if expected <= 1 else (expected - 1).bit_length()
        )
        assert audit.work_linear_in_window
        assert audit.depth_logarithmic_in_window
    assert special_jet_window_complexity("fermat", 10).balanced_parallel_depth == 500


def test_mersenne_window_has_log_depth_but_exponential_leaf_work_in_exponent() -> None:
    rows = [special_jet_window_complexity("mersenne", p) for p in (11, 13, 29, 31, 61)]
    assert [row.candidate_count for row in rows[:3]] == [2, 3, 399]
    assert all(
        row.balanced_product_work == max(0, row.candidate_count - 1) for row in rows
    )
    assert rows[-1].candidate_count > 1_000_000
    assert rows[-1].balanced_parallel_depth < rows[-1].parameter


def test_fermat_holonomy_has_exact_sparse_power_of_two_binomial_normal_form() -> None:
    for start, span in ((1, 4), (2, 8), (1, 64), (1, 511)):
        audit = fermat_jet_binomial_normal_form_audit(5, start=start, span=span)
        assert audit.center == 1 << 25
        assert audit.stride * audit.center == audit.modulus - 1
        assert audit.exact
        assert audit.binomial_lower_index == span
        assert audit.expanded_factor_count == span
        assert not audit.compact_modular_binomial_evaluator_available


def test_transverse_jet_research_does_not_fake_release_closure() -> None:
    frontier = transverse_jet_frontier()
    assert frontier.transverse_defect_semantics_closed
    assert frontier.special_progression_projection_closed
    assert frontier.one_step_left_right_holonomy_closed
    assert not frontier.dyadic_sibling_translation_bounded_state_closed
    assert not frontier.full_window_evaluator_polylog_work
    assert not frontier.production_source_extractor_available
    assert frontier.status == "UNKNOWN"

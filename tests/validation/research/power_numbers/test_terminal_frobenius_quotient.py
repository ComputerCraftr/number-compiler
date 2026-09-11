from devtools.experiments.power_numbers.terminal_frobenius_quotient import (
    cayley_square_commutation_audit,
    dickson_orientation_power_of_two,
    fermat_cofactor_sign_cancellation_audit,
    fermat_global_cyclotomic_probe,
    fermat_local_cyclotomic_frobenius_audit,
    fermat_terminal_fold_formula,
    quadratic_cayley_trace_quotient,
)
from number_compiler.sequences.power_numbers.numbers import fermat_number


def _r1(n: int) -> int:
    N = fermat_number(n)
    t = pow(2, 1 << (n - 2), N)
    return (t + pow(t, -1, N)) % N


def test_quadratic_additive_probe_descends_to_base_ring_lucas_trace() -> None:
    for n in (3, 4, 5, 6):
        N = fermat_number(n)
        d = _r1(n)
        row = quadratic_cayley_trace_quotient(N, d)
        assert row.norm_gcd == 1
        assert row.trace is not None
        assert row.discriminant is not None
        assert row.square_multiplier is not None
        assert row.discriminant_matches_radicand_square_class
        # For a=b=1 and d^2=2, the closed trace is -6-4d.
        assert row.trace == (-6 - 4 * d) % N

        commute = cayley_square_commutation_audit(N, d)
        assert commute.exact
        assert commute.trace_after_pair_square == commute.lucas_trace_step


def test_dickson_orientation_is_the_missing_frobenius_coefficient_not_the_trace() -> (
    None
):
    # B_(2e)=D_e B_e and D_(2e)=D_e^2-2 are an exact rank-two base-ring
    # quotient of powers of the Cayley ratio.  Trace alone does not retain the
    # +/- orientation; the second coordinate does.
    N = fermat_number(4)
    d = _r1(4)
    q = quadratic_cayley_trace_quotient(N, d)
    assert q.trace is not None
    s0 = dickson_orientation_power_of_two(q.trace, 0, N)
    s3 = dickson_orientation_power_of_two(q.trace, 3, N)
    assert s0.exponent == 1 and s0.orientation == 1
    assert s3.exponent == 8 and s3.compositions == 3


def test_local_power_two_cyclotomic_frobenius_equation_is_exact_next_split_bit() -> (
    None
):
    f4 = fermat_local_cyclotomic_frobenius_audit(4, 2, 65537)
    assert f4.equation_exact
    assert f4.expected_split_bit
    assert f4.stride_parity == 0
    assert f4.frobenius_rhs_sign == 1

    # Both F5 factors reach level 1 but fail level 2.  The same local equation
    # returns 1-X rather than 1+X, with no character-product cancellation.
    for q in (641, 6700417):
        row = fermat_local_cyclotomic_frobenius_audit(5, 2, q)
        assert row.equation_exact
        assert not row.expected_split_bit
        assert row.stride_parity == 1
        assert row.frobenius_rhs_sign == -1


def test_composite_cofactor_has_same_dyadic_bit_and_explains_global_blindness() -> None:
    for q in (641, 6700417):
        row = fermat_cofactor_sign_cancellation_audit(5, 2, q)
        assert row.same_parity
        assert row.factor_parity == row.cofactor_parity == 1
        assert row.candidate_residue_mod_2m == 1
        assert row.local_actions_compose_to_identity_on_X
        assert "squares it away" in row.conclusion


def test_candidate_global_partial_frobenius_probe_separates_F4_F5_without_becoming_the_theorem() -> (
    None
):
    f3 = fermat_global_cyclotomic_probe(3, 2)
    f4 = fermat_global_cyclotomic_probe(4, 2)
    f5 = fermat_global_cyclotomic_probe(5, 2)
    f6 = fermat_global_cyclotomic_probe(6, 2)
    assert f3.residue_is_one and f4.residue_is_one
    assert not f5.residue_is_one and not f6.residue_is_one
    assert f4.nonzero_coefficients == 1
    assert f5.nonzero_coefficients > 1
    for row in (f3, f4, f5, f6):
        assert not row.scalable
        assert row.candidate_derived
        # One squaring per exponent bit remains visible; this cannot be called
        # the binary-powered terminal selector yet.
        assert row.exponent_squarings >= (1 << row.parameter) - 1


def test_terminal_frobenius_carrier_folds_symbolically_to_two_binomial_copies() -> None:
    for n in (3, 4, 5, 9):
        row = fermat_terminal_fold_formula(n)
        assert row.half_degree_log2 == (1 << n) - 1
        assert row.fold_copies_per_coefficient == 2
        assert "C(2m,m)" in row.constant_formula
        assert "C(2m,r+m)" in row.nonconstant_formula
        assert not row.carrier_materialized
        assert not row.raw_power_replayed
        assert not row.factor_free_fast_evaluator_available


def test_mersenne_additive_frobenius_probe_is_exactly_lucas_lehmer_trace_quotient() -> (
    None
):
    from devtools.experiments.power_numbers.terminal_frobenius_quotient import (
        mersenne_cayley_lucas_quotient,
    )

    for p in (5, 7, 11, 13, 23):
        row = mersenne_cayley_lucas_quotient(p)
        assert row.exact_cayley_identity
        assert row.cayley_unit == (2, 1)
        assert row.cayley_norm == 1
        assert row.trace == 4
        assert row.lucas_lehmer_seed == 4
        assert not row.extension_state_required


def test_fermat_composite_side_has_total_one_scalar_reix_lucas_quotient() -> None:
    from devtools.experiments.power_numbers.terminal_frobenius_quotient import (
        fermat_reix_lucas_quotient,
    )

    expected = {1: True, 2: True, 3: True, 4: True, 5: False, 6: False}
    for n, prime in expected.items():
        row = fermat_reix_lucas_quotient(n)
        assert row.trace_seed == 5
        assert row.quadratic_radicand == 21
        assert row.horizon == (1 << n) - 2
        assert row.terminal_zero is prime
        assert row.theorem_total
        assert row.factor_enumeration == 0
        assert row.ring_squarings == row.horizon
        assert not row.scalable_powering


def test_shared_special_lucas_terminal_quotient_classifies_composite_side_without_factor_or_crt_state() -> (
    None
):
    from devtools.experiments.power_numbers.terminal_frobenius_quotient import (
        special_lucas_terminal_quotient,
    )

    rows = [
        special_lucas_terminal_quotient("fermat", 4),
        special_lucas_terminal_quotient("fermat", 5),
        special_lucas_terminal_quotient("mersenne", 13),
        special_lucas_terminal_quotient("mersenne", 11),
        special_lucas_terminal_quotient("mersenne", 15),
    ]
    assert [r.classification for r in rows] == [
        "prime",
        "composite",
        "prime",
        "composite",
        "composite",
    ]
    for row in rows:
        assert row.quotient_cells == 1
        assert row.retained_extension_coordinates == 0
        assert row.factor_enumeration == 0
        assert row.oracle_calls == 0
        assert row.total_composite_safe
    # The composite-exponent M15 case rejects symbolically before any LL work.
    assert rows[-1].ring_squarings == 0
    # The scalar quotient exists, but direct powering still pays the horizon.
    assert rows[0].ring_squarings == rows[0].horizon
    assert not rows[0].scalable_powering


def test_existing_quadratic_power_is_exact_temporal_reuse_but_source_injection_stays_fail_closed() -> (
    None
):
    from devtools.experiments.power_numbers.terminal_frobenius_quotient import (
        existing_squaring_morphism_reuse_audit,
    )

    rows = [
        existing_squaring_morphism_reuse_audit("fermat", 4),
        existing_squaring_morphism_reuse_audit("fermat", 5),
        existing_squaring_morphism_reuse_audit("mersenne", 13),
        existing_squaring_morphism_reuse_audit("mersenne", 11),
    ]
    for row in rows:
        assert row.operator_depth == row.horizon
        # Building the semantic power is logarithmic in the horizon.
        assert row.operator_build_compositions <= 2 * row.horizon.bit_length()
        assert row.semantic_power_compositions <= 2 * row.horizon.bit_length()
        # Raw specialization still replays one trace square per level.
        assert row.raw_apply_trace_squarings == row.horizon
        # The known pure-domain code would hit the target exactly after h steps,
        # but assigning it before classification would assume the result.
        assert row.prime_conditional_source_code == row.horizon + 1
        assert row.prime_conditional_terminal_output
        assert row.semantic_source_code is None
        assert not row.source_code_candidate_derived
        assert not row.direct_log_time_terminal_decision_ready
        assert "source code" in row.blocker


def test_r_level_local_frobenius_chunk_is_exact_on_prime_and_composite_controls_without_expansion() -> (
    None
):
    from devtools.experiments.power_numbers.terminal_frobenius_chunk import (
        special_local_frobenius_chunk_audit,
    )

    rows = [
        special_local_frobenius_chunk_audit("fermat", 4, 1, 11, 65537),
        special_local_frobenius_chunk_audit("fermat", 5, 1, 26, 641),
        special_local_frobenius_chunk_audit("fermat", 5, 1, 26, 6700417),
        special_local_frobenius_chunk_audit("mersenne", 13, 1, 11, 8191),
        special_local_frobenius_chunk_audit("mersenne", 11, 1, 9, 23),
        special_local_frobenius_chunk_audit("mersenne", 11, 1, 9, 89),
    ]
    assert [row.all_levels_pass for row in rows] == [
        True,
        False,
        False,
        True,
        False,
        False,
    ]
    assert rows[0].stride_residue == rows[3].stride_residue == 0
    assert rows[0].folded_x_coefficient == rows[3].folded_x_coefficient == 1
    assert rows[1].stride_residue == 10
    assert rows[1].folded_x_coefficient == 0
    assert not rows[4].reaches_start_boundary and rows[4].stride_residue is None
    for row in rows:
        assert row.factor_truth_only
        assert row.polynomial_terms_materialized == 0
        assert row.one_level_replays == 0


def test_r_level_chunk_composition_matches_direct_stride_residue_and_short_circuit_semantics() -> (
    None
):
    from devtools.experiments.power_numbers.terminal_frobenius_chunk import (
        special_frobenius_chunk_composition_audit,
    )

    # F5's 641 factor passes the first remaining bit then fails the second.
    f5 = special_frobenius_chunk_composition_audit("fermat", 5, 1, 1, 1, 641)
    assert f5.left_zero_class
    assert f5.right_reaches_boundary
    assert f5.right_zero_class is False
    assert f5.combined_stride_residue == f5.full_stride_residue == 2
    assert f5.residue_composition_exact and f5.semantic_composition_exact

    for row in (
        special_frobenius_chunk_composition_audit("fermat", 4, 1, 5, 6, 65537),
        special_frobenius_chunk_composition_audit("mersenne", 13, 1, 5, 6, 8191),
    ):
        assert row.left_zero_class and row.right_zero_class and row.full_zero_class
        assert row.combined_stride_residue == row.full_stride_residue == 0
        assert row.residue_composition_exact and row.semantic_composition_exact
        assert row.polynomial_terms_materialized == row.one_level_replays == 0


def test_terminal_threshold_now_uses_frobenius_chunk_surface_but_does_not_fake_extraction() -> (
    None
):
    from number_compiler.sequences.power_numbers.terminal_threshold import (
        terminal_threshold_probe,
    )

    for family, parameter in (
        ("fermat", 4),
        ("fermat", 5),
        ("mersenne", 11),
        ("mersenne", 13),
    ):
        row = terminal_threshold_probe(family, parameter)
        assert row.status == "UNKNOWN"
        assert row.method == "constraint-pullback-unresolved"
        assert row.carrier_states_enumerated == 0
        assert row.raw_specialization_squarings == 0

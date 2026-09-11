from devtools.experiments.power_numbers.terminal_divisor_norm import (
    aggregate_artin_blind_audit,
    fermat_full_power_residue_phase_truth_audit,
    linear_galois_fitting_blind_audit,
    quadratic_subresultant_blind_audit,
    raw_power_lower_bound_audit,
    regular_artin_euler_coefficient_truth_audit,
    repeated_factor_multiplicity_guard,
    support_euler_coefficient_target,
    terminal_divisor_norm_truth_audit,
)


def test_fermat_terminal_divisor_norm_is_exact_on_prime_and_even_packet_composite() -> (
    None
):
    f4 = terminal_divisor_norm_truth_audit("fermat", 4)
    f5 = terminal_divisor_norm_truth_audit("fermat", 5)
    assert (
        f4.candidate_is_prime_by_truth
        and f4.divisor_norm_exists
        and f4.divisor_norm_iff_prime
    )
    assert (
        not f5.candidate_is_prime_by_truth
        and not f5.divisor_norm_exists
        and f5.divisor_norm_iff_prime
    )
    assert [row.residue_degree_log2 for row in f4.local_rows] == [0]
    assert [row.residue_degree_log2 for row in f5.local_rows] == [25, 25]
    assert all(row.multiplicity_strictly_below_residue_degree for row in f5.local_rows)


def test_mersenne_real_cyclotomic_terminal_norm_removes_sqrt3_at_final_level() -> None:
    m13 = terminal_divisor_norm_truth_audit("mersenne", 13)
    m11 = terminal_divisor_norm_truth_audit("mersenne", 11)
    assert (
        m13.candidate_is_prime_by_truth
        and m13.divisor_norm_exists
        and m13.divisor_norm_iff_prime
    )
    assert (
        not m11.candidate_is_prime_by_truth
        and not m11.divisor_norm_exists
        and m11.divisor_norm_iff_prime
    )
    assert [row.local_capacity_v2 for row in m13.local_rows] == [13]
    assert [row.residue_degree_log2 for row in m13.local_rows] == [0]
    assert [row.local_capacity_v2 for row in m11.local_rows] == [3, 3]
    assert [row.residue_degree_log2 for row in m11.local_rows] == [8, 8]


def test_regular_artin_euler_coefficient_is_the_non_cancelling_support_statistic() -> (
    None
):
    for family, parameter, expected in (
        ("fermat", 4, True),
        ("fermat", 5, False),
        ("mersenne", 13, True),
        ("mersenne", 11, False),
    ):
        row = regular_artin_euler_coefficient_truth_audit(family, parameter)
        assert row.coefficient_nonzero is expected
        assert row.ideal_norm_equivalent
    # Bounded prime controls have exactly d norm preimages of a prime ideal.
    assert (
        regular_artin_euler_coefficient_truth_audit(
            "fermat", 4
        ).bounded_exact_coefficient
        == 2048
    )
    assert (
        regular_artin_euler_coefficient_truth_audit(
            "mersenne", 13
        ).bounded_exact_coefficient
        == 2048
    )


def test_full_root_of_unity_reciprocity_phase_still_cancels_on_f5() -> None:
    f4 = fermat_full_power_residue_phase_truth_audit(4)
    f5 = fermat_full_power_residue_phase_truth_audit(5)
    assert f4.candidate_is_prime_by_truth
    assert f4.aggregate_matches_prime_formula
    # Strong adversary: F5 is composite but its complete 64th power-residue
    # phase of base 3 equals the same prime-formula phase.  A scalar Artin
    # value, even root-of-unity-valued rather than +/-1, is insufficient.
    assert not f5.candidate_is_prime_by_truth
    assert f5.local_exponents == (49, 44)
    assert f5.aggregate_exponent == 29 == f5.prime_formula_exponent
    assert f5.aggregate_matches_prime_formula


def test_fixed_linear_fitting_data_is_blind_by_regular_module_theorem() -> None:
    row = linear_galois_fitting_blind_audit(5)
    assert row.same_linear_signature
    assert row.split_characteristic_polynomial == row.nonsplit_characteristic_polynomial
    assert row.split_characteristic_polynomial[0] == -1
    assert row.split_characteristic_polynomial[-1] == 1


def test_repeated_factor_size_bound_prevents_false_ideal_norms() -> None:
    # Near-terminal hypothetical factors are the hardest multiplicity case:
    # residue degree is only 2, but the factor is already > sqrt(candidate),
    # hence a proper factor can occur only once.
    assert repeated_factor_multiplicity_guard("fermat", 5, 31, 1)
    assert not repeated_factor_multiplicity_guard("fermat", 5, 31, 2)
    assert repeated_factor_multiplicity_guard("mersenne", 13, 12, 1)
    assert not repeated_factor_multiplicity_guard("mersenne", 13, 12, 2)


def test_every_aggregate_terminal_artin_character_is_forced_blind_by_special_form() -> (
    None
):
    for family, parameter in (
        ("fermat", 4),
        ("fermat", 5),
        ("mersenne", 11),
        ("mersenne", 13),
    ):
        row = aggregate_artin_blind_audit(family, parameter)
        assert row.aggregate_artin_is_identity
        assert row.all_scalar_characters_blind
    assert aggregate_artin_blind_audit("fermat", 5).candidate_residue == 1
    m11 = aggregate_artin_blind_audit("mersenne", 11)
    assert m11.candidate_residue == (1 << 11) - 1


def test_quadratic_subresultant_and_discriminant_unit_data_do_not_decide_split() -> (
    None
):
    f4 = quadratic_subresultant_blind_audit(4)
    f5 = quadratic_subresultant_blind_audit(5)
    assert f4.all_linear_subresultant_data_units
    assert f5.all_linear_subresultant_data_units
    assert f4.discriminant_gcd == f5.discriminant_gcd == 1
    assert f4.derivative_resultant_gcd == f5.derivative_resultant_gcd == 1
    assert f4.splitting_truth and not f5.splitting_truth


def test_raw_powering_has_linear_addition_chain_depth_without_new_quotient() -> None:
    f4 = raw_power_lower_bound_audit("fermat", 4)
    m13 = raw_power_lower_bound_audit("mersenne", 13)
    assert f4.squaring_depth == 11 == f4.minimum_generic_multiplications
    assert m13.squaring_depth == 11 == m13.minimum_generic_multiplications
    assert f4.binary_composition_cannot_reduce_raw_evaluation
    assert m13.binary_composition_cannot_reduce_raw_evaluation


def test_surviving_support_euler_target_is_explicitly_fail_closed() -> None:
    for family, parameter in (
        ("fermat", 4),
        ("fermat", 5),
        ("mersenne", 11),
        ("mersenne", 13),
    ):
        target = support_euler_coefficient_target(family, parameter)
        assert target.aggregate_artin_rejected
        assert target.fixed_linear_fitting_rejected
        assert not target.factor_free_evaluator_available
        assert target.status == "UNKNOWN"

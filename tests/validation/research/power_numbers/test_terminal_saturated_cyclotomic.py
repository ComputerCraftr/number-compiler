from devtools.experiments.power_numbers.terminal_saturated_cyclotomic import (
    candidate_saturated_cyclotomic_probe,
    cyclotomic_factor_audit,
    cyclotomic_witness_cost_audit,
    terminal_two_power_cyclotomic_criterion,
)


def test_special_terminal_congruence_is_exact_low_degree_cyclotomic_extension_condition() -> (
    None
):
    f4 = terminal_two_power_cyclotomic_criterion("fermat", 4)
    assert f4.conductor_v2 == 8
    assert f4.frobenius_degree == 1
    assert f4.candidate_residue == 1
    assert f4.subgroup_residues == (1,)

    f5 = terminal_two_power_cyclotomic_criterion("fermat", 5)
    assert f5.conductor_v2 == 16
    assert f5.frobenius_degree == 1

    m11 = terminal_two_power_cyclotomic_criterion("mersenne", 11)
    assert m11.conductor_v2 == 4
    assert m11.frobenius_degree == 2
    assert set(m11.subgroup_residues) == {1, 15}

    m13 = terminal_two_power_cyclotomic_criterion("mersenne", 13)
    assert m13.conductor_v2 == 5
    assert m13.frobenius_degree == 2
    assert set(m13.subgroup_residues) == {1, 31}


def test_factor_backed_controls_match_cyclotomic_extension_existence_exactly() -> None:
    rows = (
        cyclotomic_factor_audit("fermat", 4, (65537,)),
        cyclotomic_factor_audit("fermat", 5, (641, 6700417)),
        cyclotomic_factor_audit("mersenne", 11, (23, 89)),
        cyclotomic_factor_audit("mersenne", 13, (8191,)),
    )
    assert [row.extension_exists_by_factor_truth for row in rows] == [
        True,
        False,
        False,
        True,
    ]
    assert all(row.agrees_with_prime_truth for row in rows)
    assert rows[1].local_passes == (False, False)
    assert rows[2].local_passes == (False, False)
    assert all(row.factor_enumeration == 0 for row in rows)


def test_obvious_low_degree_witness_construction_is_not_a_temporal_shortcut() -> None:
    for family, parameter in (
        ("fermat", 4),
        ("fermat", 16),
        ("mersenne", 13),
        ("mersenne", 10007),
    ):
        row = cyclotomic_witness_cost_audit(family, parameter)
        assert row.total_sequential_squarings == row.classical_horizon
        assert not row.cheaper_than_classical_chain
        assert not row.candidate_derived_compact_constructor_known


def test_candidate_probe_stays_fail_closed_despite_exact_semantic_equivalence() -> None:
    for family, parameter in (
        ("fermat", 4),
        ("fermat", 5),
        ("mersenne", 11),
        ("mersenne", 13),
    ):
        row = candidate_saturated_cyclotomic_probe(family, parameter)
        assert row["status"] == "UNKNOWN"
        assert row["method"] == "candidate-saturated-cyclotomic-witness-unavailable"
        assert row["factor_enumeration"] == 0
        assert row["raw_specialization_squarings"] == 0
        assert row["candidate_derived_witness"] is None


def test_low_degree_orbit_polynomial_payload_is_exactly_the_missing_root_or_trace() -> (
    None
):
    f4 = terminal_two_power_cyclotomic_criterion("fermat", 4)
    assert (
        f4.frobenius_degree == 1
    )  # Psi=X-zeta: coefficient is the primitive root itself.
    m13 = terminal_two_power_cyclotomic_criterion("mersenne", 13)
    assert (
        m13.frobenius_degree == 2
    )  # Psi=X^2-TX+1: T=zeta+zeta^-1 is the missing trace.

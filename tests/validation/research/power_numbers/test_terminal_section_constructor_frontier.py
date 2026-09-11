from devtools.experiments.power_numbers.terminal_section_constructor_frontier import (
    cyclotomic_section_equivalence,
    fermat_high_two_adic_aks_tradeoff,
    section_constructor_frontier,
)


def test_fermat_orbit_polynomial_section_is_square_root_extraction() -> None:
    row = cyclotomic_section_equivalence("fermat", 4)
    assert row.frobenius_degree == 1
    assert row.section_equation == "zeta_(v+1)^2 = zeta_v"
    assert row.section_is_quadratic_etale_query
    assert not row.candidate_derived_section_constructor_known


def test_mersenne_orbit_polynomial_section_is_half_angle_square_root() -> None:
    row = cyclotomic_section_equivalence("mersenne", 13)
    assert row.frobenius_degree == 2
    assert row.section_equation == "T_(v+1)^2 = T_v + 2"
    assert row.section_is_quadratic_etale_query
    assert not row.candidate_derived_section_constructor_known


def test_fermat_high_two_adic_aks_endpoints_do_not_close_compact_constructor() -> None:
    small, deep = fermat_high_two_adic_aks_tradeoff(4)
    assert small.k_v2_n_minus_1 == 16
    assert small.u == 1
    assert small.power_condition_squaring_depth == 15
    assert small.polynomial_degree_log2 == 8
    assert not small.compact_section_constructor

    assert deep.u == 12
    assert deep.power_condition_squaring_depth == 0
    assert deep.polynomial_degree_log2 == 30
    assert not deep.compact_section_constructor


def test_fermat_high_two_adic_aks_tradeoff_scales_against_compact_parameter() -> None:
    small, deep = fermat_high_two_adic_aks_tradeoff(16)
    assert small.power_condition_squaring_depth == (1 << 16) - 1
    assert small.polynomial_degree_log2 == 32
    assert deep.power_condition_squaring_depth == 0
    assert deep.polynomial_degree_log2 == 2 * (1 << 16) - 2


def test_frontier_remains_fail_closed_for_both_families() -> None:
    for family, parameter in (("fermat", 4), ("mersenne", 13)):
        row = section_constructor_frontier(family, parameter)
        assert row.semantic_section_law_closed
        assert row.orbit_polynomial_section_collapses_to_square_query
        assert row.saturated_extension_semantics_closed
        assert not row.compact_candidate_constructor_known
        assert row.production_status == "UNKNOWN"

from devtools.experiments.power_numbers.terminal_projective_wreath import (
    ODOMETER_BINARY_HANDLER,
    ProjectiveLucasState,
    candidate_frobenius_section_probe,
    conditional_odometer_section,
    local_frobenius_wreath_audit,
    odometer_identity_on_prefix,
    odometer_section_step,
    odometer_wreath_section,
    projective_lucas_audit,
)


def test_projective_cayley_map_is_exact_and_difference_is_known_square_clock() -> None:
    for family, parameter, steps in (
        ("fermat", 4, 14),
        ("fermat", 5, 12),
        ("mersenne", 13, 11),
        ("mersenne", 11, 9),
    ):
        row = projective_lucas_audit(family, parameter, steps)
        assert row.cayley_commutes
        assert row.difference_clock_exact
        assert row.polynomial_terms_materialized == 0
        assert row.factor_enumeration == 0

    # Prime controls hit the projective target at their classical Lucas horizon.
    assert projective_lucas_audit("fermat", 4, 14).terminal_target_gcd == 65537
    assert projective_lucas_audit("mersenne", 13, 11).terminal_target_gcd == 8191
    # The simple projective target gcd does not by itself expose these composites.
    assert projective_lucas_audit("fermat", 5, 12).proper_target_gcds == ()
    assert projective_lucas_audit("mersenne", 11, 9).proper_target_gcds == ()


def test_projective_sd_formula_matches_homogeneous_formula_without_division() -> None:
    state = ProjectiveLucasState(65537, 3, 7)
    for _ in range(6):
        expected = state.double_sd()
        state = state.double()
        assert (state.sum_coordinate, state.difference_coordinate) == expected
        assert state.difference_gcd == 1


def test_binary_odometer_wreath_recursion_and_conditional_sections_are_exact() -> None:
    even = odometer_wreath_section(10)
    assert even.root_permutation == 0
    assert even.left_section_stride == even.right_section_stride == 5
    assert even.next_boundary_stride == 5

    odd = odometer_wreath_section(5)
    assert odd.root_permutation == 1
    assert (odd.left_section_stride, odd.right_section_stride) == (2, 3)
    assert odd.next_boundary_stride is None

    assert odometer_identity_on_prefix(24, 3)
    assert not odometer_identity_on_prefix(24, 4)
    assert conditional_odometer_section(24, 3) == 3
    assert conditional_odometer_section(24, 4) is None


def test_local_frobenius_section_is_exactly_next_doubled_boundary_on_controls() -> None:
    # F4 passes both queried levels: the root is identity and the section is the
    # exact stride quotient at the doubled boundary.
    f4 = local_frobenius_wreath_audit("fermat", 4, 2, 2, 65537)
    assert f4.reaches_start_boundary
    assert f4.root_permutation == 0
    assert f4.conditional_section_formula_exact
    assert f4.next_boundary_stride == f4.direct_next_boundary_stride
    assert f4.identity_on_span and f4.chunk_all_pass

    # F5/641 fails at the first queried root action.  The next conditional
    # boundary is therefore unavailable rather than silently traversed.
    f5 = local_frobenius_wreath_audit("fermat", 5, 2, 9, 641)
    assert f5.reaches_start_boundary
    assert f5.root_permutation == 1
    assert f5.next_boundary_stride is None
    assert f5.conditional_section_formula_exact
    assert not f5.identity_on_span and not f5.chunk_all_pass

    m13 = local_frobenius_wreath_audit("mersenne", 13, 1, 3, 8191)
    assert m13.root_permutation == 0
    assert m13.conditional_section_formula_exact
    assert m13.identity_on_span and m13.chunk_all_pass

    # M11 does not reach even the starting torus boundary; the transducer
    # short-circuits before manufacturing a section.
    m11 = local_frobenius_wreath_audit("mersenne", 11, 1, 2, 23)
    assert not m11.reaches_start_boundary
    assert m11.stride_quotient is None
    assert m11.conditional_section_formula_exact
    assert not m11.chunk_all_pass


def test_frobenius_odometer_uses_same_binary_piecewise_control_contract() -> None:
    assert ODOMETER_BINARY_HANDLER.canonical_key == (
        "binary-piecewise-handler",
        "frobenius-odometer",
    )
    even = odometer_section_step(10)
    assert even.decision.kind == "ZERO"
    assert even.status == "CONTINUE"
    assert even.next_stride == 5

    odd = odometer_section_step(5)
    assert odd.decision.kind == "ONE"
    assert odd.status == "FAIL"
    assert odd.next_stride is None


def test_wreath_section_probe_stays_fail_closed_for_unfactored_candidate() -> None:
    row = candidate_frobenius_section_probe("fermat", 16, 2, 32750)
    assert row.status == "UNKNOWN"
    assert row.method == "candidate-derived-wreath-section-unavailable"
    assert row.candidate_derived_section is None
    assert row.factor_enumeration == 0
    assert row.tree_nodes_materialized == 0
    assert row.one_level_replays == 0

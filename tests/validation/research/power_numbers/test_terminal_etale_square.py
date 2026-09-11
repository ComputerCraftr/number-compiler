from devtools.experiments.power_numbers.terminal_etale_square import (
    bit_not_successor_closed_audit,
    etale_square_bit_truth_audit,
    fermat_additive_etale_frobenius_probe,
    fermat_prime_phase_compression_audit,
    fermat_pure_order_layer_audit,
    fermat_terminal_root_torsor_audit,
    formal_expression_cannot_see_field_of_definition_audit,
    mersenne_additive_etale_frobenius_probe,
    mersenne_terminal_torus_bit_audit,
    minimal_etale_selector_target,
    special_etale_tile_applicability_audit,
)


def test_single_etale_bit_is_the_required_and_not_the_product_character() -> None:
    f4 = etale_square_bit_truth_audit("fermat", 4, 2)
    f5 = etale_square_bit_truth_audit("fermat", 5, 2)
    assert f4.local_square_bits == (True,)
    assert f4.all_local_square
    assert f4.product_sign == 1

    # This is the exact cancellation that motivated the correction: the
    # required Boolean is False even though the scalar +/-1 product is +1.
    assert f5.local_square_bits == (False, False)
    assert not f5.all_local_square
    assert f5.product_sign == 1
    assert not f5.product_sign_decides_all_local

    m13 = etale_square_bit_truth_audit("mersenne", 13, 1)
    m11 = etale_square_bit_truth_audit("mersenne", 11, 1)
    assert m13.all_local_square
    assert m11.local_square_bits == (False, False)
    assert not m11.all_local_square
    assert m11.product_sign == 1


def test_one_split_bit_is_not_itself_successor_closed() -> None:
    row = bit_not_successor_closed_audit()
    assert row.same_current_bit
    assert row.left_current_bit and row.right_current_bit
    assert row.different_next_bit
    assert row.left_next_bit and not row.right_next_bit
    assert "output query" in row.conclusion


def test_fermat_terminal_certificate_is_one_root_existence_bit() -> None:
    for n in (2, 3, 4, 5, 9):
        row = fermat_terminal_root_torsor_audit(n)
        assert row.terminal_level == (1 << n) - n - 1
        assert row.terminal_root_order == row.candidate_modulus - 1
        assert row.terminal_root_would_be_maximal_order_unit
        assert row.terminal_root_exists_iff_prime
        assert row.global_frobenius_is_formally_identity
        assert not row.raw_power_evaluation_required_by_this_audit
        assert "X^N-X == 0" in row.global_candidate_frobenius_remainder


def test_mersenne_terminal_certificate_is_one_torus_split_bit() -> None:
    for p in (5, 11, 13):
        row = mersenne_terminal_torus_bit_audit(p)
        assert row.terminal_level == p - 2
        assert row.formal_torus_order == 1 << p
        assert row.terminal_split_iff_prime
        assert row.candidate_exponent_residue == (1 << p) - 1
        assert row.global_candidate_action == "inversion"
        assert row.global_action_is_formally_predetermined
        assert row.raw_lucas_lehmer_steps == 0


def test_universal_quadratic_root_has_same_formal_order_on_both_sides() -> None:
    for n, level in ((4, 2), (5, 2), (4, 11)):
        row = fermat_pure_order_layer_audit(n, level)
        assert row.same_formal_order
        assert row.split_universal_root_order == row.nonsplit_universal_root_order
        assert row.universal_root_order_log2 == row.current_order_log2 + 1
        assert row.split_requires_local_v2 == row.universal_root_order_log2
        assert "base-ring membership" in row.conclusion


def test_release_target_explicitly_discards_overstrong_support_objects_and_generic_hardness_claim() -> (
    None
):
    for family, parameter in (
        ("fermat", 4),
        ("fermat", 5),
        ("mersenne", 11),
        ("mersenne", 13),
    ):
        row = minimal_etale_selector_target(family, parameter)
        assert row.output_bits == 1
        assert not row.full_support_required
        assert not row.splitting_weight_required
        assert not row.euler_coefficient_required
        assert not row.generic_higher_residue_hardness_claimed
        assert not row.factor_free_evaluator_available
        assert row.production_status == "UNKNOWN"


def test_special_etale_tile_handoff_is_geometry_first_and_output_selector_last() -> (
    None
):
    rows = tuple(
        special_etale_tile_applicability_audit(family, parameter)
        for family, parameter in (
            ("fermat", 4),
            ("fermat", 5),
            ("mersenne", 11),
            ("mersenne", 13),
        )
    )
    assert [row.closure for row in rows] == [
        "negacyclic",
        "negacyclic",
        "cyclic",
        "cyclic",
    ]
    assert [row.boundary_sign for row in rows] == [-1, -1, 1, 1]
    for row in rows:
        assert row.geometry_key[0] == "special-source-geometry"
        assert row.angular_action_key[0] == "special-germ-transfer"
        assert row.selector_port_key[0] == "special-etale-selector-port"
        assert row.binary_compositions <= 2 * row.powered_span.bit_length()
        assert row.per_level_states_retained == 0
        assert row.exact_source_digits_retained == 0
        assert not row.selector_in_action_identity
        assert row.selector_value is None
        assert not row.candidate_selector_available
        assert not row.certified_tile_family
        assert not row.scheduler_promotion_safe
        assert row.production_status == "RESEARCH_ONLY"

    for family, parameter in (("fermat", 3), ("mersenne", 7)):
        row = special_etale_tile_applicability_audit(family, parameter)
        assert row.selector_value is True
        assert row.candidate_selector_available
        assert row.powered_span == row.binary_compositions == 0
        assert not row.selector_in_action_identity
        assert not row.certified_tile_family
        assert not row.scheduler_promotion_safe
        assert row.production_status == "AWAITING_TILE_FAMILY_CERTIFICATE"


def test_prime_side_terminal_root_compresses_to_n_plus_one_odd_phase_bits() -> None:
    expected = {2: 7, 3: 3, 4: 27}
    for n, phase in expected.items():
        row = fermat_prime_phase_compression_audit(n)
        assert row.odd_phase == phase
        assert row.phase_modulus == 1 << (n + 1)
        assert row.retained_phase_bits == n + 1
        assert row.odd_phase & 1
        assert row.terminal_root_power_residue == 2
        assert row.raw_deep_power_used_for_audit
        assert row.prime_assumption_only


def test_additive_etale_frobenius_is_a_real_composite_witness_but_not_a_prime_certificate() -> (
    None
):
    for n in (3, 4):
        row = fermat_additive_etale_frobenius_probe(n)
        assert row.defect == (0, 0)
        assert not row.composite_witness
        assert not row.prime_certificate
        assert not row.scalable
        assert row.factor_enumeration == 0

    for n in (5, 6):
        row = fermat_additive_etale_frobenius_probe(n)
        assert row.defect != (0, 0)
        assert row.composite_witness
        assert not row.prime_certificate
        assert not row.scalable
        assert row.factor_enumeration == 0
        assert row.ring_multiplications >= (1 << n)


def test_formal_kummer_identities_are_not_the_missing_field_of_definition_bit() -> None:
    row = formal_expression_cannot_see_field_of_definition_audit()
    assert row.same_formal_algebraic_identities
    assert row.relation == "y^2=d"
    assert "R-valued root" in row.missing_property
    assert "base-ring arithmetic" in row.conclusion


def test_mersenne_specific_additive_frobenius_probe_is_one_sided_and_oracle_free() -> (
    None
):
    for p in (5, 7, 13):
        row = mersenne_additive_etale_frobenius_probe(p)
        assert row.defect == (0, 0)
        assert not row.composite_witness
        assert not row.prime_certificate
        assert not row.scalable
        assert row.factor_enumeration == 0
        assert row.ring_multiplications >= p

    for p in (11, 23):
        row = mersenne_additive_etale_frobenius_probe(p)
        assert row.defect != (0, 0)
        assert row.composite_witness
        assert not row.prime_certificate
        assert not row.scalable
        assert row.factor_enumeration == 0

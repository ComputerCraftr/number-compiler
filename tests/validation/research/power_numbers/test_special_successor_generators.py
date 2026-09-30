from devtools.verification.oracles.special_binary_jump import _mersenne_carrier_proof
from number_compiler.arithmetic.functions.finite_unary import (
    minimize_unary_moore,
    partition_equivalent,
    unary_image_filtration,
)
from number_compiler.sequences.prime.set import jacobi_symbol
from tests.support.immutable_special_proofs import (
    complete_special_successor_metrics,
    immutable_proof_record,
    immutable_proof_rows,
)


def test_jacobi_symbol_is_exact_and_replaces_prime_field_euler_split() -> None:
    # Standard values plus zero/gcd behavior.
    assert jacobi_symbol(2, 7) == 1
    assert jacobi_symbol(3, 7) == -1
    assert jacobi_symbol(0, 7) == 0
    assert jacobi_symbol(5, 21) == 1  # Jacobi +1 is not a composite-ring square proof.
    # The bounded Mersenne classifier still returns the same exact state after
    # replacing Euler's-criterion exponentiation with the Euclidean symbol.


def test_unary_image_filtration_is_a_canonical_set_morphism() -> None:
    transition = (1, 2, 2, 1)
    filtration = unary_image_filtration(transition)
    assert filtration.ranks == (4, 2, 1, 1)
    assert filtration.stable_states == 1
    assert filtration.depth_ids == (0, 1, -1, 0)


def test_carry_interval_artifact_reuses_the_complete_recipe_row() -> None:
    from devtools.experiments.power_numbers.special_successor_carry import (
        _reachable_carry_interval,
    )

    first_interval = _reachable_carry_interval("fermat", 3, 10)
    assert _reachable_carry_interval("fermat", 3, 10) is first_interval


def test_prime_mersenne_image_depth_matches_moore_but_composite_guard_does_not() -> (
    None
):
    for p in (7, 13):
        proof = _mersenne_carrier_proof(p)
        moore = minimize_unary_moore(proof.transition, proof.outputs)
        filtration = unary_image_filtration(proof.transition)
        assert partition_equivalent(moore.class_ids, filtration.depth_ids)
    proof = _mersenne_carrier_proof(11)
    moore = minimize_unary_moore(proof.transition, proof.outputs)
    filtration = unary_image_filtration(proof.transition)
    assert not partition_equivalent(moore.class_ids, filtration.depth_ids)


def test_successor_generator_probe_locks_constraints_and_negative_middle_result() -> (
    None
):
    metrics = complete_special_successor_metrics()
    by_key = {(r.family, r.parameter): r for r in metrics.filtrations}
    assert by_key[("fermat", 4)].image_ranks == (
        2049,
        1025,
        513,
        257,
        129,
        65,
        33,
        17,
        9,
        5,
        3,
        2,
        2,
    )
    assert by_key[("mersenne", 13)].image_ranks == (
        4096,
        3072,
        2560,
        2304,
        2176,
        2112,
        2080,
        2064,
        2056,
        2052,
        2050,
        2049,
        2048,
        2048,
    )
    assert not by_key[("mersenne", 11)].moore_equals_image_depth

    constraints = {
        (r.family, r.parameter, r.target_set): r for r in metrics.residue_constraints
    }
    assert constraints[("mersenne", 13, "first_image")].feature_classes == 4
    assert constraints[("mersenne", 13, "first_image")].conflicts == 0
    assert constraints[("mersenne", 11, "first_image")].conflicts > 0
    assert constraints[("fermat", 4, "first_image")].feature_classes == 3
    assert constraints[("fermat", 4, "first_image")].conflicts == 0

    static = {(r.family, r.parameter): r for r in metrics.static_injections}
    assert static[("fermat", 4)].selected_key_classes == 2044
    assert static[("mersenne", 13)].selected_key_classes == 4068
    # Those are deliberately rejected as scalable injectors: they nearly
    # reconstruct their complete 2049/4096 carriers.

    automata = {(r.family, r.parameter): r for r in metrics.structured_automata}
    assert automata[("fermat", 4)].best_nodes == 4181
    assert automata[("mersenne", 13)].best_nodes == 917

    boolean = {(r.family, r.parameter): r for r in metrics.boolean_sets}
    assert boolean[("fermat", 4)].anf_degree == 15
    assert boolean[("fermat", 4)].anf_terms == 32721
    assert boolean[("mersenne", 13)].anf_degree == 11
    assert boolean[("mersenne", 13)].anf_terms == 2087


def test_prime_group_depth_theorem_matches_complete_bounded_machines() -> None:
    from devtools.experiments.power_numbers.special_successor_purity import (
        prime_group_depth_audits,
    )

    rows = immutable_proof_rows("prime_group_depths", prime_group_depth_audits)
    assert rows
    assert all(r.predicted_quotient_classes == r.bounded_moore_classes for r in rows)
    assert all(r.predicted_target_depth == r.bounded_target_depth for r in rows)
    assert all(r.image_rank_formula_exact for r in rows)
    assert all(r.moore_equals_image_depth for r in rows)
    assert all(r.target_distance_formula_exact for r in rows)
    assert all(r.source_orbit_covers_all_classes for r in rows)
    assert all(r.source_machine_isomorphic for r in rows)
    by_key = {(r.family, r.parameter): r for r in rows}
    assert by_key[("fermat", 4)].active_two_group_exponent == 11
    assert by_key[("fermat", 4)].stable_image_states == 2
    assert by_key[("fermat", 4)].predicted_image_ranks == (
        2049,
        1025,
        513,
        257,
        129,
        65,
        33,
        17,
        9,
        5,
        3,
        2,
        2,
    )
    assert by_key[("mersenne", 13)].active_two_group_exponent == 12
    assert by_key[("mersenne", 13)].stable_image_states == 2048
    assert by_key[("mersenne", 13)].predicted_image_ranks == (
        4096,
        3072,
        2560,
        2304,
        2176,
        2112,
        2080,
        2064,
        2056,
        2052,
        2050,
        2049,
        2048,
        2048,
    )
    assert by_key[("fermat", 4)].carrier_states_avoided_by_theorem == 2049
    assert by_key[("mersenne", 17)].carrier_states_avoided_by_theorem == 65536


def test_factor_backed_crt_truth_audit_identifies_actual_two_primary_obstruction() -> (
    None
):
    from devtools.experiments.power_numbers.special_successor_purity import (
        crt_purity_audits,
    )

    rows = {
        (r.family, r.parameter): r
        for r in immutable_proof_rows(
            "crt_purity",
            crt_purity_audits,
        )
    }
    assert rows[("fermat", 4)].pure_prime_domain_shape
    assert rows[("mersenne", 13)].pure_prime_domain_shape

    f5 = rows[("fermat", 5)]
    assert f5.factors == ((641, 1), (6700417, 1))
    assert not f5.pure_prime_domain_shape
    assert {c.quotient_odd_part for c in f5.components} == {5, 52347}
    assert {(c.prime, c.source_order) for c in f5.components} == {
        (641, 10),
        (6700417, 17449),
    }
    assert "multiple-or-repeated-crt-components" in f5.obstructions

    m11 = rows[("mersenne", 11)]
    assert m11.factors == ((23, 1), (89, 1))
    assert not m11.pure_prime_domain_shape
    assert {c.local_model for c in m11.components} == {
        "split-multiplicative-torus",
        "nonsplit-norm-one-torus",
    }
    assert {(c.prime, c.source_order) for c in m11.components} == {(23, 11), (89, 90)}
    assert "mixed-split-nonsplit-components" in m11.obstructions


def test_cheap_purity_probe_fails_closed_and_cost_gate_rejects_fake_green_paths() -> (
    None
):
    from devtools.experiments.power_numbers.purity_cost import (
        cheap_purity_probe_audits,
        purity_candidate_audits,
    )

    probes = {
        (r.family, r.parameter): r
        for r in immutable_proof_rows(
            "cheap_purity_probes",
            cheap_purity_probe_audits,
        )
    }
    assert probes[("fermat", 4)].outer_signature == (-1,)
    assert probes[("fermat", 5)].outer_signature == (-1,)
    assert probes[("mersenne", 13)].outer_signature == (-1, -1)
    assert probes[("mersenne", 11)].outer_signature == (-1, -1)
    assert all(r.status == "unknown" for r in probes.values())

    candidates = {
        (r.family, r.candidate): r
        for r in immutable_proof_rows(
            "purity_candidates",
            purity_candidate_audits,
        )
    }
    for family in ("fermat", "mersenne"):
        outer = candidates[(family, "outer-jacobi-boundary")]
        assert outer.gate_accepted and outer.available
        assert not outer.establishes_purity and not outer.distinguishes_fixture

        factor = candidates[(family, "factor-backed-crt-truth-audit")]
        assert factor.establishes_purity and factor.distinguishes_fixture
        assert not factor.gate_accepted
        assert "factorization" in factor.rejection_reasons
        assert "crt-reconstruction" in factor.rejection_reasons

        short = candidates[(family, "sqrt-height-special-factor-product-short-circuit")]
        assert short.gate_accepted and short.available
        assert short.distinguishes_fixture
        assert not short.establishes_purity
        assert short.cost.big_ring_squarings == 0
        assert short.cost.candidate_product_multiplications > 0

        target = candidates[(family, "higher-2^k-euclidean-reciprocity-target")]
        assert target.gate_accepted
        assert not target.available and not target.establishes_purity

    pepin = candidates[("fermat", "pepin-full-order-congruence")]
    assert not pepin.gate_accepted
    assert "sequential-image-height-work" in pepin.rejection_reasons
    ll = candidates[("mersenne", "torus-frobenius/full-lucas-lehmer-order")]
    assert not ll.gate_accepted
    assert "sequential-image-height-work" in ll.rejection_reasons


def test_factor_identity_free_two_primary_interface_and_shift_power_are_exact() -> None:
    from devtools.experiments.power_numbers.special_successor_residual import (
        two_primary_residual_interface_audits,
        two_primary_shift_block_audits,
    )

    interfaces = {
        (r.family, r.parameter): r
        for r in immutable_proof_rows(
            "residual_interfaces",
            two_primary_residual_interface_audits,
        )
    }
    assert interfaces[("fermat", 4)].purity_status == "pure"
    assert interfaces[("mersenne", 13)].purity_status == "pure"
    assert interfaces[("fermat", 5)].purity_status == "impure"
    assert interfaces[("mersenne", 11)].purity_status == "impure"
    assert all(not r.factor_identities_retained for r in interfaces.values())
    assert all(r.classifies_purity_exactly for r in interfaces.values())
    # The truth interface is tiny and does not retain the actual 641/6700417
    # or 23/89 identities.
    assert interfaces[("fermat", 5)].retained_description_bits < 64
    assert interfaces[("mersenne", 11)].retained_description_bits < 64

    shifts = immutable_proof_rows("shift_blocks", two_primary_shift_block_audits)
    assert shifts and all(r.exact_for_all_components for r in shifts)
    # Existing tropical valuation powering is logarithmic in block height.
    for row in shifts:
        assert row.powered_compositions <= 2 * row.block_size.bit_length()


def test_exact_behavioral_blocks_reject_endpoint_only_fake_compression() -> None:
    from devtools.experiments.power_numbers.special_successor_residual import (
        behavioral_purity_block_audits,
    )

    rows = {
        (r.family, r.parameter, r.block_size): r
        for r in immutable_proof_rows(
            "behavioral_blocks",
            behavioral_purity_block_audits,
        )
    }
    f4 = rows[("fermat", 4, 8)]
    assert f4.sampled_block_classes == 3
    assert f4.exact_block_classes == f4.one_step_classes == 12
    assert f4.sampled_compression_is_unsound
    m13 = rows[("mersenne", 13, 8)]
    assert m13.sampled_block_classes == 3
    assert m13.exact_block_classes == m13.one_step_classes == 13
    assert m13.sampled_compression_is_unsound
    m11 = rows[("mersenne", 11, 4)]
    assert m11.sampled_block_classes == 2
    assert m11.exact_block_classes == m11.one_step_classes == 3


def test_native_jacobi_primary_jet_and_cyclotomic_blocks_do_not_fake_close_purity() -> (
    None
):
    from devtools.experiments.power_numbers.special_successor_residual import (
        algebraic_block_observer_audits,
    )

    rows = {
        (r.family, r.parameter, r.block_size): r
        for r in immutable_proof_rows(
            "algebraic_block_observers",
            algebraic_block_observer_audits,
        )
    }
    # F4/M13 remain non-closed even after reusing the canonical native
    # primary/cyclotomic word channels.  Their selected keys also approach
    # source reconstruction, so they are not scalable quotient injectors.
    f4 = rows[("fermat", 4, 8)]
    assert not f4.closed
    assert f4.selected_classes == 2043
    assert f4.unresolved_counterexamples > 0
    m13 = rows[("mersenne", 13, 8)]
    assert not m13.closed
    assert m13.selected_classes == 3933
    assert m13.unresolved_counterexamples > 0
    # M11 can be made closed only by reconstructing every bounded carrier
    # state, which is explicitly rejected as a quotient.
    m11 = rows[("mersenne", 11, 8)]
    assert m11.closed
    assert not m11.noninjective
    assert m11.selected_classes == m11.source_states == 1024


def test_special_square_carry_transfer_automata_compress_but_are_not_closed() -> None:
    from devtools.experiments.power_numbers.special_successor_carry import (
        carry_transfer_automaton_audits,
    )

    rows = {
        (r.family, r.parameter, r.radix): r
        for r in immutable_proof_rows(
            "carry_transfer_automata",
            carry_transfer_automaton_audits,
        )
    }
    f4 = rows[("fermat", 4, 10)]
    assert f4.block_size == 8
    assert f4.reachable_carry_values == 2
    assert f4.action_alphabet == 3
    assert f4.action_word_classes == 4
    assert not f4.closed and f4.successor_conflicts == 58
    m13 = rows[("mersenne", 13, 10)]
    assert m13.block_size == 8
    assert m13.reachable_carry_values == 3
    assert m13.action_alphabet == 7
    assert m13.action_word_classes == 9
    assert not m13.closed and m13.successor_conflicts == 74
    # Alternate-radix reinterpretation is genuinely changing the transient
    # carry quotient rather than reusing the base-2 raw state.
    assert rows[("fermat", 4, 2)].action_word_classes == 196
    assert rows[("fermat", 4, 10)].action_word_classes < 10
    assert rows[("mersenne", 13, 2)].action_word_classes == 568
    assert rows[("mersenne", 13, 10)].action_word_classes < 10


def test_carry_cyclotomic_transducer_emission_is_exact_but_does_not_close_depth() -> (
    None
):
    from devtools.experiments.power_numbers.special_successor_carry import (
        carry_cyclotomic_transducer_audits,
    )

    rows = {
        (r.family, r.parameter, r.order): r
        for r in immutable_proof_rows(
            "carry_cyclotomic_transducers",
            carry_cyclotomic_transducer_audits,
        )
    }
    f4 = rows[("fermat", 4, 2)]
    assert f4.transducer_word_classes == 16
    assert not f4.closed and f4.successor_conflicts == 1631
    m13 = rows[("mersenne", 13, 8)]
    assert m13.transducer_word_classes == 108
    assert not m13.closed and m13.successor_conflicts == 2171
    # Richer cyclotomic emission refines the transient action but does not turn
    # it into the 12/13-class Moore quotient.
    assert rows[("fermat", 4, 8)].transducer_word_classes > f4.transducer_word_classes


def test_boundary_consumer_quotient_keeps_exact_output_as_injective_control() -> None:
    from devtools.experiments.power_numbers.special_successor_carry import (
        boundary_consumer_quotient_audits,
    )

    rows = boundary_consumer_quotient_audits()
    assert {(row.family, row.parameter) for row in rows} == {
        ("fermat", 3),
        ("fermat", 4),
        ("mersenne", 7),
        ("mersenne", 11),
        ("mersenne", 13),
    }
    for row in rows:
        # A single exact (carry,payload) response reconstructs the raw product.
        assert row.exact_output_action_injective
        assert row.exact_output_action_classes == row.distinct_raw_products
        # Carry and harmonic consumers are genuine contextual quotients, but a
        # bounded table is not a temporal scheduler certificate.
        assert row.carry_action_classes <= row.source_states
        assert row.harmonic_action_classes <= row.source_states
        assert not row.scheduler_promotion_safe


def test_carry_hensel_bitplanes_still_reconstruct_instead_of_quotienting() -> None:
    from devtools.experiments.power_numbers.special_successor_carry import (
        carry_hensel_cyclotomic_audits,
    )

    rows = {
        (r.family, r.parameter, r.source_channels): r
        for r in immutable_proof_rows(
            "carry_hensel_cyclotomic",
            carry_hensel_cyclotomic_audits,
        )
    }
    f4 = rows[("fermat", 4, "raw-square+carry")]
    assert not f4.closed and f4.selected_classes == 2044
    assert f4.unresolved_counterexamples == 5
    m13 = rows[("mersenne", 13, "raw-square+carry")]
    assert not m13.closed and m13.selected_classes == 4088
    assert m13.unresolved_counterexamples == 8
    # The carry-only tower is also not the missing state.
    assert not rows[("mersenne", 13, "carry-only")].closed
    assert rows[("mersenne", 13, "carry-only")].selected_classes == 3872


def test_coarse_carry_marker_itinerary_closes_only_at_original_prime_depth() -> None:
    from devtools.experiments.power_numbers.special_successor_carry import (
        carry_temporal_automaton_audits,
    )

    rows = {
        (r.family, r.parameter, r.marker): r
        for r in immutable_proof_rows(
            "carry_temporal_automata",
            carry_temporal_automaton_audits,
        )
    }
    for family, parameter in (
        ("fermat", 3),
        ("fermat", 4),
        ("mersenne", 5),
        ("mersenne", 7),
        ("mersenne", 13),
        ("mersenne", 17),
    ):
        row = next(
            r
            for r in rows.values()
            if r.family == family
            and r.parameter == parameter
            and "carry-action" in r.marker
        )
        assert row.prime_target_depth is not None
        assert row.closure_horizon == row.prime_target_depth + 1
        assert not row.subdepth_closure
    # Composite M11 can close a cheap marker itinerary early; that is a useful
    # adversarial reminder that finite carry closure is not prime-domain purity.
    m11 = rows[("mersenne", 11, "radix10-boundary")]
    assert m11.closure_horizon == 4 and m11.horizon_classes == 8
    assert m11.moore_classes == 3


def test_sqrt_height_special_factor_scan_is_sound_sublinear_short_circuit_only() -> (
    None
):
    from devtools.experiments.power_numbers.special_successor_factor import (
        special_factor_short_circuit_audits,
    )

    rows = {
        (r.family, r.parameter): r
        for r in immutable_proof_rows(
            "factor_short_circuits",
            special_factor_short_circuit_audits,
        )
    }
    f5 = rows[("fermat", 5)]
    assert f5.candidate_budget == 6
    assert f5.witness_k == 5 and f5.witness_factor == 641
    assert f5.status == "composite-witness"
    assert f5.small_ring_compositions == 25
    assert f5.batched_powered_compositions == 5
    assert f5.product_multiplications == 5
    assert f5.batch_witness_matches_serial
    m11 = rows[("mersenne", 11)]
    assert m11.witness_k == 1 and m11.witness_factor == 23
    assert m11.status == "composite-witness"
    assert m11.batched_powered_compositions == 6
    assert m11.product_multiplications == 3
    assert m11.batch_witness_matches_serial
    # Exhaustion is fail-closed: prime fixtures remain unknown rather than
    # being promoted to prime from a bounded factor window.
    assert rows[("fermat", 4)].status == "unknown"
    assert rows[("mersenne", 13)].status == "unknown"
    assert all(not r.complete_primality_decision for r in rows.values())


def test_temporal_history_partition_refinement_matches_materialized_histories() -> None:
    from devtools.experiments.power_numbers.special_successor_carry import (
        _partition_ids,
        _temporal_marker_histories,
        _temporal_marker_history_ids,
    )

    transition = (1, 2, 3, 3)
    marker = ("a", "b", "a", "c")
    for horizon in range(6):
        if horizon == 0:
            expected: tuple[int, ...] = (0, 0, 0, 0)
        else:
            expected = _partition_ids(
                _temporal_marker_histories(marker, transition, horizon)
            )
        actual = _temporal_marker_history_ids(marker, transition, horizon)
        # Class numbers may be canonicalized in a different encounter order;
        # compare the induced equivalence relation rather than integer labels.
        for i in range(len(transition)):
            for j in range(len(transition)):
                assert (actual[i] == actual[j]) == (expected[i] == expected[j])

    from devtools.experiments.power_numbers.special_successor_carry import (
        _temporal_marker_closure,
        _temporal_marker_partition,
    )

    outputs = (False, False, True, False)
    expected_horizon = None
    expected_classes = len(set(marker))
    for horizon in range(1, 6):
        expected_classes, conflicts = _temporal_marker_partition(
            marker,
            transition,
            outputs,
            horizon,
        )
        if conflicts == 0:
            expected_horizon = horizon
            break
    assert _temporal_marker_closure(marker, transition, outputs, 5) == (
        expected_horizon,
        expected_classes,
    )


def test_carry_history_is_exactly_a_phase_refinement_of_independent_image_depth() -> (
    None
):
    from devtools.experiments.power_numbers.special_successor_carry import (
        carry_phase_refinement_audits,
    )

    rows = {
        (r.family, r.parameter, r.radix): r
        for r in immutable_proof_rows(
            "carry_phase_refinements",
            carry_phase_refinement_audits,
        )
    }
    assert rows
    assert all(r.history_refines_depth for r in rows.values())
    assert all(r.minimized_history_equals_depth for r in rows.values())
    assert all(r.minimized_history_classes == r.depth_classes for r in rows.values())
    assert all(r.excess_phase_classes >= 0 for r in rows.values())

    # High-radix carry histories retain lots of irrelevant phase, but exact
    # Moore minimization deletes it back to the 12/13 successor-depth classes.
    f4 = rows[("fermat", 4, 10)]
    assert f4.history_horizon == 11
    assert f4.history_classes == 41 and f4.depth_classes == 12
    assert f4.excess_phase_classes == 29
    m13 = rows[("mersenne", 13, 10)]
    assert m13.history_horizon == 12
    assert m13.history_classes == 149 and m13.depth_classes == 13
    assert m13.excess_phase_classes == 136

    # The phase is not a bounded correction waiting to be retained.  On M17
    # radix 10 it explodes to thousands of histories while exact minimization
    # still deletes all of it back to the 17 image-depth classes.
    m17 = rows[("mersenne", 17, 10)]
    assert m17.history_horizon == 16
    assert m17.history_classes == 15334 and m17.depth_classes == 17
    assert m17.max_finite_phase_fiber == 1745
    assert m17.stable_phase_classes == 11467


def test_legacy_carry_event_and_source_only_theorem_surfaces_are_removed() -> None:
    import devtools.verification.oracles.special_binary_jump as special_jump
    import number_compiler.arithmetic.polynomials.two_primary_filtration as filtration
    from devtools.experiments.power_numbers.special_successor_carry import (
        carry_phase_refinement_audits,
    )

    assert hasattr(filtration, "pure_two_primary_image_filtration")
    assert not hasattr(special_jump, "pure_two_primary_group_depth")
    assert not hasattr(special_jump, "_prime_conditional_source_depth")
    row = immutable_proof_rows(
        "carry_phase_refinements",
        carry_phase_refinement_audits,
    )[0]
    for legacy_field in (
        "target_marker_classes",
        "event_horizon",
        "first_target_event_exact",
        "last_target_event_exact",
        "stable_states_hitting_target_event",
        "target_marker_predicate_equals_output",
        "source_target_event_time",
    ):
        assert not hasattr(row, legacy_field)


def test_composite_m11_depth_and_target_semantics_are_reconstructed_without_carry_events() -> (
    None
):
    from devtools.experiments.power_numbers.special_successor_generators import (
        composite_depth_semantics_audit,
    )

    row = immutable_proof_record(
        "composite_depth_semantics",
        composite_depth_semantics_audit,
    )
    assert row.family == "mersenne" and row.parameter == 11
    assert row.image_ranks == (1024, 460, 282, 196, 196)
    assert row.finite_depth_strata == (564, 178, 86)
    assert row.stable_image_states == 196
    assert row.image_depth_classes == 4
    assert row.moore_classes == 3
    assert not row.moore_equals_image_depth
    assert row.target_image_depths == (1,)
    assert row.output_states == 1
    assert row.finite_target_hitting_counts == ((0, 1), (1, 2))
    assert row.never_target_states == 1021
    assert row.source_image_depth == 0
    assert row.source_target_hitting_time is None

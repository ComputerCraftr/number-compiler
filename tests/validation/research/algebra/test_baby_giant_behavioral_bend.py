from devtools.experiments.algebra.baby_giant_behavioral_bend import (
    BabyGiantBendPacketMemo,
    behavioral_bend_frontier,
    behavioral_bend_quotient_audit,
)
from devtools.paths import repository_root


def test_dyadic_backward_trace_partition_has_exact_min_h_plus_one_q_growth() -> None:
    expected = {
        ("fermat", 5): 641,
        ("mersenne", 11): 23,
        ("mersenne", 29): 233,
    }
    for key, q in expected.items():
        audit = behavioral_bend_quotient_audit(*key)
        assert audit.hidden_factor == q
        assert audit.candidate_window_trace_formula_exact
        assert audit.no_trace_closure_before_candidate_window
        assert all(
            row.pullback_exact
            and row.formula_exact
            and row.closed_distance_formula_exact
            for row in audit.dyadic_rows
        )
        assert all(row.classes == min(row.horizon + 1, q) for row in audit.dyadic_rows)
        # Before saturation every doubling creates new behavioral classes.
        assert all(
            not row.no_bend_doubling for row in audit.dyadic_rows if row.horizon < q
        )
        assert audit.one_parent_split_per_unsaturated_doubling
        assert audit.symbolic_partition_grammar_constant
        assert audit.hidden_period_needed_for_distance_coordinate


def test_terminal_block_hit_observer_is_not_a_small_successor_closed_quotient() -> None:
    for key in (("fermat", 5), ("mersenne", 11)):
        audit = behavioral_bend_quotient_audit(*key)
        assert audit.candidate_window < audit.hidden_factor
        assert audit.candidate_window_block_hit_classes == audit.hidden_factor
        assert audit.candidate_window_block_hit_expected == audit.hidden_factor
        assert audit.source_hit_observer_classes == 2
        assert audit.source_hit_observer_successor_conflicts > 0
        assert not audit.source_hit_observer_successor_closed
        assert not audit.block_hit_powered_polylogarithmic


def test_long_m29_window_collapses_only_after_it_already_spans_a_hidden_period() -> (
    None
):
    audit = behavioral_bend_quotient_audit("mersenne", 29)
    assert audit.candidate_window >= audit.hidden_factor
    assert audit.candidate_window_block_hit_classes == 1
    assert audit.candidate_window_block_hit_expected == 1
    # This is not a constructive win: the quotient only knows the period after
    # factor-backed truth supplied q=233.
    assert audit.baby_giant_phase.hidden_factor_required
    assert not audit.baby_giant_phase.is_behavioral_quotient


def test_baby_giant_phase_encoding_is_sqrt_structured_but_does_not_merge_behavioral_states() -> (
    None
):
    for key in (("fermat", 5), ("mersenne", 11), ("mersenne", 29)):
        phase = behavioral_bend_quotient_audit(*key).baby_giant_phase
        assert phase.exact_injective
        assert phase.encoded_classes == phase.period
        assert phase.structural_entries < phase.period
        assert phase.hidden_factor_required
        assert not phase.is_behavioral_quotient


def test_fixed_window_bsgs_packet_is_reused_instead_of_recomputed() -> None:
    memo = BabyGiantBendPacketMemo()
    first = memo.evaluate("fermat", 5, start=1, span=511)
    second = memo.evaluate("fermat", 5, start=1, span=511)
    assert first is second
    assert memo.size == 1 and memo.misses == 1 and memo.hits == 1
    assert first.support_gcd == 641
    assert first.status == "SPLIT"
    assert first.first_bend_slot == 5
    assert first.first_bend_gcd == 641
    assert first.first_bend_distance == 4
    assert not first.direct_control_evaluated
    assert first.character_constant == 3
    assert first.first_bend_dirichlet_character == -1
    assert first.block_locator_gcds <= first.giant_blocks
    assert first.leaf_locator_gcds <= first.baby_width
    assert first.structural_state_entries < first.span


def test_fixed_window_packets_match_known_prime_and_composite_bend_supports() -> None:
    memo = BabyGiantBendPacketMemo()
    rows = (
        ("fermat", 4, 1, 3, 1, "CLEAR"),
        ("fermat", 5, 1, 511, 641, "SPLIT"),
        ("mersenne", 13, 1, 3, 1, "CLEAR"),
        ("mersenne", 29, 1, 399, (1 << 29) - 1, "FULL"),
    )
    for family, parameter, start, span, support, status in rows:
        packet = memo.evaluate(family, parameter, start=start, span=span)
        assert packet.support_gcd == support
        assert packet.status == status
        if status == "CLEAR":
            assert packet.first_bend_slot is None and packet.first_bend_gcd == 1
        else:
            assert packet.first_bend_slot is not None and packet.first_bend_gcd > 1
            assert packet.block_locator_gcds <= packet.giant_blocks
            assert packet.leaf_locator_gcds <= packet.baby_width


def test_behavioral_bend_frontier_refuses_fake_polylog_promotion() -> None:
    frontier = behavioral_bend_frontier()
    assert frontier.dyadic_pullback_implemented
    assert frontier.exact_trace_formula_verified
    assert frontier.closed_distance_partition_formula
    assert frontier.one_parent_split_per_doubling
    assert frontier.symbolic_partition_grammar_constant
    assert not frontier.factor_free_distance_coordinate_available
    assert not frontier.raw_trace_polylogarithmic
    assert not frontier.terminal_hit_successor_closed_small
    assert not frontier.baby_giant_phase_is_behavioral_quotient
    assert frontier.fixed_window_bsgs_reusable
    assert frontier.bsgs_first_bend_injector_available
    assert frontier.bsgs_first_bend_locator_logarithmic_gcd_bound
    assert frontier.support_only_observer_skips_factor_descent
    assert not frontier.unseen_window_polylog_constructor_available
    assert not frontier.production_promotable
    assert frontier.status == "REFUTED_RAW_BEND_QUOTIENT"


def test_behavioral_bend_research_is_not_reachable_from_production_sources() -> None:
    root = repository_root() / "src" / "number_compiler"
    source = "\n".join(path.read_text() for path in root.glob("*.py"))
    assert "baby_giant_behavioral_bend" not in source


def test_support_only_packet_stops_before_factor_or_bend_location_work() -> None:
    from devtools.experiments.algebra.baby_giant_behavioral_bend import (
        BabyGiantSupportPacketMemo,
    )

    memo = BabyGiantSupportPacketMemo()
    packet = memo.evaluate("mersenne", 29, start=1, span=399)
    assert packet.status == "NONUNIT"
    assert packet.support_gcd == packet.modulus
    assert packet.final_support_gcds == 1
    assert packet.split_descent_gcds == 0
    assert not packet.direct_control_evaluated
    assert memo.evaluate("mersenne", 29, start=1, span=399) is packet
    assert memo.hits == memo.misses == 1


def test_prefix_first_bend_carries_safe_local_dirichlet_phase_after_support_extraction() -> (
    None
):
    memo = BabyGiantBendPacketMemo()
    f5 = memo.evaluate("fermat", 5, start=1, span=511)
    m29 = memo.evaluate("mersenne", 29, start=1, span=399)
    assert (f5.character_constant, f5.first_bend_dirichlet_character) == (3, -1)
    assert (m29.character_constant, m29.first_bend_dirichlet_character) == (12, -1)

    # An arbitrary translated window is not allowed to reinterpret the Jacobi
    # symbol of a composite supported slot as a prime-local factor character.
    shifted = memo.evaluate("fermat", 5, start=2, span=510)
    assert shifted.first_bend_slot == 5
    assert shifted.first_bend_dirichlet_character is None
    assert shifted.character_constant is None

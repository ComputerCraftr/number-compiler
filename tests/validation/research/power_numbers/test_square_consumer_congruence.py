from devtools.experiments.power_numbers.square_consumer_congruence import (
    square_consumer_congruence_audits,
    terminal_deck_congruence_audits,
)


def test_square_only_consumers_are_exact_noninjective_unary_congruences() -> None:
    rows = square_consumer_congruence_audits()
    assert {(row.family, row.parameter) for row in rows} == {
        ("fermat", 2),
        ("fermat", 3),
        ("mersenne", 5),
        ("mersenne", 7),
    }
    for row in rows:
        assert row.one_step_image_states <= row.sign_orbit_classes < row.source_states
        assert row.triangular_product_cells == row.width * (row.width + 1) // 2
        assert row.triangular_product_cells < row.ordered_product_cells
        assert row.stable_classes >= row.initial_consumer_classes
        assert row.stable_successor_conflicts == 0
        assert row.quotient_transition_verified
        assert row.source_sign_action_conflicts == 0
        assert row.pulled_terminal_sign_conflicts == 0
        assert row.noninjective
        assert not row.general_multiplication_required
        assert not row.general_addition_required
        assert not row.scheduler_promotion_safe


def test_pepin_current_terminal_sign_is_delayed_to_the_pulled_observer() -> None:
    fermat = [
        row for row in square_consumer_congruence_audits() if row.family == "fermat"
    ]
    assert all(row.current_terminal_sign_conflicts > 0 for row in fermat)
    assert all(row.pulled_terminal_sign_conflicts == 0 for row in fermat)


def test_terminal_deck_partition_is_closed_under_powered_squares() -> None:
    rows = terminal_deck_congruence_audits()
    assert {(row.family, row.parameter) for row in rows} == {
        ("fermat", 2),
        ("fermat", 3),
        ("fermat", 4),
        ("mersenne", 5),
        ("mersenne", 7),
        ("mersenne", 11),
        ("mersenne", 13),
    }
    for row in rows:
        assert row.deck_classes == row.expected_half_deck_classes
        assert row.one_step_image_states <= row.deck_classes
        assert row.terminal_observer_classes == 2
        assert row.terminal_observer_conflicts == 0
        assert row.square_power_horizons == (1, 2, 4, 8, 16, 32)
        assert row.square_power_conflicts == (0, 0, 0, 0, 0, 0)
        assert not row.scheduler_promotion_safe


def test_fermat_terminal_split_replaces_dead_sign_pair_with_zero_one_merge() -> None:
    rows = terminal_deck_congruence_audits()
    for row in rows:
        if row.family == "fermat":
            assert row.terminal_deck_split
            assert row.zero_one_merged
            assert row.fermat_zero_one_carry_harmonic_equal
            assert row.zero_one_incoming_interval == (0, 0)
            assert not row.cyclotomic_lift_marker_sign_invariant_safe
        else:
            assert not row.terminal_deck_split
            assert not row.zero_one_merged
            assert row.fermat_zero_one_carry_harmonic_equal is None
            assert row.zero_one_incoming_interval is None
            assert row.cyclotomic_lift_marker_sign_invariant_safe
        assert row.cyclotomic_lift_marker_owner == "cyclotomic_binary_lift_marker"
        assert not row.full_five_dimensional_germ_descends_claimed
        assert not row.minimal_moore_quotient_claimed

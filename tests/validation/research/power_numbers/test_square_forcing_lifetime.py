from devtools.experiments.power_numbers.square_forcing_lifetime import (
    square_forcing_lifetime_audits,
)


def test_old_square_forcing_dies_but_birth_clock_and_fold_response_survive() -> None:
    rows = square_forcing_lifetime_audits()
    assert {(row.family, row.parameter) for row in rows} == {
        ("fermat", 2),
        ("fermat", 3),
        ("mersenne", 5),
        ("mersenne", 7),
    }
    for row in rows:
        assert row.death_depth == 5
        assert row.raw_history_occurrences == row.source_states * (row.horizon + 1)
        assert row.post_death_occurrences == row.source_states * (
            row.horizon - row.death_depth + 1
        )
        assert row.post_death_tangent_actions == 1
        assert row.canonical_key_hits_after_death == row.post_death_occurrences - 1
        assert row.surviving_birth_actions_after_source_death > 1
        assert not row.production_interner_present
        assert (row.birth_clock_order, row.birth_clock_period) == (5, 4)
        assert row.post_death_clock_phases == row.birth_clock_period
        assert row.canonical_tangent_actions < row.raw_history_occurrences
        assert row.scalar_differential_checks == 32 * row.source_states
        assert row.scalar_differential_exact
        assert row.equal_valuation_fold_responses_distinct
        assert not row.valuation_only_identity_safe
        assert not row.clock_removed_from_birth_identity
        assert not row.scheduler_promotion_safe

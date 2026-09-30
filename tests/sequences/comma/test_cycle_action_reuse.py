"""Exact cycle reuse must avoid construction without supplying branch authority."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.fields.consumer_pullback import PrefixSafety
from number_compiler.resources.process_cache import ProcessCache, get_process_cache
from number_compiler.resources.temporal_diagnostics import (
    collect_temporal_diagnostics_snapshot,
)
from number_compiler.sequences.comma import cycle_actions
from number_compiler.sequences.comma.action_arena import CommaActionArena
from number_compiler.sequences.comma.power import CommaTerm
from tests.support.comma_oracles import literal_children


@pytest.mark.parametrize("leading", range(1, 10))
@pytest.mark.parametrize("digit", range(10))
def test_closed_parent_has_literal_duration_output_and_strict_guard(
    leading: int,
    digit: int,
) -> None:
    copies = 7
    steps, displacement, guard = cycle_actions.normalized_cycle(leading, digit, copies)
    source = leading * 100_000 + 100 + digit
    value = source
    worst = 0
    for _ in range(steps):
        worst = max(worst, value - source + 10 * (value % 10) + leading + (leading < 9))
        children = literal_children(value)
        assert len(children) == 1
        value = children[0]
    assert (value - source, worst) == (displacement, guard)


def test_parent_lookup_precedes_any_cold_composition_and_children(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = CommaTerm(20_000, shared_cache=False)
    action = term.arena.cycles(1, 4, 73)
    before = dict(term.ledger.counters)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("warm normalized parent constructed child arithmetic")

    monkeypatch.setattr(cycle_actions, "normalized_cycle", forbidden)
    monkeypatch.setattr(CommaActionArena, "compose", forbidden)
    monkeypatch.setattr(CommaActionArena, "one_cycle", forbidden)
    assert term.arena.cycles(1, 4, 73) == action
    assert term.arena.node(action).before is None
    assert term.ledger.counters["comma_hashlife_cold_child_discoveries"] == 0
    assert (
        term.ledger.counters["comma_hashlife_coefficient_compositions"]
        == before["comma_hashlife_coefficient_compositions"]
    )
    assert term.ledger.counters["comma_hashlife_semantic_local_hits"] == 1
    # Retrieval alone never counts as an application.
    assert term.ledger.counters["comma_hashlife_semantic_applied_parent_hits"] == 0
    assert (
        collect_temporal_diagnostics_snapshot(term.ledger)
        .macrocells[0]
        .capacity_bypasses
        == 0
    )


def test_public_arithmetic_warm_parent_avoids_cold_constructor(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    cache = ProcessCache()
    monkeypatch.setattr(cycle_actions, "get_process_cache", lambda: cache)
    first = CommaTerm(20_000)
    assert first.materialize() == 1_039_404

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("shared warm parent reconstructed normalized coefficients")

    monkeypatch.setattr(cycle_actions, "normalized_cycle", forbidden)
    monkeypatch.setattr(PrefixSafety, "repeat", forbidden)
    warm = CommaTerm(20_000)
    assert warm.materialize() == first.materialize()
    row = collect_temporal_diagnostics_snapshot(warm.ledger).macrocells[0]
    assert row.family == "comma"
    assert row.index_unit == "oeis_transition"
    assert row.cache_scope == "guarded_interior_cycle_action"
    assert row.semantic.process_hits is not None and row.semantic.process_hits > 0
    assert (
        row.semantic.applied_parent_hits is not None
        and row.semantic.applied_parent_hits > 0
    )
    assert row.coefficient_compositions == row.cold_child_discoveries == 0
    assert row.occurrence.requests is None
    assert row.max_level is None  # No invented tree depth or higher-level proof.
    assert cache.stats().active_leases == 0
    cache.reset()
    with pytest.raises(pytest.fail.Exception, match="reconstructed"):
        CommaTerm(20_000).materialize()


def test_cycle_cache_cannot_import_unissued_records(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    cache = ProcessCache()
    monkeypatch.setattr(cycle_actions, "get_process_cache", lambda: cache)
    with cache.acquire(
        "comma-cycle-action", cycle_actions.CYCLE_CACHE_VERSION, (10, "strict-interior")
    ) as lease:
        lease.put((1, 0, 73), (730, 33580, 33581))
    term = CommaTerm(1)
    with pytest.raises(ValueError, match="publisher capability"):
        term.arena.cycles(1, 4, 73)
    assert term.ledger.counters["comma_hashlife_semantic_admission_rejections"] == 1
    assert cache.stats().active_leases == 0
    collect_temporal_diagnostics_snapshot(term.ledger)


def test_optional_cycle_retention_refusal_keeps_exact_output(
    monkeypatch: pytest.MonkeyPatch,
    publication_blocked_cache: ProcessCache,
) -> None:
    monkeypatch.setattr(
        cycle_actions, "get_process_cache", lambda: publication_blocked_cache
    )
    term = CommaTerm(1000)
    assert term.materialize() == 48_042
    assert term.ledger.counters["comma_hashlife_semantic_bypasses"] > 0
    assert publication_blocked_cache.stats().active_leases == 0
    row = collect_temporal_diagnostics_snapshot(term.ledger).macrocells[0]
    assert (
        row.capacity_bypasses
        == term.ledger.counters["comma_hashlife_semantic_bypasses"]
    )


@pytest.mark.parametrize("key", ((True, 0, 1), (1, False, 1), (1, 0, True), (1, 0, 0)))
def test_cycle_key_does_not_alias_integer_and_boolean_authority(
    key: tuple[int, int, int],
) -> None:
    get_process_cache().reset()
    with pytest.raises(ValueError, match="cycle action key"):
        CommaTerm(1).arena.cycles(*key)


@pytest.mark.parametrize("leading", range(1, 10))
@pytest.mark.parametrize("digit", (0, 1))
def test_complete_cycle_rotation_shares_summary_but_retains_receiving_phase(
    leading: int, digit: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    cache = ProcessCache()
    monkeypatch.setattr(cycle_actions, "get_process_cache", lambda: cache)
    cold = CommaTerm(1)
    before = cold.arena.node(cold.arena.cycles(leading, digit, 11))

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("a rotated complete cycle rebuilt its arithmetic summary")

    monkeypatch.setattr(cycle_actions, "normalized_cycle", forbidden)
    receiving_digit = (digit + leading) % 10
    warm = CommaTerm(1)
    after = warm.arena.node(warm.arena.cycles(leading, receiving_digit, 11))
    assert receiving_digit != digit
    assert after.entering_digit == receiving_digit
    assert before.entering_digit == digit
    assert (after.steps, after.displacement, after.maximum_guard) == (
        before.steps,
        before.displacement,
        before.maximum_guard,
    )
    counters = warm.ledger.counters
    assert counters["comma_hashlife_semantic_process_hits"] == 1
    assert counters["comma_hashlife_coefficient_compositions"] == 0
    assert counters["comma_hashlife_semantic_applied_hits"] == 0
    assert cache.stats().active_leases == 0


def test_distinct_cycle_cosets_keep_distinct_displacements(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    cache = ProcessCache()
    monkeypatch.setattr(cycle_actions, "get_process_cache", lambda: cache)
    arena = CommaTerm(1).arena
    even = arena.node(arena.cycles(2, 0, 11))
    odd = arena.node(arena.cycles(2, 1, 11))
    assert even.steps == odd.steps
    assert even.displacement != odd.displacement
    assert arena.ledger.counters["comma_hashlife_semantic_misses"] == 2
    assert arena.ledger.counters["comma_hashlife_semantic_process_hits"] == 0

"""Cache bypass reasons stay distinct from misses, capacity and local reuse."""

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.temporal_diagnostics import (
    collect_temporal_diagnostics_snapshot,
)
from number_compiler.sequences.antihydra import mahler_cache
from number_compiler.sequences.antihydra.mahler_action import associated_action
from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm
from number_compiler.sequences.collatz.source_cylinder_cache import CollatzDyadicMacros


def test_disabled_process_reuse_does_not_hide_local_collatz_hits() -> None:
    ledger = ResourceLedger()
    with CollatzDyadicMacros(ledger, shared_cache=False) as macros:
        assert macros.lookup(1, 8) is None
        # The normalized map for residue 1 at eight symbols maps 1 to 1.
        assert macros.remember(1, 8, 4, 1)
        found = macros.lookup(1, 8)
        assert found is not None and found.apply(1) == 1
        macros.applied()
        row = collect_temporal_diagnostics_snapshot(ledger).macrocells[0]
        lane = row.occurrence
        assert (lane.requests, lane.misses, lane.local_hits, lane.applied_hits) == (
            2,
            1,
            1,
            1,
        )
        assert lane.disabled_bypasses == lane.bypasses == 1
        assert lane.capacity_bypasses == row.capacity_bypasses == 0


@pytest.mark.parametrize("shared", (False, True))
def test_mahler_outer_policy_and_disabled_bypasses_are_not_capacity(
    shared: bool, monkeypatch: pytest.MonkeyPatch
) -> None:
    def forbidden() -> None:
        raise AssertionError("bypassed observer acquired process cache")

    monkeypatch.setattr(mahler_cache, "get_process_cache", forbidden)
    term = AntihydraArithmeticTerm(8, shared_cache=shared)
    associated_action(term.result())
    row = next(
        row
        for row in collect_temporal_diagnostics_snapshot(term.ledger).macrocells
        if row.family == "mahler"
    )
    lane = row.outer_observer
    assert lane.bypasses == 1
    assert lane.disabled_bypasses == int(not shared)
    assert lane.policy_bypasses == int(shared)
    assert lane.requests == lane.misses == lane.capacity_bypasses == 0
    assert row.capacity_bypasses == 0


def test_local_occurrence_evictions_count_only_replaced_roots(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(CollatzDyadicMacros, "LIMIT", 1)
    ledger = ResourceLedger()
    with CollatzDyadicMacros(ledger) as macros:
        assert macros.remember(1, 8, 4, 1)
        assert not macros.remember(1, 8, 4, 1)
        assert macros.remember(2, 8, 4, 2)
        assert macros.lookup(1, 8) is None
        assert macros.lookup(2, 8) is not None
        lane = collect_temporal_diagnostics_snapshot(ledger).macrocells[0].occurrence
        assert lane.evictions == 1


def test_republication_at_capacity_preserves_other_local_occurrences(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(CollatzDyadicMacros, "LIMIT", 2)
    with CollatzDyadicMacros(ResourceLedger()) as macros:
        assert macros.remember(1, 8, 4, 1)
        assert macros.remember(2, 8, 4, 2)
        second = macros.lookup(2, 8)
        assert second is not None
        macros._publish(second, 0)
        assert macros.lookup(1, 8) is not None
        assert len(macros.occurrences) == 2
        assert macros.ledger.counters["collatz_hashlife_occurrence_evictions"] == 0


def test_disabled_store_is_not_a_capacity_refusal(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.resources.process_cache import ProcessCache
    from number_compiler.sequences.antihydra import mahler_source_actions
    from number_compiler.sequences.antihydra.arithmetic_images import (
        ANTIHYDRA_ARITHMETIC_LAW,
    )
    from number_compiler.sequences.collatz import source_cylinder_cache
    from number_compiler.sequences.comma import cycle_actions
    from number_compiler.sequences.comma.power import CommaTerm

    cache = ProcessCache(enabled=False)
    for module in (
        mahler_cache,
        mahler_source_actions,
        source_cylinder_cache,
        cycle_actions,
    ):
        monkeypatch.setattr(module, "get_process_cache", lambda: cache)
    with CollatzDyadicMacros(ResourceLedger(), shared_cache=True) as macros:
        assert macros.lookup(1, 8) is None
        assert macros.remember(1, 8, 4, 1)
        row = collect_temporal_diagnostics_snapshot(macros.ledger).macrocells[0]
        assert row.occurrence.disabled_bypasses == 2
        assert row.capacity_bypasses == 0
    with mahler_source_actions.MahlerOccurrenceConsumer(
        ResourceLedger(), ANTIHYDRA_ARITHMETIC_LAW, shared_cache=True
    ) as consumer:
        assert consumer.lease is None
        row = collect_temporal_diagnostics_snapshot(consumer.ledger).macrocells[0]
        assert row.source_action.disabled_bypasses == 1
        assert row.capacity_bypasses == 0
    term = AntihydraArithmeticTerm(1024, shared_cache=True)
    associated_action(term.result())
    row = next(
        row
        for row in collect_temporal_diagnostics_snapshot(term.ledger).macrocells
        if row.family == "mahler"
    )
    assert row.outer_observer.disabled_bypasses == 1
    assert row.outer_observer.requests == row.capacity_bypasses == 0
    comma = CommaTerm(20, shared_cache=True)
    comma.arena.cycles(1, 4, 73)
    row = collect_temporal_diagnostics_snapshot(comma.ledger).macrocells[0]
    assert row.semantic.bypasses == 1
    assert row.capacity_bypasses == 0
    assert cache.stats().active_leases == cache.stats().entries == 0

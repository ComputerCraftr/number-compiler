"""Ledger-owned action reuse: quadratic-regression and allocation invariants."""

from __future__ import annotations

from random import Random

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.parity_carry_tape import ParityCarryTape
from number_compiler.sequences.collatz.parity_carry_tape_actions import (
    LedgeredParityTapeActions,
)


def _assert_retired_root_row_bound(
    cache: LedgeredParityTapeActions, tape: ParityCarryTape
) -> int:
    expected_rows = 2 * tape.steps - 1
    assert cache.retirement_pending
    assert (
        expected_rows
        <= cache.retained_entries
        <= (expected_rows + 2 * (tape.height + 1))
    )
    return expected_rows


def _assert_current_root_rows(
    cache: LedgeredParityTapeActions,
    tape: ParityCarryTape,
    expected_rows: int,
) -> None:
    assert cache.is_current_root(tape)
    assert not cache.retirement_pending
    assert cache.retained_entries == expected_rows
    assert cache.live_entries == expected_rows


def test_512_incremental_actions_do_not_refold_old_slp() -> None:
    ledger = ResourceLedger()
    with LedgeredParityTapeActions(ledger) as cache:
        tape = ParityCarryTape.letters((1,))
        edge_samples: dict[int, int] = {}
        result = tape.action(cache=cache)
        for index in range(1, 512):
            tape = ParityCarryTape.sequence(
                (tape, ParityCarryTape.letters((int((index * 37) % 13 < 5),)))
            )
            result = tape.action(cache=cache)
            if index in (127, 255, 511):
                edge_samples[index + 1] = cache.edge_visits
        assert result == tape.action()
        assert tape.height <= 12
        assert cache.compositions < 12_000
        # This aggregate counts three actual passes: cold-node discovery,
        # retained parent-edge publication, and retirement of the previous
        # root's unshared AVL path. Persistent append clones O(log n) nodes,
        # so the cumulative work is O(n log n), not O(n).
        assert cache.edge_visits == (
            cache.discovery_edge_visits
            + cache.published_edge_references
            + cache.retirement_node_visits
            + cache.retirement_edge_visits
        )
        assert edge_samples[256] <= 3 * edge_samples[128]
        assert edge_samples[512] <= 3 * edge_samples[256]
        exact_reachable_rows = _assert_retired_root_row_bound(cache, tape)
        assert ledger.entries == cache.retained_entries + cache.live_entries
        assert ledger.nodes > ledger.entries
        assert ledger.inventory_owner(cache.owner).accounting_delta == 0
        assert result is tape.action(cache=cache)
        _assert_current_root_rows(cache, tape, exact_reachable_rows)
        assert cache.cache_hits > 0
        assert ledger.nodes < ledger.peak_nodes
    assert (ledger.nodes, ledger.entries) == (0, 0)


def test_compressed_shared_repeats_match_unowned_exact_action() -> None:
    rng = Random(1978)
    shared = ParityCarryTape.letters((1, 0, 1, 0, 0))
    leaves = [
        ParityCarryTape.repeated(shared, rng.randrange(1, 33))
        if rng.randrange(3) == 0
        else ParityCarryTape.letters(tuple(rng.randrange(2) for _ in range(5)))
        for _ in range(32)
    ]
    tree = ParityCarryTape.sequence(tuple(leaves))
    ledger = ResourceLedger()
    with LedgeredParityTapeActions(ledger) as cache:
        assert (
            tree.action(cache=cache).coefficient_snapshot()
            == tree.action().coefficient_snapshot()
        )
        charged = ledger.snapshot()
        assert (
            tree.action(cache=cache).coefficient_snapshot()
            == tree.action().coefficient_snapshot()
        )
        assert ledger.nodes == charged.nodes
        assert ledger.entries == charged.entries
        assert all(row.accounting_delta in (None, 0) for row in ledger.inventory())
    assert ledger.nodes == ledger.entries == 0


def test_tiny_budget_rejects_before_an_unbounded_power_and_rolls_back() -> None:
    tree = ParityCarryTape.repeated(ParityCarryTape.letters((1, 0)), 10_000)
    ledger = ResourceLedger(max_nodes=600)
    with LedgeredParityTapeActions(ledger) as cache:
        with pytest.raises(BlockContextBudgetExceeded):
            tree.action(cache=cache)
        assert cache.retained_entries == ledger.nodes == ledger.entries == 0
        assert ledger.peak_nodes <= 600
    assert ledger.nodes == ledger.entries == 0


def test_failed_incremental_request_preserves_prior_rows_and_usage() -> None:
    # Parent fold requires more capacity than the already retained leaf rows.
    ledger = ResourceLedger(max_nodes=1250)
    with LedgeredParityTapeActions(ledger) as cache:
        old = ParityCarryTape.letters((1, 0))
        old_action = old.action(cache=cache)
        before = (ledger.nodes, ledger.entries, cache.retained_entries)
        giant = ParityCarryTape.repeated(old, 8000)
        with pytest.raises(BlockContextBudgetExceeded):
            giant.action(cache=cache)
        assert (ledger.nodes, ledger.entries, cache.retained_entries) == before
        assert old.action(cache=cache) is old_action
        assert ledger.inventory_owner(cache.owner).accounting_delta == 0
    assert ledger.nodes == ledger.entries == 0


def test_mid_fold_arithmetic_failure_releases_new_rows(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    tree = ParityCarryTape.sequence(
        tuple(ParityCarryTape.letters((index % 2,)) for index in range(30))
    )
    with LedgeredParityTapeActions(ledger) as cache:
        old = ParityCarryTape.letters((1, 0))
        old_action = old.action(cache=cache)
        before = (ledger.nodes, ledger.entries, cache.retained_entries)
        original_then = DyadicTerminalFieldAction.then
        calls = 0

        def failing_then(
            self: DyadicTerminalFieldAction, later: DyadicTerminalFieldAction
        ) -> DyadicTerminalFieldAction:
            nonlocal calls
            calls += 1
            if calls == 19:
                raise RuntimeError("injected parent fold failure")
            return original_then(self, later)

        monkeypatch.setattr(DyadicTerminalFieldAction, "then", failing_then)
        with pytest.raises(RuntimeError, match="injected parent fold failure"):
            tree.action(cache=cache)
        assert (ledger.nodes, ledger.entries, cache.retained_entries) == before
        assert ledger.inventory_owner(cache.owner).accounting_delta == 0
        assert old.action(cache=cache) is old_action
    assert ledger.nodes == ledger.entries == 0


def test_entry_capacity_denial_before_cache_publication() -> None:
    ledger = ResourceLedger(max_cache_entries=0)
    with LedgeredParityTapeActions(ledger) as cache:
        with pytest.raises(BlockContextBudgetExceeded):
            ParityCarryTape.letters((1,)).action(cache=cache)
        assert (ledger.entries, ledger.nodes) == (0, 0)


def test_budgeted_start_append_charges_every_rotation_and_prunes_old_roots() -> None:
    ledger = ResourceLedger()
    with LedgeredParityTapeActions(ledger) as cache:
        tape = cache.start((1,))
        for i in range(1, 513):
            tape = cache.append(tape, (i & 1,))
        assert tape.height <= 12
        assert cache.compositions < 12_000
        exact_reachable_rows = _assert_retired_root_row_bound(cache, tape)
        assert cache.live_entries == cache.retained_entries
        assert ledger.entries == 2 * cache.retained_entries
        assert ledger.peak_nodes >= ledger.nodes > 0
        assert all(row.accounting_delta in (None, 0) for row in ledger.inventory())
        assert tape.action(cache=cache) == tape.action()
        _assert_current_root_rows(cache, tape, exact_reachable_rows)
    assert (ledger.nodes, ledger.entries) == (0, 0)


def test_retirement_reserves_full_depth_through_repeated_root() -> None:
    deep = ParityCarryTape.sequence(
        tuple(ParityCarryTape.letters((index & 1,)) for index in range(64))
    )
    repeated = ParityCarryTape.repeated(deep, 3)
    assert repeated.height == 1
    assert repeated.traversal_depth > repeated.height

    ledger = ResourceLedger()
    with LedgeredParityTapeActions(ledger) as cache:
        cache.action(repeated)
        following = ParityCarryTape.sequence((repeated, ParityCarryTape.letters((1,))))
        cache.action(following)
        assert cache.retirement_pending
        cache.action(following)
        assert not cache.retirement_pending
        assert cache.retirement_node_visits > 0
        assert ledger.inventory_owner(cache.owner).accounting_delta == 0
    assert ledger.nodes == ledger.entries == 0


def _cached_parent(
    cache: LedgeredParityTapeActions,
) -> tuple[ParityCarryTape, DyadicTerminalFieldAction, ParityCarryTape]:
    child = ParityCarryTape.letters((1, 0, 1))
    action = cache.action(child)
    parent = ParityCarryTape.sequence((child, ParityCarryTape.letters((0, 0))))
    cache.action(parent)
    return child, action, parent


def test_immediately_retired_root_hit_swaps_pins_without_rebuilding() -> None:
    ledger = ResourceLedger()
    with LedgeredParityTapeActions(ledger) as cache:
        prior, prior_action, current = _cached_parent(cache)
        assert cache.is_current_root(current)
        assert cache.retirement_pending
        before = (
            cache.discovery_edge_visits,
            cache.compositions,
            cache.retained_entries,
            cache.live_entries,
        )

        assert cache.action(prior) is prior_action
        assert cache.is_current_root(prior)
        assert cache.retirement_pending
        assert (
            cache.discovery_edge_visits,
            cache.compositions,
            cache.retained_entries,
            cache.live_entries,
        ) == before
        assert ledger.inventory_owner(cache.owner).accounting_delta == 0
    assert ledger.nodes == ledger.entries == 0


def test_cached_descendant_is_pinned_before_its_retired_parent_is_pruned() -> None:
    ledger = ResourceLedger()
    with LedgeredParityTapeActions(ledger) as cache:
        child, child_action, _retired_parent = _cached_parent(cache)
        current = ParityCarryTape.letters((0, 1, 0))
        cache.action(current)
        assert cache.retirement_pending

        before = (
            cache.discovery_edge_visits,
            cache.compositions,
        )
        assert cache.action(child) is child_action
        assert cache.is_current_root(child)
        assert cache.retirement_pending
        assert (
            cache.discovery_edge_visits,
            cache.compositions,
        ) == before
        assert ledger.inventory_owner(cache.owner).accounting_delta == 0
    assert ledger.nodes == ledger.entries == 0


def test_failed_budgeted_append_is_atomic_and_keeps_source_tape() -> None:
    ledger = ResourceLedger(max_nodes=1000)
    with LedgeredParityTapeActions(ledger) as cache:
        tape = cache.start((1,))
        initial = tape.action(cache=cache)
        attempts = 0
        while True:
            before = (ledger.entries, ledger.nodes, cache.retained_entries)
            try:
                tape = cache.append(tape, (0,))
            except BlockContextBudgetExceeded:
                break
            attempts += 1
            assert attempts < 100  # guard against a dropped resource ceiling
        assert (ledger.entries, ledger.nodes, cache.retained_entries) == before
        assert cache.is_current_root(tape)
        assert cache.action(tape) == tape.action()
        assert cache.action(tape).producer_issued
        assert ledger.peak_nodes <= 1000
        assert ledger.inventory_owner(cache.owner).accounting_delta == 0
        assert tape.prefix_action(1) == initial
    assert ledger.entries == ledger.nodes == 0


def test_failed_seed_preflight_leaves_zero_peak() -> None:
    ledger = ResourceLedger(max_nodes=0)
    with LedgeredParityTapeActions(ledger) as cache:
        with pytest.raises(BlockContextBudgetExceeded):
            cache.start((1,))
        assert cache.is_current_root(None)
        assert (ledger.nodes, ledger.entries, ledger.peak_nodes) == (0, 0, 0)
    assert ledger.entries == ledger.nodes == 0


def test_failed_root_reservation_close_preserves_old_root_and_rows(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.resources.owned_memo import LedgerReservation

    ledger = ResourceLedger()
    with LedgeredParityTapeActions(ledger) as cache:
        old = cache.start((1, 0, 1))
        old_action = cache.action(old)
        before = (ledger.nodes, ledger.entries, cache.retained_entries)
        candidate = ParityCarryTape.sequence((old, ParityCarryTape.letters((0,))))
        original_close = LedgerReservation.close
        close_count = 0

        def close_then_fail(self: LedgerReservation) -> None:
            nonlocal close_count
            close_count += 1
            original_close(self)
            # The fold reservation closes first; the second close is the
            # root-pin reservation, immediately before its commit point.
            if close_count == 2:
                raise RuntimeError("injected pin reservation close failure")

        monkeypatch.setattr(LedgerReservation, "close", close_then_fail)
        with pytest.raises(
            RuntimeError, match="injected pin reservation close failure"
        ):
            cache.action(candidate)
        assert cache.is_current_root(old)
        assert (ledger.nodes, ledger.entries, cache.retained_entries) == before
        assert cache.action(old) is old_action

        monkeypatch.setattr(LedgerReservation, "close", original_close)
        admitted = cache.action(candidate)
        assert cache.is_current_root(candidate)
        assert admitted is cache.action(candidate)
        assert admitted.steps == candidate.steps
    assert ledger.entries == ledger.nodes == 0


def test_revoked_ledger_owner_fails_closed_and_disposal_is_idempotent() -> None:
    ledger = ResourceLedger()
    cache = LedgeredParityTapeActions(ledger)
    root = ParityCarryTape.letters((1, 0, 1))
    cache.action(root)
    ledger.mark_disposed(cache.scratch_owner)
    with pytest.raises(RuntimeError, match="revoked by its ledger"):
        cache.action(root)
    # Teardown can still reclaim the live memo stores after detecting owner
    # revocation; a second disposal is harmless.
    cache.dispose()
    cache.dispose()
    assert ledger.entries == ledger.nodes == 0


def test_failed_cleanup_can_be_retried_without_leaking_ledger_owners(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    cache = LedgeredParityTapeActions(ledger)
    cache.action(ParityCarryTape.letters((1, 0, 1)))
    original_mark_disposed = ResourceLedger.mark_disposed
    failed = False

    def mark_then_fail_once(self: ResourceLedger, owner: int) -> None:
        nonlocal failed
        if self is ledger and owner == cache.scratch_owner and not failed:
            failed = True
            raise RuntimeError("injected resource-owner cleanup failure")
        original_mark_disposed(self, owner)

    monkeypatch.setattr(ResourceLedger, "mark_disposed", mark_then_fail_once)
    with pytest.raises(RuntimeError, match="injected resource-owner cleanup failure"):
        cache.dispose()
    with pytest.raises(RuntimeError, match="failed parity tape action owner"):
        cache.action(ParityCarryTape.letters((0,)))

    monkeypatch.setattr(ResourceLedger, "mark_disposed", original_mark_disposed)
    cache.dispose()
    cache.dispose()
    assert ledger.entries == ledger.nodes == 0

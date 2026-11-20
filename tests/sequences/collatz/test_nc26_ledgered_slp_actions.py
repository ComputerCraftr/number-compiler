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
from tests.support.private_attributes import set_private_test_attribute


def _assert_committed_root_row_bound(
    cache: LedgeredParityTapeActions, tape: ParityCarryTape
) -> int:
    expected_rows = 2 * tape.steps - 1
    assert cache.retained_entries == expected_rows
    assert cache.live_entries == expected_rows
    return expected_rows


def _assert_current_root_rows(
    cache: LedgeredParityTapeActions,
    tape: ParityCarryTape,
    expected_rows: int,
) -> None:
    assert cache.is_current_root(tape)
    assert cache.retained_entries == expected_rows
    assert cache.live_entries == expected_rows


def _root_switch_fixture(
    cache: LedgeredParityTapeActions, ledger: ResourceLedger
) -> tuple[
    ParityCarryTape,
    DyadicTerminalFieldAction,
    tuple[int, int, int],
    ParityCarryTape,
]:
    old = cache.start((1, 0, 1))
    old_action = cache.action(old)
    before = (ledger.nodes, ledger.entries, cache.retained_entries)
    candidate = ParityCarryTape.sequence((old, ParityCarryTape.letters((0,))))
    return old, old_action, before, candidate


def _assert_root_switch_rollback(
    cache: LedgeredParityTapeActions,
    ledger: ResourceLedger,
    old: ParityCarryTape,
    old_action: DyadicTerminalFieldAction,
    before: tuple[int, int, int],
    plan_owner: int,
) -> None:
    assert cache.is_current_root(old)
    assert (ledger.nodes, ledger.entries, cache.retained_entries) == before
    assert ledger.account_usage(plan_owner) == (0, 0)
    assert cache.action(old) is old_action


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
        # This aggregate counts cold-node discovery, retained parent-edge
        # publication, and the old root's changed reference fringe. Persistent
        # append clones O(log n) nodes, so cumulative work is O(n log n).
        assert cache.edge_visits == (
            cache.discovery_edge_visits
            + cache.published_edge_references
            + cache.retirement_node_visits
            + cache.retirement_edge_visits
        )
        assert edge_samples[256] <= 3 * edge_samples[128]
        assert edge_samples[512] <= 3 * edge_samples[256]
        exact_reachable_rows = _assert_committed_root_row_bound(cache, tape)
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
        exact_reachable_rows = _assert_committed_root_row_bound(cache, tape)
        assert cache.live_entries == cache.retained_entries
        assert ledger.entries == 2 * cache.retained_entries
        assert ledger.peak_nodes >= ledger.nodes > 0
        assert all(row.accounting_delta in (None, 0) for row in ledger.inventory())
        assert tape.action(cache=cache) == tape.action()
        _assert_current_root_rows(cache, tape, exact_reachable_rows)
    assert (ledger.nodes, ledger.entries) == (0, 0)


def test_retirement_plan_uses_full_depth_through_repeated_root() -> None:
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
        cache.action(following)
        assert cache.retirement_node_visits > 0
        assert ledger.inventory_owner(cache.owner).accounting_delta == 0
    assert ledger.nodes == ledger.entries == 0


def test_temporary_root_lease_preserves_both_join_parents_without_refolding() -> None:
    ledger = ResourceLedger()
    left = ParityCarryTape.letters((1,))
    right = ParityCarryTape.letters((0,))
    joined = ParityCarryTape.sequence((left, right))
    with LedgeredParityTapeActions(ledger) as cache:
        lease_owner = next(
            item.owner
            for item in ledger.inventory()
            if item.name.endswith("-root-leases")
        )
        baseline_lease_charge = ledger.account_usage(lease_owner)
        left_action = left.action(cache=cache)
        with cache.temporary_root_pin(left) as lease:
            assert ledger.account_usage(lease_owner) == (
                baseline_lease_charge[0] + 1,
                baseline_lease_charge[1] + 16,
            )
            right_action = right.action(cache=cache)
            assert cache.is_current_root(right)
            compositions_before_join = cache.compositions
            joined_action = joined.action(cache=cache)
            assert joined_action == left_action.then(right_action)
            assert cache.compositions == compositions_before_join + 2
            assert cache.is_current_root(joined)
            lease.commit()
        assert ledger.account_usage(lease_owner) == baseline_lease_charge
        # A scoped extra pin on the current root is valid: releasing the lease
        # leaves the current-root reference intact.
        with cache.temporary_root_pin(joined) as lease:
            lease.commit()
        assert cache.is_current_root(joined)
        assert ledger.account_usage(lease_owner) == baseline_lease_charge
        _assert_committed_root_row_bound(cache, joined)
        assert cache.retained_entries == 3
        assert ledger.inventory_owner(cache.owner).accounting_delta == 0
    assert ledger.nodes == ledger.entries == 0


def test_parity_lease_and_join_rows_are_owned_by_audited_memos() -> None:
    from number_compiler.sequences.collatz.collatz_two_sided_ring import (
        CollatzTwoSidedCylinder,
    )
    from number_compiler.sequences.collatz.guarded_port_join import (
        certify_pointed_port_join,
    )

    ledger = ResourceLedger()
    source = CollatzTwoSidedCylinder(7, 7, 0, 1)
    joined = certify_pointed_port_join(
        7,
        DyadicTerminalFieldAction.one_run(1),
        1,
        ledger=ledger,
        source_cylinder=source,
        factor_grammar=(((1,), 1),),
    )
    with LedgeredParityTapeActions(ledger) as cache:
        tape = joined.parity_tape_for_action(cache=cache)
        assert tape is not None
        assert cache.action(tape).producer_issued
        lease_owner = next(
            item.owner
            for item in ledger.inventory()
            if item.name.endswith("-root-leases")
        )
        join_owner = next(
            item.owner
            for item in ledger.inventory()
            if item.name.endswith("-joined-ports")
        )
        with cache.temporary_root_pin(tape):
            cache.retain_guarded_join(joined, nodes=73)
            lease_inventory = ledger.inventory_owner(lease_owner)
            join_inventory = ledger.inventory_owner(join_owner)
            assert (lease_inventory.entries, lease_inventory.nodes) == (1, 16)
            assert (join_inventory.entries, join_inventory.nodes) == (1, 73)
            assert lease_inventory.accounting_delta == 0
            assert join_inventory.accounting_delta == 0
            assert join_inventory.observed_entries == 1
        assert ledger.account_usage(lease_owner) == (0, 0)
        assert ledger.account_usage(join_owner) == (1, 73)
        assert ledger.inventory_owner(join_owner).accounting_delta == 0
    assert ledger.entries == ledger.nodes == 0


def test_temporary_root_lease_root_cannot_be_redirected() -> None:
    ledger = ResourceLedger()
    root = ParityCarryTape.letters((1,))
    other = ParityCarryTape.letters((0,))
    with LedgeredParityTapeActions(ledger) as cache:
        cache.action(root)
        with cache.temporary_root_pin(root) as lease:
            cache.action(other)
            with pytest.raises(AttributeError):
                set_private_test_attribute(lease, "root", other)
            with pytest.raises(AttributeError):
                object.__setattr__(lease, "root", other)
            assert lease.root is root
        assert cache.is_current_root(root)
        assert ledger.inventory_owner(cache.owner).accounting_delta == 0
    assert ledger.entries == ledger.nodes == 0


def test_temporary_root_lease_rolls_back_to_parent_after_failed_composition() -> None:
    ledger = ResourceLedger()
    left = ParityCarryTape.letters((1,))
    right = ParityCarryTape.letters((0,))
    with LedgeredParityTapeActions(ledger) as cache:
        left_action = left.action(cache=cache)
        with pytest.raises(RuntimeError, match="injected staged failure"):
            with cache.temporary_root_pin(left):
                right.action(cache=cache)
                raise RuntimeError("injected staged failure")
        assert cache.is_current_root(left)
        assert left.action(cache=cache) is left_action
        assert cache.retained_entries == 1
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


def _assert_cached_root_reuse(
    cache: LedgeredParityTapeActions,
    root: ParityCarryTape,
    action: DyadicTerminalFieldAction,
) -> None:
    before = (cache.discovery_edge_visits, cache.compositions)
    assert cache.action(root) is action
    assert cache.is_current_root(root)
    assert (cache.discovery_edge_visits, cache.compositions) == before
    assert cache.retained_entries == cache.live_entries == 1


def test_cached_child_root_hit_reuses_action_without_rebuilding() -> None:
    ledger = ResourceLedger()
    with LedgeredParityTapeActions(ledger) as cache:
        prior, prior_action, current = _cached_parent(cache)
        assert cache.is_current_root(current)
        _assert_cached_root_reuse(cache, prior, prior_action)
        assert ledger.inventory_owner(cache.owner).accounting_delta == 0
    assert ledger.nodes == ledger.entries == 0


def test_nested_cached_descendant_is_pinned_before_parent_pruning() -> None:
    ledger = ResourceLedger()
    with LedgeredParityTapeActions(ledger) as cache:
        child = ParityCarryTape.letters((1, 0, 1))
        child_action = cache.action(child)
        parent = ParityCarryTape.sequence((child, ParityCarryTape.letters((0, 0))))
        cache.action(parent)
        current = ParityCarryTape.sequence((parent, ParityCarryTape.letters((1,))))
        cache.action(current)

        _assert_cached_root_reuse(cache, child, child_action)
        assert ledger.inventory_owner(cache.owner).accounting_delta == 0
    assert ledger.nodes == ledger.entries == 0


def test_unrelated_root_is_reclaimed_at_the_switch_commit() -> None:
    ledger = ResourceLedger()
    with LedgeredParityTapeActions(ledger) as cache:
        old = ParityCarryTape.sequence(
            tuple(ParityCarryTape.letters((index & 1,)) for index in range(64))
        )
        cache.action(old)
        assert cache.retained_entries == 127
        new = ParityCarryTape.letters((1, 0, 1))
        cache.action(new)
        assert cache.is_current_root(new)
        assert cache.retained_entries == cache.live_entries == 1
        assert ledger.inventory_owner(cache.owner).accounting_delta == 0
    assert ledger.entries == ledger.nodes == 0


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
        old, old_action, before, candidate = _root_switch_fixture(cache, ledger)
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


@pytest.mark.parametrize("after_apply", (False, True))
def test_failed_plan_transfer_releases_exact_charge_and_keeps_old_root(
    after_apply: bool, monkeypatch: pytest.MonkeyPatch
) -> None:
    from number_compiler.resources.ledger import LedgerReservation

    ledger = ResourceLedger()
    with LedgeredParityTapeActions(ledger) as cache:
        old, old_action, before, candidate = _root_switch_fixture(cache, ledger)
        plan_owner = next(
            item.owner
            for item in ledger.inventory()
            if item.name.endswith("-root-plan")
        )
        transfer = LedgerReservation.transfer_to

        def fail_plan_transfer(
            reservation: LedgerReservation,
            owner: int,
            *,
            entries: int = 0,
            nodes: int = 0,
        ) -> None:
            if owner == plan_owner:
                if after_apply:
                    transfer(reservation, owner, entries=entries, nodes=nodes)
                raise RuntimeError("injected plan transfer failure")
            transfer(reservation, owner, entries=entries, nodes=nodes)

        with monkeypatch.context() as patch:
            patch.setattr(LedgerReservation, "transfer_to", fail_plan_transfer)
            with pytest.raises(RuntimeError, match="injected plan transfer failure"):
                cache.action(candidate)
        _assert_root_switch_rollback(cache, ledger, old, old_action, before, plan_owner)
        assert cache.action(candidate).producer_issued
    assert ledger.entries == ledger.nodes == 0


def test_failed_root_switch_release_restores_live_charge_and_old_root(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    with LedgeredParityTapeActions(ledger) as cache:
        old, old_action, before, candidate = _root_switch_fixture(cache, ledger)
        plan_owner = next(
            item.owner
            for item in ledger.inventory()
            if item.name.endswith("-root-plan")
        )
        original_release = ResourceLedger.release
        release_failed = False

        def release_then_fail_once(
            self: ResourceLedger,
            owner: int,
            entries: int = 0,
            nodes: int = 0,
        ) -> None:
            nonlocal release_failed
            original_release(self, owner, entries=entries, nodes=nodes)
            if (
                self is ledger
                and owner == plan_owner
                and nodes > 0
                and not release_failed
            ):
                release_failed = True
                raise RuntimeError("injected post-publication plan release failure")

        monkeypatch.setattr(ResourceLedger, "release", release_then_fail_once)
        with pytest.raises(RuntimeError, match="post-publication plan release"):
            cache.action(candidate)

        monkeypatch.setattr(ResourceLedger, "release", original_release)
        assert release_failed
        _assert_root_switch_rollback(cache, ledger, old, old_action, before, plan_owner)
        assert cache.action(candidate).producer_issued
        assert cache.is_current_root(candidate)
        assert ledger.inventory_owner(cache.owner).accounting_delta == 0
    assert ledger.nodes == ledger.entries == 0


@pytest.mark.parametrize(
    ("action_store", "fail_restore"),
    ((True, False), (False, False), (True, True)),
)
def test_root_row_delete_failure_is_atomic_or_poisons_owner(
    monkeypatch: pytest.MonkeyPatch,
    action_store: bool,
    fail_restore: bool,
) -> None:
    from number_compiler.resources.owned_memo import LedgerReservation, OwnedMemo

    ledger = ResourceLedger()
    cache = LedgeredParityTapeActions(ledger)
    old = ParityCarryTape.letters((1, 0, 1))
    old_action = cache.action(old)
    before = (ledger.nodes, ledger.entries, cache.retained_entries)
    replacement = ParityCarryTape.letters((0, 1, 0, 1))
    original_delete = OwnedMemo[object, object].__delitem__
    original_adopt = OwnedMemo[object, object].adopt_reserved
    deletion_failed = False

    def delete_then_fail(memo: OwnedMemo[object, object], key: object) -> None:
        nonlocal deletion_failed
        original_delete(memo, key)
        if (
            (memo.node_cost is not None) is action_store
            and key == id(old)
            and not deletion_failed
        ):
            deletion_failed = True
            label = "action" if action_store else "reference"
            raise RuntimeError(f"injected {label}-row deletion failure")

    def reject_restore(
        memo: OwnedMemo[object, object],
        key: object,
        value: object,
        reservation: LedgerReservation,
    ) -> None:
        if fail_restore and memo.node_cost is not None and key == id(old):
            raise RuntimeError("injected action-row rollback failure")
        original_adopt(memo, key, value, reservation)

    monkeypatch.setattr(OwnedMemo, "__delitem__", delete_then_fail)
    if fail_restore:
        monkeypatch.setattr(OwnedMemo, "adopt_reserved", reject_restore)
        expected_error = "action-row rollback failure"
    else:
        expected_error = (
            "action-row deletion failure"
            if action_store
            else "reference-row deletion failure"
        )
    with pytest.raises(RuntimeError, match=expected_error):
        cache.action(replacement)

    monkeypatch.setattr(OwnedMemo, "__delitem__", original_delete)
    monkeypatch.setattr(OwnedMemo, "adopt_reserved", original_adopt)
    if fail_restore:
        with pytest.raises(RuntimeError, match="failed parity tape action owner"):
            cache.action(old)
        cache.dispose()
        assert ledger.entries == ledger.nodes == 0
        return
    assert cache.is_current_root(old)
    assert (ledger.nodes, ledger.entries, cache.retained_entries) == before
    assert cache.action(old) is old_action
    assert ledger.inventory_owner(cache.owner).accounting_delta == 0
    assert cache.action(replacement).producer_issued
    assert cache.is_current_root(replacement)
    cache.dispose()
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

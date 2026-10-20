"""Causal workspace publication rolls back post-mutation audit failures."""

from __future__ import annotations

from collections.abc import Callable, Mapping
from typing import cast

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.tile_causal_admission import admit_run_actions
from number_compiler.resources.causal_types import CausalMemoKey, CausalSpatialValue
from number_compiler.resources.causal_workspace import (
    CausalSpatialWorkspace,
    CausalTaskWorkspace,
)
from number_compiler.resources.ledger import ResourceInventory, ResourceLedger
from tests.support.tile_kernel import make_tile_runtime


def _inject_post_mutation_failures(
    monkeypatch: pytest.MonkeyPatch,
    ledger: ResourceLedger,
    failures: Mapping[int, RuntimeError],
) -> Callable[[], int]:
    original = ledger.note_store_mutation
    calls = 0

    def fail_selected_mutations() -> None:
        nonlocal calls
        calls += 1
        original()
        failure = failures.get(calls)
        if failure is not None:
            raise failure

    monkeypatch.setattr(ledger, "note_store_mutation", fail_selected_mutations)
    return lambda: calls


def _owner_reservation(ledger: ResourceLedger, owner: int) -> tuple[int, int]:
    row = ledger.inventory_owner(owner)
    return row.entries, row.nodes


def _assert_reservations_match_snapshot(
    ledger: ResourceLedger,
    entries: int,
    nodes: int,
    inventory: tuple[ResourceInventory, ...],
) -> None:
    assert ledger.entries == entries
    assert ledger.nodes == nodes
    assert ledger.inventory() == inventory


def test_begin_rolls_back_when_insert_and_rollback_audits_raise(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    workspace = CausalTaskWorkspace(ledger, "begin-publication-failure")
    key: CausalMemoKey = ("transfer", (1, 2))
    before = workspace.audit_snapshot()
    entries, nodes = ledger.entries, ledger.nodes
    inventory = ledger.inventory()
    primary = RuntimeError("active insertion audit failed")
    rollback = RuntimeError("active rollback audit failed")

    with monkeypatch.context() as patch:
        calls = _inject_post_mutation_failures(patch, ledger, {1: primary, 2: rollback})
        with pytest.raises(RuntimeError) as caught:
            workspace.begin(key)

    assert caught.value is primary
    assert calls() == 2
    after = workspace.audit_snapshot()
    assert key not in after.active_store
    assert _owner_reservation(ledger, before.active_owner) == (0, 0)
    _assert_reservations_match_snapshot(ledger, entries, nodes, inventory)

    workspace.begin(key)
    workspace.finish(key, 3)
    assert workspace.memo[key] == 3
    workspace.clear()
    _assert_reservations_match_snapshot(ledger, entries, nodes, inventory)


def test_finish_restores_active_entry_after_delete_and_rollback_audit_failures(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    workspace = CausalTaskWorkspace(ledger, "finish-publication-failure")
    key: CausalMemoKey = ("transfer", (1, 2))
    workspace.begin(key)
    before = workspace.audit_snapshot()
    entries, nodes = ledger.entries, ledger.nodes
    inventory = ledger.inventory()
    primary = RuntimeError("active deletion audit failed")
    rollback = RuntimeError("active restoration audit failed")

    with monkeypatch.context() as patch:
        calls = _inject_post_mutation_failures(patch, ledger, {2: primary, 3: rollback})
        with pytest.raises(RuntimeError) as caught:
            workspace.finish(key, 3)

    assert caught.value is primary
    assert calls() == 4
    after = workspace.audit_snapshot()
    assert dict(after.active_items).get(key) is True
    assert key not in dict(after.memo_items)
    assert _owner_reservation(ledger, before.active_owner) == (1, 0)
    assert _owner_reservation(ledger, before.memo_owner) == (0, 0)
    _assert_reservations_match_snapshot(ledger, entries, nodes, inventory)

    workspace.finish(key, 3)
    assert key not in workspace.active
    assert workspace.memo[key] == 3
    workspace.clear()
    assert ledger.entries == 0
    assert ledger.nodes == 0


def test_action_admission_retries_after_insert_and_rollback_audit_failures(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, _tiles, adapter, action, _scheduler = make_tile_runtime(BaseBlockEffect(3))
    workspace = CausalTaskWorkspace(ledger, "action-admission-failure")
    run = workspace.begin_run()
    before = workspace.audit_snapshot()
    entries, nodes = ledger.entries, ledger.nodes
    inventory = ledger.inventory()
    primary = RuntimeError("admitted action insertion audit failed")
    rollback = RuntimeError("admitted action rollback audit failed")

    try:
        with monkeypatch.context() as patch:
            calls = _inject_post_mutation_failures(
                patch, ledger, {3: primary, 4: rollback}
            )
            with pytest.raises(RuntimeError) as caught:
                admit_run_actions(adapter, workspace, ledger, action)

        assert caught.value is primary
        assert calls() == 4
        failed = workspace.audit_snapshot()
        assert not failed.pending_actions
        assert not failed.admitted_items
        assert failed.action_admission is None
        assert failed.issued_action_admission is None
        assert _owner_reservation(ledger, before.action_pending_owner) == (0, 0)
        assert _owner_reservation(ledger, before.action_admitted_owner) == (0, 0)
        _assert_reservations_match_snapshot(ledger, entries, nodes, inventory)

        token = admit_run_actions(adapter, workspace, ledger, action)
        workspace.admitted_action_metadata(token, adapter, action)
        workspace.clear_action_admission(token)
        completed = workspace.audit_snapshot()
        assert not completed.pending_actions
        assert not completed.admitted_items
        _assert_reservations_match_snapshot(ledger, entries, nodes, inventory)
    finally:
        workspace.end_run(run)
        workspace.clear()


def test_spatial_release_restores_refs_and_remains_retryable_after_two_audit_failures(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    workspace: CausalSpatialWorkspace[CausalSpatialValue] = CausalSpatialWorkspace(
        ledger, "spatial-release-failure"
    )
    retained = workspace.allocate(2)
    attempted = workspace.allocate(2)
    retained.append(11)
    attempted.append(22)
    before_workspace = workspace.audit_snapshot()
    entries, nodes = ledger.entries, ledger.nodes
    inventory = ledger.inventory()
    primary = RuntimeError("spatial reference deletion audit failed")
    rollback = RuntimeError("spatial reference restoration audit failed")

    try:
        with monkeypatch.context() as patch:
            calls = _inject_post_mutation_failures(
                patch, ledger, {1: primary, 2: rollback}
            )
            with pytest.raises(RuntimeError) as caught:
                attempted.close()

        assert caught.value is primary
        assert calls() == 2
        assert workspace.audit_snapshot() == before_workspace
        assert workspace.owns_buffer(retained)
        assert workspace.owns_buffer(attempted)
        assert not retained.closed
        assert not attempted.closed
        assert retained.used == attempted.used == 1
        _assert_reservations_match_snapshot(ledger, entries, nodes, inventory)

        attempted.close()
        assert attempted.closed
        assert not workspace.owns_buffer(attempted)
        assert workspace.owns_buffer(retained)
    finally:
        attempted.close()
        retained.close()

    assert ledger.entries == 0
    assert ledger.nodes == 0


def test_spatial_failed_write_rollback_distinguishes_missing_slot_from_none() -> None:
    ledger = ResourceLedger()
    workspace: CausalSpatialWorkspace[CausalSpatialValue] = CausalSpatialWorkspace(
        ledger, "spatial-missing-rollback-slot"
    )
    buffer = workspace.allocate(1)
    key = (buffer.identity, 0)

    try:
        workspace.restore_reference_after_failed_write(key, 17)
        assert workspace.reference_at(*key) is None

        # A rollback is allowed to observe the reserved, already-restored None
        # slot, but a missing dictionary entry must not masquerade as None.
        reference_store = workspace.audit_snapshot().reference_store
        backing = cast(
            dict[tuple[int, int], CausalSpatialValue | None],
            object.__getattribute__(reference_store, "_data"),
        )
        backing.pop(key)
        with pytest.raises(RuntimeError, match="found no store value"):
            workspace.restore_reference_after_failed_write(key, 17)
    finally:
        workspace.write_reference(key, None)
        buffer.close()

    assert ledger.entries == 0
    assert ledger.nodes == 0

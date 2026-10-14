"""Exact clear accounting for causal task stores, including node charges."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.resources.causal_workspace import CausalTaskWorkspace
from number_compiler.resources.ledger import ResourceLedger


def _workspace_with_admitted_action() -> tuple[
    ResourceLedger, CausalTaskWorkspace, int, int
]:
    ledger = ResourceLedger()
    workspace = CausalTaskWorkspace(ledger, "causal-cleanup-accounting")
    owner = workspace.action_admitted_owner
    action = FieldCellActionID(ArenaToken("cleanup-test"), "field-cell-action", 0)
    nodes = workspace.action_admitted.nodes_per_entry
    ledger.reserve(owner, entries=1, nodes=nodes)
    workspace.action_admitted[action] = (object(),)
    return ledger, workspace, owner, nodes


@pytest.mark.parametrize("failure_timing", ("before", "after"))
def test_causal_action_store_clear_retries_exact_entry_and_node_delta(
    monkeypatch: pytest.MonkeyPatch,
    failure_timing: str,
) -> None:
    ledger, workspace, owner, nodes = _workspace_with_admitted_action()
    original_release = ledger.release
    fail_once = True
    store_nodes = workspace.action_admitted.nodes_per_entry

    def fail_release(
        target: int,
        entries: int = 0,
        nodes: int = 0,
    ) -> None:
        nonlocal fail_once
        if target == owner and entries == 1 and nodes == store_nodes and fail_once:
            fail_once = False
            if failure_timing == "after":
                original_release(target, entries, nodes)
            raise RuntimeError(f"injected {failure_timing} release failure")
        original_release(target, entries, nodes)

    with monkeypatch.context() as patch:
        patch.setattr(ledger, "release", fail_release)
        with pytest.raises(RuntimeError, match="injected .* release failure"):
            workspace.clear()

    account = ledger._account(owner)
    expected_entries = int(failure_timing == "before")
    expected_nodes = nodes if expected_entries else 0
    assert not workspace.action_admitted
    assert (account.entries, account.nodes) == (expected_entries, expected_nodes)

    workspace.clear()
    account = ledger._account(owner)
    assert (account.entries, account.nodes) == (0, 0)
    assert ledger.entries == ledger.nodes == 0


def test_causal_action_store_clear_rejects_unexplained_owner_reservation() -> None:
    ledger, workspace, owner, nodes = _workspace_with_admitted_action()
    ledger.reserve(owner, entries=1)

    with pytest.raises(
        RuntimeError, match="store clear differs from its owner reservation"
    ):
        workspace.clear()

    account = ledger._account(owner)
    assert not workspace.action_admitted
    assert (account.entries, account.nodes) == (2, nodes)

    # Remove only the deliberately unexplained reservation. The recorded clear
    # delta can then be retried exactly, without reconciling the whole account.
    ledger.release(owner, entries=1)
    workspace.clear()
    account = ledger._account(owner)
    assert (account.entries, account.nodes) == (0, 0)
    assert ledger.entries == ledger.nodes == 0

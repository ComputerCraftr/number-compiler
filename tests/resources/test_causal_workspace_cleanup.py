"""Causal workspace clears account only for their exact retained stores."""

from __future__ import annotations

import pytest

from number_compiler.resources.causal_types import CausalMemoKey
from number_compiler.resources.causal_workspace import CausalTaskWorkspace
from number_compiler.resources.ledger import ResourceLedger
from tests.support.ledger_failures import inject_release_failure


def _workspace_with_memo_entry() -> tuple[
    ResourceLedger,
    CausalTaskWorkspace,
    CausalMemoKey,
]:
    ledger = ResourceLedger()
    workspace = CausalTaskWorkspace(ledger, "causal-clear-test")
    key = ("test", ())
    ledger.reserve(workspace.memo_owner, entries=1)
    workspace.memo[key] = False
    return ledger, workspace, key


def test_causal_clear_rejects_unexplained_owner_charge() -> None:
    ledger, workspace, _key = _workspace_with_memo_entry()
    ledger.reserve(workspace.memo_owner, entries=1)

    with pytest.raises(
        RuntimeError, match="store clear differs from its owner reservation"
    ):
        workspace.clear()

    assert not workspace.memo
    assert ledger._account(workspace.memo_owner).entries == 2
    assert workspace._memo_clear_retry.pending == (1, 0)


@pytest.mark.parametrize("failure_timing", ("before", "after"))
def test_causal_clear_retries_exact_delta_after_release_failure(
    monkeypatch: pytest.MonkeyPatch,
    failure_timing: str,
) -> None:
    ledger, workspace, _key = _workspace_with_memo_entry()
    owner = workspace.memo_owner
    with monkeypatch.context() as patch:
        inject_release_failure(
            patch, ledger, owner, entries=1, after_apply=failure_timing == "after"
        )
        with pytest.raises(RuntimeError, match="injected ledger release failure"):
            workspace.clear()

    expected_entries = int(failure_timing == "before")
    expected_pending = (expected_entries, 0)
    assert not workspace.memo
    assert ledger._account(owner).entries == expected_entries
    assert workspace._memo_clear_retry.pending == expected_pending

    workspace.clear()
    assert ledger._account(owner).entries == 0
    assert workspace._memo_clear_retry.pending == (0, 0)

"""Failure injection for retained-store publication regressions."""

from __future__ import annotations

from collections.abc import Callable
from typing import cast

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.ledger_records import ResourceInventory
from number_compiler.resources.stores import LedgerDict


def assert_empty_ledger_account(
    ledger: ResourceLedger, account_name: str
) -> ResourceInventory:
    """Require one live, empty account with the requested name."""
    matches = [item for item in ledger.inventory() if item.name == account_name]
    assert len(matches) == 1
    account = matches[0]
    assert not account.disposed
    assert account.entries == account.nodes == 0
    return account


def assert_constructor_rollback(ledger: ResourceLedger, initial_inventory: int) -> None:
    """Check newly registered owners, roots and storage after a failed factory."""
    created = ledger.inventory()[initial_inventory:]
    assert all(item.disposed and item.entries == item.nodes == 0 for item in created)
    assert tuple(ledger.iter_execution_roots()) == ()
    assert ledger.entries == ledger.nodes == 0


def inject_write_once_failure(
    monkeypatch: pytest.MonkeyPatch,
    target: object,
    *,
    after_insert: bool,
) -> None:
    """Fail one selected write-once map before or after its insertion."""
    original = cast(
        Callable[[LedgerDict[object, object], object, object], None],
        object.__getattribute__(LedgerDict, "__setitem__"),
    )

    def fail_selected_store(
        store: LedgerDict[object, object], key: object, value: object
    ) -> None:
        if store is target:
            if after_insert:
                original(store, key, value)
            raise RuntimeError("injected issued-store publication failure")
        original(store, key, value)

    monkeypatch.setattr(LedgerDict, "__setitem__", fail_selected_store)


def inject_release_failure(
    monkeypatch: pytest.MonkeyPatch,
    ledger: ResourceLedger,
    owner: int,
    *,
    entries: int,
    after_apply: bool,
) -> None:
    """Fail one matching release, either before or after its accounting update."""
    release = ledger.release
    fail_once = True

    def fail_selected_release(target: int, entries: int = 0, nodes: int = 0) -> None:
        nonlocal fail_once
        if target == owner and entries == expected_entries and fail_once:
            fail_once = False
            if after_apply:
                release(target, entries, nodes)
            raise RuntimeError("injected ledger release failure")
        release(target, entries, nodes)

    expected_entries = entries
    monkeypatch.setattr(ledger, "release", fail_selected_release)

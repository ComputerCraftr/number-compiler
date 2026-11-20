from __future__ import annotations

import sys
from collections.abc import Callable

import pytest

from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.lifecycle import cleanup_all, cleanup_on_error
from number_compiler.resources.stores import LedgerDict


def test_cleanup_all_attempts_every_owner_and_keeps_failure_chain() -> None:
    events: list[str] = []

    def first() -> None:
        events.append("first")
        raise RuntimeError("first cleanup")

    def second() -> None:
        events.append("second")
        raise ValueError("second cleanup")

    def last() -> None:
        events.append("last")

    with pytest.raises(ValueError, match="second cleanup") as failure:
        cleanup_all((first, second, last))

    assert events == ["first", "second", "last"]
    assert isinstance(failure.value.__context__, RuntimeError)
    assert str(failure.value.__context__) == "first cleanup"


def test_cleanup_all_retains_active_cause_and_all_cleanup_failures() -> None:
    events: list[str] = []
    construction_error = LookupError("original construction failure")

    def first() -> None:
        events.append("first")
        raise RuntimeError("first cleanup")

    def second() -> None:
        events.append("second")
        raise ValueError("second cleanup")

    try:
        raise construction_error
    except LookupError as active:
        with pytest.raises(ValueError, match="second cleanup") as failure:
            cleanup_all((first, second))
        assert failure.value.__cause__ is active

    assert events == ["first", "second"]
    assert isinstance(failure.value.__context__, RuntimeError)
    assert str(failure.value.__context__) == "first cleanup"
    assert failure.value.__cause__ is construction_error


def test_cleanup_all_preserves_rethrown_active_exception_and_success_path() -> None:
    original = LookupError("active exception")
    ran: list[str] = []

    def rethrow_active() -> None:
        ran.append("rethrow")
        raise original

    try:
        raise original
    except LookupError as active:
        with pytest.raises(LookupError, match="active exception") as failure:
            cleanup_all((rethrow_active,))
        assert failure.value is active
        assert failure.value.__cause__ is None

    assert ran == ["rethrow"]
    succeeded: list[str] = []
    try:
        raise LookupError("successful cleanup context")
    except LookupError as active:
        cleanup_all((lambda: succeeded.append("cleaned"),))
        assert sys.exception() is active
    assert succeeded == ["cleaned"]


def test_cleanup_on_error_preserves_successful_owner_and_chains_rollback_failure() -> (
    None
):
    events: list[str] = []

    with cleanup_on_error(lambda: events.append("unexpected cleanup")):
        pass
    assert events == []

    def broken_cleanup() -> None:
        events.append("rollback")
        raise RuntimeError("rollback failed")

    with (
        pytest.raises(RuntimeError, match="rollback failed") as failure,
        cleanup_on_error(broken_cleanup),
    ):
        raise ValueError("construction failed")

    assert events == ["rollback"]
    assert isinstance(failure.value.__context__, ValueError)
    assert str(failure.value.__context__) == "construction failed"


def test_ledgered_slp_fast_paths_reject_use_after_dispose() -> None:
    from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
    from number_compiler.resources.ledger import ResourceLedger

    arena = LedgerSLPArena(ResourceLedger(), "lifecycle-test", "slp")
    root = arena.word((1, 2))
    empty = arena.empty()
    arena.dispose()

    operations = (
        arena.empty,
        lambda: arena.terminal(1),
        lambda: arena.concat(empty, root),
        lambda: arena.concat(root, empty),
        lambda: arena.repeat(root, 0),
        lambda: arena.repeat(empty, 3),
        lambda: arena.concat_many((empty, root)),
        lambda: arena.word((1,)),
        lambda: arena.materialize(root),
        lambda: arena.reachable(root),
        lambda: arena.metrics(root),
    )
    for operation in operations:
        with pytest.raises(ValueError, match="disposed"):
            operation()


@pytest.mark.parametrize("raise_after_release", (False, True))
def test_owned_memo_clear_retries_exact_accounting_after_release_failure(
    raise_after_release: bool,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    owner = ledger.register("clear-retry", "query_memo")
    memo: OwnedMemo[str, str] = OwnedMemo(ledger, owner, nodes_per_entry=2)
    memo["entry"] = "payload"
    original_release = ledger.release
    failed = False

    def fail_once(target: int, entries: int = 0, nodes: int = 0) -> None:
        nonlocal failed
        if target == owner and not failed:
            failed = True
            if raise_after_release:
                original_release(target, entries, nodes)
            raise RuntimeError("injected ledger release failure")
        original_release(target, entries, nodes)

    monkeypatch.setattr(ledger, "release", fail_once)
    with pytest.raises(RuntimeError, match="injected ledger release failure"):
        memo.clear()

    if raise_after_release:
        assert ledger.inventory_owner(owner).entries == 0
        assert ledger.inventory_owner(owner).nodes == 0
    else:
        assert ledger.inventory_owner(owner).entries == 1
        assert ledger.inventory_owner(owner).nodes == 2
    assert len(memo) == 0

    memo.clear()
    assert ledger.inventory_owner(owner).entries == 0
    assert ledger.inventory_owner(owner).nodes == 0
    memo.dispose()


def _memo_with_one_entry(
    ledger: ResourceLedger,
    owner: int,
    *,
    dynamic_cost: bool,
) -> tuple[OwnedMemo[str, tuple[int, ...]], tuple[int, ...], int]:
    payload = (2, 3, 5)
    charged_nodes = 4
    if dynamic_cost:
        memo: OwnedMemo[str, tuple[int, ...]] = OwnedMemo(
            ledger, owner, node_cost=lambda _key, value: len(value)
        )
    else:
        memo = OwnedMemo(ledger, owner, nodes_per_entry=charged_nodes)
    memo["entry"] = payload
    return memo, payload, charged_nodes


def _assert_memo_owner_released(ledger: ResourceLedger, owner: int) -> None:
    assert ledger.account_usage(owner) == (0, 0)
    assert ledger.entries == ledger.nodes == 0


@pytest.mark.parametrize("failure_timing", ("before", "after"))
def test_dynamic_memo_replacement_reconciles_release_failure(
    failure_timing: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    ledger = ResourceLedger()
    owner = ledger.register("replace-retry", "query_memo")
    memo = OwnedMemo[str, str](ledger, owner, node_cost=lambda _key, value: len(value))
    memo["entry"] = "long"
    original_release = ledger.release
    failures = 0

    def fail_release(target: int, entries: int = 0, nodes: int = 0) -> None:
        nonlocal failures
        if target == owner and nodes == 3:
            failures += 1
            if failure_timing == "after":
                original_release(target, entries, nodes)
            raise RuntimeError("injected replacement release failure")
        original_release(target, entries, nodes)

    with monkeypatch.context() as patch:
        patch.setattr(ledger, "release", fail_release)
        with pytest.raises(RuntimeError, match="replacement release failure"):
            memo["entry"] = "x"

    assert memo["entry"] == "x"
    assert failures >= 1
    memo.dispose()
    _assert_memo_owner_released(ledger, owner)


@pytest.mark.parametrize("dynamic_cost", (False, True))
@pytest.mark.parametrize("failure_timing", ("before", "after"))
def test_owned_memo_delete_reconciles_release_failure_before_disposal(
    dynamic_cost: bool,
    failure_timing: str,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    owner = ledger.register("delete-retry", "query_memo")
    memo, _payload, charged_nodes = _memo_with_one_entry(
        ledger, owner, dynamic_cost=dynamic_cost
    )
    original_release = ledger.release

    def fail_selected_release(target: int, entries: int = 0, nodes: int = 0) -> None:
        if target == owner and entries == 1 and nodes == charged_nodes:
            if failure_timing == "after":
                original_release(target, entries, nodes)
            raise RuntimeError("injected memo delete release failure")
        original_release(target, entries, nodes)

    with monkeypatch.context() as patch:
        patch.setattr(ledger, "release", fail_selected_release)
        with pytest.raises(RuntimeError, match="memo delete release failure"):
            del memo["entry"]

    assert len(memo) == 0
    pending = memo.audit_snapshot()
    if failure_timing == "before":
        assert ledger.account_usage(owner) == (1, charged_nodes)
        assert (pending.pending_clear_entries, pending.pending_clear_nodes) == (
            1,
            charged_nodes,
        )
    else:
        assert ledger.account_usage(owner) == (0, 0)
        assert (pending.pending_clear_entries, pending.pending_clear_nodes) == (0, 0)

    memo.dispose()
    _assert_memo_owner_released(ledger, owner)


@pytest.mark.parametrize("dynamic_cost", (False, True))
@pytest.mark.parametrize("after_delete", (False, True))
def test_owned_memo_delete_reconciles_store_mutation_failure(
    dynamic_cost: bool,
    after_delete: bool,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    owner = ledger.register("store-delete-retry", "query_memo")
    memo, payload, charged_nodes = _memo_with_one_entry(
        ledger, owner, dynamic_cost=dynamic_cost
    )
    store = memo.audit_snapshot().container
    original_delete: Callable[[LedgerDict[object, object], object], None] = LedgerDict[
        object, object
    ].__delitem__

    def delete_then_fail(target: LedgerDict[object, object], key: object) -> None:
        if target is store and key == "entry":
            if after_delete:
                original_delete(target, key)
            raise RuntimeError("injected memo store deletion failure")
        original_delete(target, key)

    with monkeypatch.context() as patch:
        patch.setattr(LedgerDict, "__delitem__", delete_then_fail)
        with pytest.raises(RuntimeError, match="memo store deletion failure"):
            del memo["entry"]

    if after_delete:
        assert len(memo) == 0
        assert ledger.account_usage(owner) == (0, 0)
        assert memo.audit_snapshot().dynamic_nodes == 0
    else:
        assert len(memo) == 1
        assert memo["entry"] == payload
        assert ledger.account_usage(owner) == (1, charged_nodes)
        assert memo.audit_snapshot().dynamic_nodes == (
            charged_nodes if dynamic_cost else 0
        )

    memo.dispose()
    _assert_memo_owner_released(ledger, owner)

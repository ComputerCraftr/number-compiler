from __future__ import annotations

import sys

import pytest

from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.lifecycle import cleanup_all, cleanup_on_error


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

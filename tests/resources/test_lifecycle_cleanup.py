from __future__ import annotations

import pytest

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

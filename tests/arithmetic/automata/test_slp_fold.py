"""Ordered shared grammar folds and pre-allocation budget callbacks."""

from typing import NoReturn

import pytest

from number_compiler.arithmetic.automata.slp import SLPArena, SLPNode
from number_compiler.arithmetic.automata.slp_interval import fold_slp_dag


def test_reclaimable_fold_rejects_a_cycle_below_the_root() -> None:
    arena = SLPArena()
    arena.nodes.clear()
    arena.nodes.extend(
        (
            SLPNode(0, "CONCAT", 4, left=1, right=2),
            SLPNode(1, "CONCAT", 3, left=3, right=4),
            SLPNode(2, "TERM", 1, symbol=2),
            SLPNode(3, "CONCAT", 2, left=1, right=5),
            SLPNode(4, "TERM", 1, symbol=1),
            SLPNode(5, "TERM", 1, symbol=3),
        )
    )

    with pytest.raises(ValueError, match="grammar contains a cycle"):
        fold_slp_dag(
            arena,
            0,
            empty_value=tuple[int, ...](),
            terminal_value=lambda digit: (digit,),
            concatenate=lambda first, second: first + second,
            repeat=lambda word, count: word * count,
            reclaim_values=True,
        )


def test_reclaimable_fold_accepts_non_topological_node_ids() -> None:
    arena = SLPArena()
    arena.nodes.clear()
    arena.nodes.extend(
        (
            SLPNode(0, "CONCAT", 3, left=2, right=1),
            SLPNode(1, "TERM", 1, symbol=2),
            SLPNode(2, "CONCAT", 2, left=3, right=4),
            SLPNode(3, "TERM", 1, symbol=1),
            SLPNode(4, "TERM", 1, symbol=3),
        )
    )

    values = fold_slp_dag(
        arena,
        0,
        empty_value=tuple[int, ...](),
        terminal_value=lambda digit: (digit,),
        concatenate=lambda first, second: first + second,
        repeat=lambda word, count: word * count,
        reclaim_values=True,
    )

    assert values == {0: (1, 3, 2)}


@pytest.mark.parametrize("stage", ("schedule", "evaluate"))
def test_capacity_refusal_precedes_source_evaluation(stage: str) -> None:
    arena = SLPArena()
    root = arena.word((1, 2, 3))

    def refuse(_count: int) -> NoReturn:
        raise MemoryError("no worklist capacity")

    def forbid_terminal(_digit: int) -> NoReturn:
        raise AssertionError("source evaluated before worklist admission")

    with pytest.raises(MemoryError, match="no worklist capacity"):
        fold_slp_dag(
            arena,
            root,
            empty_value=tuple[int, ...](),
            terminal_value=forbid_terminal,
            concatenate=lambda first, second: first + second,
            repeat=lambda word, count: word * count,
            on_schedule=refuse if stage == "schedule" else None,
            on_evaluate=refuse if stage == "evaluate" else None,
        )


def test_shared_repeat_fold_keeps_word_order_and_reduces_nodes_once() -> None:
    arena = SLPArena()
    block = arena.word((1, 2))
    root = arena.concat(arena.repeat(block, 3), block)
    reduced: list[int] = []
    scheduled: list[int] = []
    values = fold_slp_dag(
        arena,
        root,
        empty_value=tuple[int, ...](),
        terminal_value=lambda digit: (digit,),
        concatenate=lambda first, second: first + second,
        repeat=lambda word, count: word * count,
        on_schedule=scheduled.append,
        on_reduce=reduced.append,
    )
    assert values[root] == (1, 2) * 4
    assert len(reduced) == len(set(reduced)) == len(values)
    assert sum(scheduled) >= len(values)
    assert all(count == 1 for count in scheduled)


def test_reclaimable_fold_keeps_shared_values_until_last_parent() -> None:
    arena = SLPArena()
    shared = arena.word((1, 2))
    left = arena.concat(shared, arena.terminal(3))
    right = arena.concat(shared, arena.terminal(4))
    root = arena.concat(left, right)
    released_values: list[int] = []
    reference_entries: list[int] = []
    reference_releases: list[int] = []
    values = fold_slp_dag(
        arena,
        root,
        empty_value=tuple[int, ...](),
        terminal_value=lambda digit: (digit,),
        concatenate=lambda first, second: first + second,
        repeat=lambda word, count: word * count,
        reclaim_values=True,
        on_reference_entry=reference_entries.append,
        on_reference_release=reference_releases.append,
        on_value_release=released_values.append,
    )
    reachable = set(reference_entries)
    assert values == {root: (1, 2, 3, 1, 2, 4)}
    assert len(reference_entries) == len(reachable)
    assert set(reference_releases) == reachable
    assert len(reference_releases) == len(reachable)
    assert set(released_values) == reachable - {root}
    assert len(released_values) == len(reachable) - 1
    assert shared in released_values


def test_live_worklist_reservations_balance_on_success_and_failure() -> None:
    arena = SLPArena()
    root = arena.concat(arena.terminal(1), arena.terminal(2))
    scheduled = 0
    unscheduled = 0
    live = 0

    def reserve(count: int) -> None:
        nonlocal scheduled, live
        scheduled += count
        live += count

    def release(count: int) -> None:
        nonlocal unscheduled, live
        assert 0 < count <= live
        unscheduled += count
        live -= count

    fold_slp_dag(
        arena,
        root,
        empty_value=tuple[int, ...](),
        terminal_value=lambda digit: (digit,),
        concatenate=lambda first, second: first + second,
        repeat=lambda word, count: word * count,
        on_schedule=reserve,
        on_unschedule=release,
        reclaim_values=True,
    )
    assert live == 0 and scheduled == unscheduled

    scheduled = unscheduled = live = 0

    def fail_evaluate(_node_id: int) -> NoReturn:
        raise RuntimeError("injected fold evaluation failure")

    with pytest.raises(RuntimeError, match="injected fold evaluation failure"):
        fold_slp_dag(
            arena,
            root,
            empty_value=tuple[int, ...](),
            terminal_value=lambda digit: (digit,),
            concatenate=lambda first, second: first + second,
            repeat=lambda word, count: word * count,
            on_schedule=reserve,
            on_evaluate=fail_evaluate,
            on_unschedule=release,
            reclaim_values=True,
        )
    assert live == 0 and scheduled == unscheduled


def test_reducer_failure_drops_partial_fold_from_retained_traceback() -> None:
    arena = SLPArena()
    root = arena.word((1, 2, 3, 4))

    def fail_reduce(_node_id: int) -> NoReturn:
        raise RuntimeError("injected reducer failure")

    empty = tuple[int, ...]()
    with pytest.raises(RuntimeError, match="injected reducer failure") as captured:
        fold_slp_dag(
            arena,
            root,
            empty_value=empty,
            terminal_value=lambda digit: (digit,),
            concatenate=lambda first, second: first + second,
            repeat=lambda word, count: word * count,
            on_reduce=fail_reduce,
        )

    frame = captured.value.__traceback__
    fold_locals: dict[str, object] | None = None
    while frame is not None:
        if frame.tb_frame.f_code.co_name == "fold_slp_dag":
            fold_locals = frame.tb_frame.f_locals
            break
        frame = frame.tb_next
    assert fold_locals is not None
    assert fold_locals["values"] == {}
    assert fold_locals["tasks"] == []
    assert fold_locals["value"] is empty

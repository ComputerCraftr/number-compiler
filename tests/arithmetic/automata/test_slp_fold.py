"""Ordered shared grammar folds and pre-allocation budget callbacks."""

from typing import NoReturn

import pytest

from number_compiler.arithmetic.automata.slp import SLPArena
from number_compiler.arithmetic.automata.slp_interval import fold_slp_dag


def test_schedule_refusal_precedes_source_evaluation() -> None:
    arena = SLPArena()
    root = arena.word((1, 2, 3))

    def refuse(count: int) -> NoReturn:
        assert count == 1
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
            on_schedule=refuse,
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

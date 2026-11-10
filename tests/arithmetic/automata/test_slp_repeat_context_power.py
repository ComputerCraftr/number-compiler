"""Exact regular projection of repeated SLP blocks by finite context orbits."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.automata.slp import BimachineSLPProjector, SLPArena
from number_compiler.arithmetic.automata.transducer import (
    DFA,
    LazyBimachine,
    build_pair_step_bimachine,
    end_tag,
    parity_tag,
)
from number_compiler.arithmetic.functions.residual import minimize_bimachine


@pytest.mark.parametrize("block", ((10, 11), (0, 18), (9, 10, 11), (1, 7, 16)))
@pytest.mark.parametrize("copies", (2, 3, 5, 8, 17))
def test_repeated_block_projection_matches_literal_bimachine(
    block: tuple[int, ...], copies: int
) -> None:
    machine = minimize_bimachine(
        build_pair_step_bimachine(10), cache_outputs=False
    ).machine
    arena = SLPArena()
    repeated = arena.repeat(arena.word(block), copies)
    source = arena.concat_many(
        (arena.terminal(parity_tag(0, 10)), repeated, arena.terminal(end_tag(10)))
    )

    projected = BimachineSLPProjector(machine, arena).apply(source)
    literal = (parity_tag(0, 10),) + block * copies + (end_tag(10),)

    assert arena.materialize(projected) == machine.output(literal)


def test_nonuniform_repeat_projection_is_bounded_by_context_cycles() -> None:
    machine = minimize_bimachine(
        build_pair_step_bimachine(10), cache_outputs=False
    ).machine
    arena = SLPArena()
    repeated = arena.repeat(arena.word((10, 11)), 10**12)
    source = arena.concat_many(
        (arena.terminal(parity_tag(0, 10)), repeated, arena.terminal(end_tag(10)))
    )
    projector = BimachineSLPProjector(machine, arena)

    projected = projector.apply(source)

    assert arena.nodes[projected].length > 10**12
    assert projector.section_calls < 1200
    assert len(arena.nodes) < 1200


@pytest.mark.parametrize("copies", (2, 3, 4, 5, 6, 7, 11, 15, 31))
def test_repeat_preserves_distinct_left_and_right_transients(copies: int) -> None:
    left_successors = (1, 2, 1)
    right_successors = (1, 2, 3, 4, 2)

    def transitions(successors: tuple[int, ...]) -> dict[tuple[int, int], int]:
        return {
            (state, symbol): successor if symbol == 1 else state
            for state, successor in enumerate(successors)
            for symbol in (1, 2)
        }

    machine = LazyBimachine(
        10,
        (1, 2),
        DFA((1, 2), 0, transitions(left_successors), tuple(range(3))),
        DFA((1, 2), 0, transitions(right_successors), tuple(range(5)), right=True),
        lambda left, _symbol, right: (5 * left + right,),
        cache_enabled=False,
    )
    arena = SLPArena()
    root = arena.repeat(arena.word((1, 2)), copies)
    projector = BimachineSLPProjector(machine, arena)

    output = projector.apply(root)

    assert arena.materialize(output) == machine.output((1, 2) * copies)
    assert projector.section_calls < 100


def _partial_machine() -> LazyBimachine:
    left = DFA((1,), 0, {(0, 1): 1}, (0, 1))
    right = DFA((1,), 0, {(0, 1): 1}, (0, 1), right=True)
    return LazyBimachine(
        10,
        (1,),
        left,
        right,
        lambda _left, symbol, _right: (symbol,),
        cache_enabled=False,
    )


def test_partial_dfa_may_reject_after_the_last_demanded_repeat() -> None:
    arena = SLPArena()
    source = arena.repeat(arena.terminal(1), 2)

    projected = BimachineSLPProjector(_partial_machine(), arena).apply(source)

    assert arena.materialize(projected) == (1, 1)


def test_partial_dfa_rejects_when_a_later_repeat_needs_the_missing_context() -> None:
    arena = SLPArena()
    source = arena.repeat(arena.terminal(1), 3)

    with pytest.raises(ValueError, match="context reject in repeat"):
        BimachineSLPProjector(_partial_machine(), arena).apply(source)


def test_failed_projection_clears_buffers_retained_by_traceback() -> None:
    transitions = {(0, symbol): 0 for symbol in (1, 2)}
    left = DFA((1, 2), 0, transitions, (0,))
    right = DFA((1, 2), 0, transitions, (0,), right=True)
    machine = LazyBimachine(
        10,
        (1, 2),
        left,
        right,
        lambda _left, symbol, _right: (symbol,) if symbol == 1 else None,
        cache_enabled=False,
    )
    arena = SLPArena()
    source = arena.repeat(arena.word((1, 2)), 4)
    projector = BimachineSLPProjector(machine, arena)

    with pytest.raises(ValueError, match="undefined bimachine output") as raised:
        projector.apply(source)

    frame = _projector_frame(raised.value, "block")
    for name in (
        "tasks",
        "values",
        "positions",
        "parts",
        "middle",
        "prefix_parts",
        "suffix_parts",
        "tail_parts",
        "left_orbit",
        "right_orbit",
    ):
        assert frame[name] == []
    projector.clear_caches()


def test_action_failures_clear_task_stacks_retained_by_traceback() -> None:
    arena = SLPArena()
    projector = BimachineSLPProjector(_partial_machine(), arena)

    with pytest.raises(IndexError) as raised:
        projector.forward(999, 0)
    frame = _projector_frame(raised.value, "_action")
    assert frame["tasks"] == []
    assert frame["values"] == []


def _projector_frame(error: BaseException, name: str) -> dict[str, object]:
    traceback = error.__traceback__
    while traceback is not None:
        frame = traceback.tb_frame
        if frame.f_code.co_name == name:
            return frame.f_locals
        traceback = traceback.tb_next
    raise AssertionError(f"exception did not retain the {name} projector frame")

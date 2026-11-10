from __future__ import annotations

from collections.abc import Callable

import pytest

from number_compiler.arithmetic.automata.slp import SLPArena, SLPNode
from number_compiler.arithmetic.automata.slp_walks import iter_symbols
from number_compiler.resources.ledger import ResourceLedger


def _walk_callbacks(
    ledger: ResourceLedger, owner: int
) -> tuple[Callable[[], None], Callable[[int], None]]:
    def reserve() -> None:
        ledger.reserve(owner, entries=1, nodes=1)

    def release(count: int) -> None:
        ledger.release(owner, entries=count, nodes=count)

    return reserve, release


def _pending_walk_fixture() -> tuple[
    SLPArena,
    int,
    ResourceLedger,
    Callable[[], None],
    Callable[[int], None],
]:
    arena = SLPArena()
    root = arena.concat(arena.word((1, 2)), arena.word((3, 4)))
    ledger = ResourceLedger()
    owner = ledger.register("walk", "slp_walk_workspace")
    reserve, release = _walk_callbacks(ledger, owner)
    return arena, root, ledger, reserve, release


def test_shared_slp_walk_preserves_repeat_and_reverse_order() -> None:
    arena = SLPArena()
    repeated = arena.repeat(arena.word((1, 2)), 3)
    root = arena.concat(repeated, arena.word((3, 4)))
    ledger = ResourceLedger()
    owner = ledger.register("walk", "slp_walk_workspace")
    reserve, release = _walk_callbacks(ledger, owner)
    tasks: list[bool] = []

    forward = tuple(
        iter_symbols(
            arena,
            root,
            on_task=tasks.append,
            reserve_task=reserve,
            release_tasks=release,
        )
    )
    backward = tuple(
        iter_symbols(
            arena,
            root,
            reverse=True,
            reserve_task=reserve,
            release_tasks=release,
        )
    )

    assert forward == (1, 2, 1, 2, 1, 2, 3, 4)
    assert backward == tuple(reversed(forward))
    assert tasks.count(True) == 14
    assert tasks.count(False) == 3
    assert ledger.entries == ledger.nodes == 0


def test_shared_slp_walk_releases_pending_tasks_when_cancelled() -> None:
    arena, root, ledger, reserve, release = _pending_walk_fixture()
    stream = iter_symbols(
        arena,
        root,
        reserve_task=reserve,
        release_tasks=release,
    )

    assert next(stream) == 1
    assert ledger.entries > 0
    stream.close()

    assert ledger.entries == ledger.nodes == 0


def test_shared_slp_walk_rejects_unknown_node_and_releases_stack() -> None:
    arena = SLPArena()
    root = arena.terminal(7)
    arena.nodes[root] = SLPNode(root, "UNKNOWN", 1)
    ledger = ResourceLedger()
    owner = ledger.register("walk", "slp_walk_workspace")
    reserve, release = _walk_callbacks(ledger, owner)
    stream = iter_symbols(
        arena,
        root,
        reserve_task=reserve,
        release_tasks=release,
    )

    with pytest.raises(ValueError, match="unknown SLP node kind"):
        next(stream)

    assert ledger.entries == ledger.nodes == 0


def test_failed_slp_walk_clears_charged_pending_tasks_from_traceback() -> None:
    arena, root, ledger, reserve, release = _pending_walk_fixture()
    reserve_count = 0
    release_count = 0
    visits = 0

    def counted_reserve() -> None:
        nonlocal reserve_count
        reserve_count += 1
        reserve()

    def counted_release(count: int) -> None:
        nonlocal release_count
        release_count += count
        release(count)

    def fail_with_pending_task(_is_node: bool) -> None:
        nonlocal visits
        visits += 1
        if visits == 2:
            raise RuntimeError("injected stream observer failure")

    stream = iter_symbols(
        arena,
        root,
        on_task=fail_with_pending_task,
        reserve_task=counted_reserve,
        release_tasks=counted_release,
    )
    with pytest.raises(
        RuntimeError, match="injected stream observer failure"
    ) as caught:
        next(stream)
    assert caught.value.__cause__ is None
    assert caught.value.__context__ is None

    frame = caught.value.__traceback__
    walk_locals: dict[str, object] | None = None
    while frame is not None:
        if frame.tb_frame.f_code.co_name == "iter_symbols":
            walk_locals = frame.tb_frame.f_locals
            break
        frame = frame.tb_next
    assert walk_locals is not None
    assert walk_locals["tasks"] == []
    assert walk_locals["retained"] == 0
    assert reserve_count == release_count
    assert ledger.entries == ledger.nodes == 0

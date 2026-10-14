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
    arena = SLPArena()
    root = arena.concat(arena.word((1, 2)), arena.word((3, 4)))
    ledger = ResourceLedger()
    owner = ledger.register("walk", "slp_walk_workspace")
    reserve, release = _walk_callbacks(ledger, owner)
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

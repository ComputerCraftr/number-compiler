"""Production diamonds use the shared scheduler, not standalone scan drivers."""

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.continuations.diamond_context_program import (
    ContextObservation,
)
from number_compiler.hashlife.execution.continuations.diamond_tasks import PairSummary
from number_compiler.hashlife.observation.diamond_query import DiamondApplication
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from number_compiler.sequences.collatz.tile_family_hooks import (
    collatz_tile_hooks_for_effect,
)
from tests.support.collatz_diamond_fixtures import build_collatz_diamond_runtime
from tests.support.diamond_query import oracle
from tests.support.diamond_runtime import build


@pytest.mark.parametrize(
    "effect,source",
    [
        (CollatzPhysicalBlockEffect(), (1, 1, 0, 1)),
        (BaseBlockEffect(3), (2, 4, 2)),
    ],
)
def test_point_and_width_never_enter_standalone_context_or_pair_drivers(
    effect: BaseBlockEffect | CollatzPhysicalBlockEffect,
    source: tuple[int, int, int, int] | tuple[int, int, int],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, action = build(
        effect, source, 8, 4, family_hooks=collatz_tile_hooks_for_effect(effect)
    )
    application = DiamondApplication(runtime, action)
    expected = oracle(effect, source, 8, 4)

    def forbidden(*args: object) -> Never:
        raise AssertionError("production entered a separate pair/context driver")

    monkeypatch.setattr(runtime.pair_macros, "summary", forbidden)
    monkeypatch.setattr(runtime.pair_macros, "advance", forbidden)
    monkeypatch.setattr(runtime.pair_macros, "apply_context", forbidden)
    monkeypatch.setattr(runtime.pair_macros.contexts, "execute", forbidden)
    assert [application.point(i) for i in range(8)] == expected
    assert application.active_width() == max(
        (i + 1 for i, symbol in enumerate(expected) if symbol != effect.blank),
        default=0,
    )
    assert runtime.ledger.counters["macro_transfer_evaluations"] > 0
    assert runtime.ledger.counters["context_observation_evaluations"] > 0
    assert runtime.ledger.counters["scheduler_workspace_peak"] > 0


def test_warm_pair_and_context_parents_are_probed_before_any_program_dispatch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, action = build_collatz_diamond_runtime(
        CollatzPhysicalBlockEffect(), (1, 1, 0, 1), 8, 2
    )
    application = DiamondApplication(runtime, action)
    application.point(5)
    arena = runtime.pair_macros
    binding = next(key for key in arena._bindings if runtime.cells.node(key.cell).level)
    pair = PairSummary(binding.action, binding.cell)
    context = next(
        key
        for key in arena.contexts.observations
        if arena.contexts.resolve(key.program).kind == "join"
    )
    assert type(context) is ContextObservation
    expected_pair, expected_context = (
        arena._bindings[binding],
        arena.contexts.observations[context],
    )
    before = runtime.ledger.snapshot()

    def forbidden(*args: object) -> Never:
        raise AssertionError("a warm parent dispatched a descendant")

    monkeypatch.setattr(runtime, "_program", forbidden)
    assert runtime.execute(pair) == expected_pair
    assert runtime.execute(context) == expected_context
    after = runtime.ledger.snapshot()
    assert (after.nodes, after.entries) == (before.nodes, before.entries)
    assert (
        after.counters["macro_transfer_cache_hits"]
        == before.counters["macro_transfer_cache_hits"] + 1
    )
    assert (
        after.counters["context_observation_cache_hits"]
        == before.counters["context_observation_cache_hits"] + 1
    )

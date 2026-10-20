"""Complete primitive transfer functions reuse a parent across bound states."""

from dataclasses import replace
from functools import partial
from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.continuations.diamond_tasks import (
    SpatialSummary,
)
from number_compiler.hashlife.interfaces.diamond_boundary import BoundaryStateID
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from number_compiler.sequences.collatz.tile_family_hooks import (
    collatz_tile_hooks_for_effect,
)
from tests.support.assertions import assert_rejected_atomically
from tests.support.collatz_diamond_fixtures import build_collatz_diamond_runtime
from tests.support.diamond_runtime import build


@pytest.mark.parametrize(
    "effect,source",
    [
        (CollatzPhysicalBlockEffect(), (1, 1, 0, 1)),
        (BaseBlockEffect(3), (2, 4, 1, 2)),
    ],
)
@pytest.mark.parametrize("side", [0, 1])
def test_complete_parent_observes_every_boundary_without_children(
    effect: BaseBlockEffect | CollatzPhysicalBlockEffect,
    source: tuple[int, int, int, int],
    side: int,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, action = build(
        effect, source, 4, 1, family_hooks=collatz_tile_hooks_for_effect(effect)
    )
    cell = runtime.cells.source(0, 2)
    task = SpatialSummary(action, cell, side)
    summary = runtime.execute(task)
    primitive = runtime.kernel(action)
    expected: list[tuple[BoundaryStateID, int]] = []
    for code in range(len(primitive.domain(BoundarySide(side)))):
        state = code
        for symbol in source if side == 0 else reversed(source):
            state = primitive.advance(BoundarySide(side), state, symbol)
        expected.append((runtime.boundaries.literal(action, side, code), state))
    before_bindings = len(runtime.spatial.bindings)
    before_images = sum(
        node.kind == "image" for node in runtime.cells.audit_snapshot().nodes
    )

    def forbidden(*args: object) -> Never:
        raise AssertionError(
            "a warm parametric parent evaluated its source or children"
        )

    monkeypatch.setattr(runtime, "task_program", forbidden)
    monkeypatch.setattr(runtime.cells, "split", forbidden)
    monkeypatch.setattr(runtime.cells, "source_symbol", forbidden)
    assert runtime.execute(task) == summary
    for incoming_state, value in expected:
        result = runtime.spatial.observe(action, side, summary, incoming_state)
        assert runtime.boundaries.state(result).literal == value
    assert len(runtime.spatial.bindings) == before_bindings
    assert (
        sum(node.kind == "image" for node in runtime.cells.audit_snapshot().nodes)
        == before_images
    )


def test_invalid_primitive_summary_scope_rejects_before_warm_lookup() -> None:
    runtime, action = build_collatz_diamond_runtime(
        CollatzPhysicalBlockEffect(), (1, 1), 4, 1
    )
    foreign, other = build_collatz_diamond_runtime(
        CollatzPhysicalBlockEffect(), (1, 1), 4, 1
    )
    request = SpatialSummary(action, runtime.cells.source(0, 2), 0)
    runtime.execute(request)
    for invalid in (
        replace(request, action=other),
        replace(request, cell=foreign.cells.source(0, 2)),
        replace(request, side=True),
    ):
        assert_rejected_atomically(
            runtime.ledger, partial(runtime.execute, invalid), (ValueError, TypeError)
        )

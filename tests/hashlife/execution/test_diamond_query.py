"""Extent observers consume whole diamonds instead of querying output leaves."""

from itertools import product
from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.execution.continuations.diamond_runtime import (
    DiamondRuntime,
)
from number_compiler.hashlife.observation.diamond_observers import NonblankBlockEffect
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from tests.support.diamond_query import build, oracle, bounded_case


def test_nonblank_observer_is_admitted_by_compiler_as_immutable_primitive() -> None:
    compiler = LazyCompiler(ResourceLedger())
    original = NonblankBlockEffect(2, 2)
    admitted = compiler.atom(original)
    assert type(admitted) is NonblankBlockEffect
    assert admitted is not original
    assert compiler.atom(NonblankBlockEffect(2, 2)) is admitted


@pytest.mark.parametrize("steps", [0, 1, 2, 3, 4])
@pytest.mark.parametrize("effect", [CollatzPhysicalBlockEffect(), BaseBlockEffect(3)])
def test_width_uses_observer_diamonds_without_point_queries(
    effect: BaseBlockEffect | CollatzPhysicalBlockEffect,
    steps: int,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    application, expected = bounded_case(effect, steps)

    def forbidden(*args: object) -> Never:
        raise AssertionError("width must not query individual output points")

    monkeypatch.setattr(DiamondRuntime, "point", forbidden)
    for bound in (0, 1, 3, 5, 8):
        width = max(
            (
                i + 1
                for i, symbol in enumerate(expected[:bound])
                if symbol != effect.blank
            ),
            default=0,
        )
        assert application.active_width(bound) == width
    assert application.ledger.counters.get("sequential_generation_advances", 0) == 0
    assert all(row.accounting_delta == 0 for row in application.ledger.inventory())


def test_nonblank_zero_and_truncated_shift_preserve_external_suffix_context(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    effect = CollatzPhysicalBlockEffect()

    def forbidden(*args: object) -> Never:
        raise AssertionError("no leaf point scan")

    monkeypatch.setattr(DiamondRuntime, "point", forbidden)
    for source in product((0, 1), repeat=3):
        application = build(effect, source, 8, 1)
        expected = oracle(effect, source, 8, 1)
        for bound in (1, 2, 3, 8):
            assert application.active_width(bound) == max(
                (
                    i + 1
                    for i, symbol in enumerate(expected[:bound])
                    if symbol != effect.blank
                ),
                default=0,
            )


def test_absorbing_observer_skips_provider_outputs_and_spatial_children(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.hashlife.actions.diamond_actions import ImageCellArena
    from number_compiler.hashlife.execution.continuations.diamond_tasks import (
        Initial,
        Transfer,
    )
    from number_compiler.hashlife.interfaces.diamond_boundary import (
        BoundaryStateID,
        ImageBinding,
    )

    application = build(CollatzPhysicalBlockEffect(), (1, 1, 0, 1, 1), 8, 8)
    runtime = application.runtime
    left = runtime.execute(Initial(application.root, 0))
    right = runtime.execute(Initial(application.root, 1))
    assert type(left) is BoundaryStateID and type(right) is BoundaryStateID
    cell = runtime.cells.source(0, 3)
    provider = ImageBinding(application.root, cell, left, right)
    absorbing = runtime.boundaries.literal(application.observer, 1, 1)
    before = application.ledger.snapshot()

    def forbidden(*args: object) -> Never:
        raise AssertionError("absorbing boundary must skip all provider descendants")

    monkeypatch.setattr(DiamondRuntime, "_output", forbidden)
    monkeypatch.setattr(ImageCellArena, "split", forbidden)
    assert (
        runtime.execute(Transfer(provider, application.observer, absorbing, 1))
        == absorbing
    )
    after = application.ledger.snapshot()
    assert (
        after.counters["nonblank_absorber_hits"]
        == before.counters.get("nonblank_absorber_hits", 0) + 1
    )
    assert after.counters.get("scalar_observation_requests", 0) == before.counters.get(
        "scalar_observation_requests", 0
    )

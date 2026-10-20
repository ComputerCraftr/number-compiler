"""Concrete parent-first primitive transfer memo regressions."""

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.tile_directed_transfer import directed_transfer
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from tests.support.assertions import assert_rejected_atomically
from tests.support.tile_kernel import (
    make_tile_from_symbols,
    make_tile_runtime,
    make_tile_runtime_source,
)


@pytest.mark.parametrize("base", (2, 3, 4, 5, 10))
@pytest.mark.parametrize("side", (0, 1))
def test_directed_transfer_matches_every_finite_state(
    base: int,
    side: int,
) -> None:
    ledger, tiles, adapter, primitive, _scheduler = make_tile_runtime(
        BaseBlockEffect(base)
    )
    blank = tiles.alphabet(adapter.alphabet(primitive)).blank
    symbols = (0, base - 1, blank, 1, blank, 0, blank, blank)
    source = make_tile_from_symbols(tiles, adapter, primitive, symbols)
    law = adapter.primitive_law(primitive)
    count = law.left_count if side == 0 else law.right_count
    scan = symbols if side == 0 else tuple(reversed(symbols))
    try:
        for incoming in range(count):
            expected = incoming
            for symbol in scan:
                expected = law.advance(BoundarySide(side), expected, symbol)
            assert (
                directed_transfer(
                    adapter,
                    primitive,
                    source.tile,
                    side,
                    incoming,
                    adapter.wiring(primitive),
                )
                == expected
            )
        assert ledger.counters.get("tile_directed_transfer_parent_evaluations", 0)
    finally:
        source.close()


def test_warm_parent_transfer_bypasses_kernel_and_descendants(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, _unused_tiles_binding, adapter, primitive, _scheduler, source = (
        make_tile_runtime_source(BaseBlockEffect(3), (0, 1, 2, 3, 4, 5, 0, 1))
    )
    wiring = adapter.wiring(primitive)
    law = adapter.primitive_law(primitive)
    try:
        expected = directed_transfer(adapter, primitive, source.tile, 0, 0, wiring)
        evaluations = ledger.counters.get(
            "tile_directed_transfer_parent_evaluations", 0
        )

        def forbidden(*_args: object) -> Never:
            raise AssertionError("warm directed parent evaluated its primitive law")

        monkeypatch.setattr(type(law), "advance", forbidden)
        assert (
            directed_transfer(adapter, primitive, source.tile, 0, 0, wiring) == expected
        )
        assert (
            ledger.counters.get("tile_directed_transfer_parent_evaluations", 0)
            == evaluations
        )
        assert ledger.counters.get("tile_directed_transfer_early_hits", 0) > 0
    finally:
        source.close()


def test_directed_workspace_releases_frames_after_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _ledger, _unused_tiles_binding, adapter, primitive, scheduler, source = (
        make_tile_runtime_source(BaseBlockEffect(3), (0, 1, 2, 3))
    )
    wiring = adapter.wiring(primitive)
    law = adapter.primitive_law(primitive)

    def forbidden(*_args: object) -> Never:
        raise RuntimeError("injected primitive failure")

    try:
        monkeypatch.setattr(type(law), "advance", forbidden)
        with pytest.raises(RuntimeError, match="injected primitive failure"):
            directed_transfer(adapter, primitive, source.tile, 0, 0, wiring)
        assert len(scheduler.causal_tasks.directed_frames) == 0
        assert len(scheduler.causal_tasks.directed_values) == 0
    finally:
        source.close()


def test_second_scheduler_rejects_before_ledger_mutation() -> None:
    ledger, tiles, adapter, _primitive, scheduler = make_tile_runtime(
        BaseBlockEffect(3)
    )
    assert_rejected_atomically(
        ledger,
        lambda: TileScheduler(tiles, scheduler.results, adapter),
        ValueError,
        match="another scheduler",
    )

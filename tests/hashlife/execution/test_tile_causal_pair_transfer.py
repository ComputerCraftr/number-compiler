"""Finite transfers answer causal dependencies without emitting boundary tiles."""

from __future__ import annotations

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.execution.tile_causal_pair_transfer import (
    finite_pair_transfer,
)
from number_compiler.hashlife.execution.tile_causal_tasks import CausalPrefix
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from tests.arithmetic.contracts.test_tile_causal_private import _scan
from tests.support.tile_kernel import _runtime, _tile


@pytest.mark.parametrize("base", (2, 3, 10))
@pytest.mark.parametrize("side", (0, 1))
@pytest.mark.parametrize("terminal", (False, True))
@pytest.mark.parametrize("width", (3, 4, 7))
def test_pair_transfer_uses_parametric_interfaces_without_output(
    base: int,
    side: int,
    terminal: bool,
    width: int,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, tiles, adapter, before, scheduler = _runtime(BaseBlockEffect(base))
    after = adapter.admit(DigitNormalizeBlockEffect(base)) if terminal else before
    action = adapter.compose(before, after)
    first, second = adapter.primitive_law(before), adapter.primitive_law(after)
    symbols = (0, base - 1, 2 * base - 2, first.blank) * 2
    producer_ports = (min(2, first.left_count - 1), min(1, first.right_count - 1))
    expected_output = _scan(first, symbols[:width], producer_ports)
    incoming = min(1, (second.left_count, second.right_count)[side] - 1)
    expected = incoming
    for symbol in reversed(expected_output) if side else expected_output:
        expected = second.advance(BoundarySide(side), expected, symbol)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("finite transfer constructed a producer boundary output")

    with _tile(tiles, adapter, before, symbols) as source:
        prefix = CausalPrefix(
            action,
            side,
            producer_ports[side],
            incoming,
            BoundaryTileView(source.tile, 0, width, side),
        )
        engine = CausalTileEngine(scheduler)
        monkeypatch.setattr(engine, "output", forbidden)
        monkeypatch.setattr(scheduler, "_complete_direct", forbidden)
        monkeypatch.setattr(tiles, "leaf", forbidden)
        try:
            assert (
                finite_pair_transfer(
                    engine,
                    action,
                    side,
                    prefix,
                    producer_ports[1 - side],
                    incoming,
                )
                == expected
            )
            assert ledger.counters["tile_causal_finite_pair_transfers"] == 1
            assert ledger.counters.get("completed_result_publications", 0) == 0
        finally:
            for lease in reversed(engine._leases):
                lease.close()

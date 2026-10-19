"""Certified blank-output tails stay distinct from causal transfer resets."""

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.hashlife.tiles.tile_ports import BoundPorts
from tests.support.tile_kernel import make_tile_from_symbols, make_tile_runtime


def test_composed_actions_publish_certified_blank_tail_law() -> None:
    _ledger, _tiles, adapter, primitive, _scheduler = make_tile_runtime(
        BaseBlockEffect(3)
    )
    expected = ((1, 1, 0), (2, 2, 1), (4, 4, 3), (8, 8, 7))
    for exponent, left, right in expected:
        record = adapter._action(adapter.power(primitive, exponent))
        assert (
            record.blank_left_tail,
            record.blank_right_tail,
            record.stable_blank_output,
        ) == (left, right, True)


@pytest.mark.parametrize("base", (2, 3, 4, 5, 10))
def test_blank_output_tail_is_not_misused_as_a_right_transfer_reset(base: int) -> None:
    """The certified right output tail is zero, but right state keeps input."""
    _ledger, tiles, adapter, primitive, _scheduler = make_tile_runtime(
        BaseBlockEffect(base)
    )
    alphabet = adapter.alphabet(primitive)
    blank = tiles.alphabet(alphabet).blank
    source = make_tile_from_symbols(tiles, adapter, primitive, (blank,) * 31 + (0,))
    initial = adapter.initial_ports(primitive)
    wiring = adapter.wiring(primitive)
    try:
        full = adapter.transfer_view(
            primitive,
            BoundaryTileView(source.tile, 0, 32),
            BoundPorts(initial, wiring),
            1,
        )
        assert adapter._action(primitive).blank_right_tail == 0
        assert full != initial[1]
    finally:
        source.close()

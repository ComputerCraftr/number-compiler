"""Width's local laws use bounded symbols without constructing future tiles."""

from itertools import product
from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from tests.support.tile_kernel import make_tile_runtime


@pytest.mark.parametrize("effect", (BaseBlockEffect(3), CollatzPhysicalBlockEffect()))
def test_symbol_interface_matches_complete_leaf_law_without_tiles(
    effect: BaseBlockEffect | CollatzPhysicalBlockEffect,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _ledger, tiles, adapter, action, _scheduler = make_tile_runtime(effect)
    kernel = adapter.primitive_law(action)
    wiring = adapter.wiring(action)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("bounded interface law constructed a future tile")

    monkeypatch.setattr(tiles, "leaf", forbidden)
    monkeypatch.setattr(tiles, "join", forbidden)
    for symbol, left, right in product(
        (0, 1, kernel.blank),
        range(kernel.left_count),
        range(kernel.right_count),
    ):
        output, interface, occurrence = adapter.leaf_interface_symbol(
            action,
            symbol,
            (left, right),
            wiring,
        )
        assert output == kernel.emit(left, symbol, right)
        assert adapter.apply_leaf(interface, (left, right)).symbol == output
        assert occurrence.physical_ticks == 0
        assert occurrence.event_weight == int(
            type(effect) is CollatzPhysicalBlockEffect
            and left == adapter.initial_ports(action)[0]
            and symbol == 1
        )
        assert occurrence.frame_shift == 0

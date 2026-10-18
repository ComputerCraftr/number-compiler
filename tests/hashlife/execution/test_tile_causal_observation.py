"""Demanded width dispatch over bounded causal interface tasks."""

from __future__ import annotations

from typing import Never, cast

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.tile_causal_interfaces import (
    CausalInterfacePayload,
)
from number_compiler.hashlife.execution.tile_causal_observation import causal_width
from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
from number_compiler.hashlife.tiles.tiles import TileArena, TileID, TileLease
from number_compiler.resources.ledger import ResourceLedger
from tests.support.tile_kernel import _runtime, _runtime_source, _tile


class _InterfaceEngine:
    def __init__(
        self,
        tiles: TileArena,
        ledger: ResourceLedger,
        interface: LocalInterfaceID,
        *,
        bad_level: bool = False,
    ) -> None:
        self.tiles = tiles
        self.ledger = ledger
        self.interface_id = interface
        self.bad_level = bad_level
        self.interface_calls = 0
        self.child_calls = 0

    def interface(
        self, action: object, tile: TileID, left: object, right: object
    ) -> CausalInterfacePayload:
        self.interface_calls += 1
        node = self.tiles.resolve(tile)
        return CausalInterfacePayload(
            self.interface_id,
            (0, 0),
            (0, 0),
            node.level + int(self.bad_level),
            bool(node.extent),
        )

    def child_states(
        self, action: object, parent: object, left: object, right: object
    ) -> tuple[tuple[object, object], tuple[object, object]]:
        self.child_calls += 1
        return ((left, right), (left, right))

    def point(self, *_args: object, **_kwargs: object) -> Never:
        raise AssertionError("causal width scanned output points")

    def output(self, *_args: object, **_kwargs: object) -> Never:
        raise AssertionError("causal width constructed an output root")


def _activity_fixture() -> tuple[
    TileArena, FieldCellActionID, TileLease, _InterfaceEngine
]:
    effect = BaseBlockEffect(3)
    ledger, tiles, adapter, action, _scheduler = _runtime(effect)
    blank = effect.blank
    source = _tile(tiles, adapter, action, (blank, blank, 1, blank))
    interface = adapter._compile_interface(
        action,
        source.tile,
        adapter.wiring(action),
    )
    engine = _InterfaceEngine(tiles, ledger, interface)
    return tiles, action, source, engine


def test_causal_width_skips_inactive_siblings_without_point_or_output() -> None:
    tiles, action, source, engine = _activity_fixture()
    try:
        assert (
            causal_width(
                engine,
                action,
                source.tile,
                0,
                0,
                limit=4,
            )
            == 3
        )
        assert engine.interface_calls <= 2 * tiles.resolve(source.tile).level
        assert engine.child_calls <= 2
    finally:
        source.close()


def test_causal_width_clips_activity_outside_limit() -> None:
    _unused_tiles_binding, action, source, engine = _activity_fixture()
    try:
        assert (
            causal_width(
                engine,
                action,
                source.tile,
                0,
                0,
                limit=2,
            )
            == 0
        )
    finally:
        source.close()


@pytest.mark.parametrize("bad", (False, True, 1.0, -1, 5))
def test_causal_width_rejects_invalid_limits_before_tasks(
    bad: bool | float,
) -> None:
    effect = BaseBlockEffect(3)
    ledger, tiles, adapter, action, _scheduler, source = _runtime_source(
        effect, (effect.blank,)
    )
    interface = adapter._compile_interface(
        action,
        source.tile,
        adapter.wiring(action),
    )
    engine = _InterfaceEngine(tiles, ledger, interface)
    before = ledger.snapshot()
    try:
        with pytest.raises((TypeError, ValueError)):
            causal_width(engine, action, source.tile, 0, 0, limit=cast("int", bad))
        assert engine.interface_calls == 0
        assert engine.child_calls == 0
        assert ledger.snapshot() == before
    finally:
        source.close()


def test_causal_width_rejects_wrong_interface_level() -> None:
    effect = BaseBlockEffect(3)
    ledger, tiles, adapter, action, _scheduler, source = _runtime_source(effect, (1,))
    interface = adapter._compile_interface(
        action,
        source.tile,
        adapter.wiring(action),
    )
    engine = _InterfaceEngine(tiles, ledger, interface, bad_level=True)
    try:
        with pytest.raises(ValueError, match="spatial level"):
            causal_width(engine, action, source.tile, 0, 0, limit=1)
    finally:
        source.close()

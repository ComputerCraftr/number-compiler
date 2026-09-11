"""Output-independent causal interface payloads for demanded width work."""

from __future__ import annotations

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.execution.tile_causal_interfaces import (
    CausalInterfacePayload,
    combine_causal_interfaces,
    primitive_interface_payload,
)
from number_compiler.hashlife.execution.tile_causal_results import PrimitiveCausalPorts
from number_compiler.hashlife.execution.tile_causal_tasks import CausalFrame
from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from tests.arithmetic.contracts.test_tile_kernel import _oracle, _runtime, _tile


def test_primitive_interface_payload_observes_without_output_tile() -> None:
    effect = BaseBlockEffect(3)
    ledger, tiles, adapter, action, scheduler = _runtime(effect)
    source = _tile(tiles, adapter, action, (1,))
    ports, wiring = adapter.initial_ports(action), adapter.wiring(action)
    before_tiles = ledger.counters.get("tile_publications", 0)
    try:
        payload = primitive_interface_payload(
            scheduler.results,
            action,
            source.tile,
            PrimitiveCausalPorts(*ports),
            wiring,
            TemporalCocycle(),
        )
        expected = _oracle(effect, (1,))[0]
        assert payload.active is (expected != effect.blank)
        assert payload.level == 0
        assert ledger.counters.get("tile_publications", 0) == before_tiles
    finally:
        source.close()


def test_spatial_interface_payload_matches_complete_thirteen_channel_product() -> None:
    effect = BaseBlockEffect(3)
    _ledger, tiles, adapter, action, scheduler = _runtime(effect)
    source = _tile(tiles, adapter, action, (0, 1))
    node = tiles.resolve(source.tile)
    assert node.left is not None and node.right is not None
    ports, wiring = adapter.initial_ports(action), adapter.wiring(action)
    left_context = adapter.child_context(
        action,
        source.tile,
        node.left,
        node.right,
        ports,
        wiring,
        0,
    )
    right_context = adapter.child_context(
        action,
        source.tile,
        node.left,
        node.right,
        ports,
        wiring,
        1,
    )
    try:
        left = primitive_interface_payload(
            scheduler.results,
            action,
            node.left,
            PrimitiveCausalPorts(*left_context.ports),
            wiring,
            TemporalCocycle(),
        )
        right = primitive_interface_payload(
            scheduler.results,
            action,
            node.right,
            PrimitiveCausalPorts(*right_context.ports),
            wiring,
            TemporalCocycle(),
        )
        parent = combine_causal_interfaces(
            scheduler.results,
            action,
            left,
            right,
            wiring,
            expected_level=1,
        )
        assert parent.interface == adapter._compile_interface(
            action,
            source.tile,
            wiring,
        )
        assert parent.incoming_ports == ports
        assert parent.active is any(
            symbol != effect.blank for symbol in _oracle(effect, (0, 1))
        )
    finally:
        source.close()


def test_primitive_parent_interface_reuses_compiled_macro_before_leaf_emit(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    effect = BaseBlockEffect(3)
    ledger, tiles, adapter, action, scheduler = _runtime(effect)
    source = _tile(tiles, adapter, action, (0, 1, 2, 3))
    ports, wiring = adapter.initial_ports(action), adapter.wiring(action)
    adapter._compile_interface(action, source.tile, wiring)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("compiled primitive parent descended to leaf output")

    monkeypatch.setattr(adapter, "leaf_interface_symbol", forbidden)
    application = scheduler.application(action, source.tile, ports, wiring)
    try:
        payload = application.interface()
        assert payload.level == tiles.resolve(source.tile).level
        assert payload.incoming_ports == ports
        assert ledger.counters["tile_causal_interface_primitive_parent_shortcuts"] == 1
    finally:
        application.close()
        source.close()


@pytest.mark.parametrize(
    ("digits", "left_port", "event_weight"),
    (((1, 0, 1, 1), 0, 1), ((0, 1, 1, 1), 0, 0), ((1, 0, 1, 1), 1, 0)),
)
def test_collatz_primitive_parent_observes_only_the_low_edge_event(
    digits: tuple[int, ...], left_port: int, event_weight: int
) -> None:
    effect = CollatzPhysicalBlockEffect()
    ledger, tiles, adapter, action, scheduler = _runtime(effect)
    source = _tile(tiles, adapter, action, digits)
    initial = adapter.initial_ports(action)
    application = scheduler.application(
        action,
        source.tile,
        (left_port, initial[1]),
        adapter.wiring(action),
    )
    try:
        payload = application.interface()
        assert payload.event_weight == event_weight
        assert (
            ledger.counters.get("tile_causal_interface_primitive_parent_shortcuts", 0)
            == 1
        )
    finally:
        application.close()
        source.close()


def test_composite_interface_pins_completed_subresults_to_issued_application() -> None:
    effect = BaseBlockEffect(3)
    _ledger, tiles, adapter, primitive, scheduler = _runtime(effect)
    action = adapter.compose(primitive, primitive)
    source = _tile(tiles, adapter, action, (0, 1))
    ports, wiring = adapter.initial_ports(action), adapter.wiring(action)
    node = tiles.resolve(source.tile)
    assert node.left is not None
    engine = CausalTileEngine(scheduler)
    left, right = engine._initial(action, 0), engine._initial(action, 1)
    left_context, _right_context = engine.child_states(action, source.tile, left, right)
    completed = engine._run(
        CausalFrame("output", (action, node.left, *left_context)),
        tile_result=True,
        return_result=True,
    )
    application = scheduler.application(action, source.tile, ports, wiring)
    try:
        application.interface()
        assert any(binding[0] == application.identity for binding in scheduler._pins)
        completed.close()
        application.interface()
    finally:
        application.close()
        assert not any(
            binding[0] == application.identity for binding in scheduler._pins
        )
        if not completed._closed:
            completed.close()
        source.close()


def test_interface_level_rejects_before_semantic_publication() -> None:
    effect = BaseBlockEffect(3)
    ledger, tiles, adapter, action, scheduler = _runtime(effect)
    source = _tile(tiles, adapter, action, (0, 1))
    node = tiles.resolve(source.tile)
    assert node.left is not None and node.right is not None
    ports, wiring = adapter.initial_ports(action), adapter.wiring(action)
    left = primitive_interface_payload(
        scheduler.results,
        action,
        node.left,
        PrimitiveCausalPorts(*ports),
        wiring,
        TemporalCocycle(),
    )
    right = primitive_interface_payload(
        scheduler.results,
        action,
        node.right,
        PrimitiveCausalPorts(*ports),
        wiring,
        TemporalCocycle(),
    )
    before = ledger.snapshot()
    try:
        with pytest.raises(ValueError, match="spatial level"):
            combine_causal_interfaces(
                scheduler.results,
                action,
                left,
                right,
                wiring,
                expected_level=2,
            )
        after = ledger.snapshot()
        assert after.entries == before.entries
        assert after.nodes == before.nodes
        assert after.inventory == before.inventory
    finally:
        source.close()


def test_collatz_interface_events_are_spatially_additive() -> None:
    effect = CollatzPhysicalBlockEffect()
    _ledger, tiles, adapter, primitive, scheduler = _runtime(effect)
    source = _tile(tiles, adapter, primitive, (1, 1))
    node = tiles.resolve(source.tile)
    assert node.left is not None and node.right is not None
    wiring = adapter.wiring(primitive)
    interface_left = adapter._compile_interface(primitive, node.left, wiring)
    interface_right = adapter._compile_interface(primitive, node.right, wiring)
    ports = adapter.initial_ports(primitive)
    left = CausalInterfacePayload(
        interface_left,
        ports,
        ports,
        0,
        True,
        2,
        1,
    )
    right = CausalInterfacePayload(
        interface_right,
        ports,
        ports,
        0,
        True,
        2,
        1,
    )
    try:
        parent = combine_causal_interfaces(
            scheduler.results,
            adapter.power(primitive, 2),
            left,
            right,
            adapter.wiring(adapter.power(primitive, 2)),
            expected_level=1,
        )
        assert parent.physical_ticks == 2
        assert parent.event_weight == 2
    finally:
        source.close()

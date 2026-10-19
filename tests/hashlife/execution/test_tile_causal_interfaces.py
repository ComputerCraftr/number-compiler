"""Output-independent causal interface payloads for demanded width work."""

from __future__ import annotations

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.causal_frames import (
    OutputFrame,
)
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.execution.tile_causal_interfaces import (
    CausalInterfacePayload,
    combine_causal_interfaces,
    primitive_interface_payload,
)
from number_compiler.hashlife.execution.tile_causal_results import PrimitiveCausalPorts
from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
from number_compiler.hashlife.tiles.tile_results import ResultLease
from number_compiler.resources.ledger import LedgerSnapshot, ResourceLedger
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from tests.support.tile_kernel import (
    literal_tile_output,
    make_tile_from_symbols,
    make_tile_runtime,
    make_tile_runtime_source,
    runtime_source_children,
    runtime_spatial_inputs,
    runtime_tile_inputs,
)


def _assert_no_resource_publication(
    ledger: ResourceLedger,
    before: LedgerSnapshot,
) -> None:
    after = ledger.snapshot()
    assert (after.entries, after.nodes, after.inventory) == (
        before.entries,
        before.nodes,
        before.inventory,
    )


def test_primitive_interface_payload_observes_without_output_tile() -> None:
    effect = BaseBlockEffect(3)
    ledger, _unused_tiles_binding, adapter, action, scheduler, source = (
        make_tile_runtime_source(effect, (1,))
    )
    ports, wiring = adapter.initial_ports(action), adapter.wiring(action)
    law = adapter.primitive_law(action)
    expected_outgoing = (
        law.advance(BoundarySide.LEFT, ports[0], 1),
        law.advance(BoundarySide.RIGHT, ports[1], 1),
    )
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
        expected = literal_tile_output(effect, (1,))[0]
        assert payload.incoming_ports == ports
        assert payload.outgoing_ports == expected_outgoing
        assert payload.active is (expected != effect.blank)
        assert payload.level == 0
        assert ledger.counters.get("tile_publications", 0) == before_tiles
    finally:
        source.close()


def test_primitive_interface_rejects_instance_action_record_override(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    effect = BaseBlockEffect(3)
    ledger, _unused_tiles, adapter, action, scheduler, source = (
        make_tile_runtime_source(effect, (1,))
    )
    ports = adapter.initial_ports(action)
    wiring = adapter.wiring(action)
    callback_calls = 0

    def forbidden_record(_action: FieldCellActionID) -> Never:
        nonlocal callback_calls
        callback_calls += 1
        raise AssertionError("instance action-record override was called")

    monkeypatch.setattr(adapter, "action_record", forbidden_record)
    before = ledger.snapshot()
    try:
        with pytest.raises(ValueError, match="authority record method"):
            primitive_interface_payload(
                scheduler.results,
                action,
                source.tile,
                PrimitiveCausalPorts(*ports),
                wiring,
                TemporalCocycle(),
            )
        assert callback_calls == 0
        _assert_no_resource_publication(ledger, before)
    finally:
        source.close()


@pytest.mark.parametrize(
    ("spoofed_callback", "expected_error"),
    (
        ("action_children", "atomic action"),
        ("action_record", "authority record method"),
    ),
)
def test_primitive_interface_uses_authenticated_composite_sort(
    monkeypatch: pytest.MonkeyPatch,
    spoofed_callback: str,
    expected_error: str,
) -> None:
    effect = BaseBlockEffect(3)
    ledger, _unused_tiles, adapter, primitive, scheduler, source = (
        make_tile_runtime_source(effect, (1,))
    )
    composite = adapter.compose(primitive, primitive)
    assert adapter.action_record(composite).children is not None
    ports = PrimitiveCausalPorts(*adapter.initial_ports(composite))
    wiring = adapter.wiring(composite)

    callback_calls = 0

    def claim_atomic(_action: FieldCellActionID) -> None:
        nonlocal callback_calls
        callback_calls += 1
        return None

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("composite sort check reached compilation or observation")

    # Neither mutable adapter callback may override the authenticated record's
    # actual sort. The class-owned record lookup must reject before execution.
    monkeypatch.setattr(adapter, spoofed_callback, claim_atomic)
    monkeypatch.setattr(adapter, "compile_interface", forbidden)
    monkeypatch.setattr(adapter, "observe", forbidden)
    before = ledger.snapshot()
    try:
        with pytest.raises(ValueError, match=expected_error):
            primitive_interface_payload(
                scheduler.results,
                composite,
                source.tile,
                ports,
                wiring,
                TemporalCocycle(),
            )
        assert callback_calls == 0
        _assert_no_resource_publication(ledger, before)
    finally:
        source.close()


def test_spatial_interface_payload_matches_complete_thirteen_channel_product() -> None:
    effect = BaseBlockEffect(3)
    _ledger, tiles, adapter, action, scheduler, source = make_tile_runtime_source(
        effect, (0, 1)
    )
    (
        _unused_node_binding,
        left_cell,
        right_cell,
        ports,
        wiring,
        left_context,
        right_context,
    ) = runtime_spatial_inputs(tiles, adapter, action, source)
    try:
        left = primitive_interface_payload(
            scheduler.results,
            action,
            left_cell,
            PrimitiveCausalPorts(*left_context.ports),
            wiring,
            TemporalCocycle(),
        )
        right = primitive_interface_payload(
            scheduler.results,
            action,
            right_cell,
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
        assert parent.interface == adapter.compile_interface(
            action,
            source.tile,
            wiring,
        )
        assert parent.incoming_ports == ports
        assert parent.active is any(
            symbol != effect.blank for symbol in literal_tile_output(effect, (0, 1))
        )
    finally:
        source.close()


def test_primitive_parent_interface_reuses_compiled_macro_before_leaf_emit(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    effect = BaseBlockEffect(3)
    ledger, tiles, adapter, action, scheduler, source = make_tile_runtime_source(
        effect, (0, 1, 2, 3)
    )
    ports, wiring = adapter.initial_ports(action), adapter.wiring(action)
    adapter.compile_interface(action, source.tile, wiring)

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
    ledger, _unused_tiles_binding, adapter, action, scheduler, source = (
        make_tile_runtime_source(effect, digits)
    )
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
    _ledger, tiles, adapter, primitive, scheduler = make_tile_runtime(effect)
    action = adapter.compose(primitive, primitive)
    source = make_tile_from_symbols(tiles, adapter, action, (0, 1))
    ports, wiring = adapter.initial_ports(action), adapter.wiring(action)
    node = tiles.resolve(source.tile)
    assert node.left is not None
    engine = CausalTileEngine(scheduler)
    left, right = engine._initial(action, 0), engine._initial(action, 1)
    left_context, _right_context = engine.child_states(action, source.tile, left, right)
    completed = engine._run(
        OutputFrame((action, node.left, *left_context)),
        tile_result=True,
        return_result=True,
    )
    assert type(completed) is ResultLease
    application = scheduler.application(action, source.tile, ports, wiring)
    try:
        application.interface()
        assert any(
            binding[0] == application.identity
            for binding in scheduler.audit_snapshot().pins
        )
        completed.close()
        application.interface()
    finally:
        application.close()
        assert not any(
            binding[0] == application.identity
            for binding in scheduler.audit_snapshot().pins
        )
        if not completed._closed:
            completed.close()
        source.close()


def test_interface_level_rejects_before_semantic_publication() -> None:
    effect = BaseBlockEffect(3)
    ledger, tiles, adapter, action, scheduler, source = make_tile_runtime_source(
        effect, (0, 1)
    )
    _unused_node_binding, left_cell, right_cell, ports, wiring = runtime_tile_inputs(
        tiles, adapter, action, source
    )
    left = primitive_interface_payload(
        scheduler.results,
        action,
        left_cell,
        PrimitiveCausalPorts(*ports),
        wiring,
        TemporalCocycle(),
    )
    right = primitive_interface_payload(
        scheduler.results,
        action,
        right_cell,
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
    _ledger, _unused_tiles_binding, adapter, primitive, scheduler, source, node = (
        runtime_source_children(CollatzPhysicalBlockEffect(), (1, 1))
    )
    assert node.left is not None and node.right is not None
    wiring = adapter.wiring(primitive)
    interface_left = adapter.compile_interface(primitive, node.left, wiring)
    interface_right = adapter.compile_interface(primitive, node.right, wiring)
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

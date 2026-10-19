"""Completed-result ownership for exact causal tile outputs."""

from __future__ import annotations

from dataclasses import replace
from typing import TYPE_CHECKING, cast

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.execution.tile_causal_results import (
    CausalCompletedOutput,
    CompositeCausalPrefixes,
    PrimitiveCausalPorts,
    cached_causal_output,
    causal_result_key,
    combine_causal_outputs,
    lookup_causal_result,
    primitive_causal_semantics,
    publish_causal_completed,
    publish_causal_result,
)
from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileOperands,
    BoundaryTileView,
)
from number_compiler.hashlife.tiles.tile_context import ResultSemantics, TemporalCocycle
from number_compiler.hashlife.tiles.tile_ports import BoundPorts, FusedBoundaryContract
from number_compiler.hashlife.tiles.tiles import TileAlphabet
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from tests.support.assertions import assert_rejected_atomically
from tests.support.tile_kernel import (
    literal_tile_output,
    make_tile_from_symbols,
    make_tile_runtime,
    make_tile_runtime_source,
    read_tile_symbols,
    runtime_source_children,
    runtime_spatial_inputs,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.tiles.tile_results import ResultLease


def test_primitive_causal_output_publishes_complete_reusable_result() -> None:
    effect = BaseBlockEffect(3)
    ledger, tiles, adapter, action, scheduler, source = make_tile_runtime_source(
        effect, (0, 0, 0, 1)
    )
    ports, wiring = adapter.initial_ports(action), adapter.wiring(action)
    key = causal_result_key(
        scheduler.results,
        action,
        source.tile,
        PrimitiveCausalPorts(*ports),
        wiring,
    )
    try:
        engine = CausalTileEngine(scheduler)
        with engine.output(action, source.tile) as output:
            semantics = primitive_causal_semantics(
                scheduler.results,
                action,
                source.tile,
                output.tile,
                PrimitiveCausalPorts(*ports),
                wiring,
                TemporalCocycle(),
            )
            with publish_causal_completed(
                scheduler.results,
                key,
                CausalCompletedOutput(output.tile, semantics),
            ) as published:
                expected = published.result
                assert read_tile_symbols(
                    tiles, published.output
                ) == literal_tile_output(
                    effect,
                    (0, 0, 0, 1),
                )
                assert expected.outgoing_ports == semantics.outgoing_ports
                assert expected.outgoing_boundaries == BoundaryTileOperands()
                before = ledger.counters.get("completed_result_early_hits", 0)
                found = lookup_causal_result(scheduler.results, key)
                assert found is not None
                with found:
                    assert found.result == expected
                assert ledger.counters["completed_result_early_hits"] == before + 1
    finally:
        source.close()


def test_cached_causal_output_rejects_rebound_action_authority(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    effect = BaseBlockEffect(3)
    _, _, adapter, action, scheduler, source = make_tile_runtime_source(
        effect, (0, 0, 0, 1)
    )
    _, _, foreign, _, _ = make_tile_runtime(effect)

    def forbidden_children(*args: object, **kwargs: object) -> None:
        raise AssertionError("a rebound authority must not interpret the cached action")

    monkeypatch.setattr(foreign, "action_children", forbidden_children)
    with (
        source,
        scheduler.complete(
            action, source.tile, adapter.initial_ports(action), adapter.wiring(action)
        ) as result,
    ):
        expected = cached_causal_output(result)
        scheduler.results.action_authority = foreign
        try:
            with pytest.raises(ValueError, match="authority changed after admission"):
                cached_causal_output(result)
        finally:
            scheduler.results.action_authority = adapter
        assert cached_causal_output(result) == expected


def test_result_lease_rejects_same_signature_action_rebinding_and_releases_root() -> (
    None
):
    effect = BaseBlockEffect(3)
    _, _, adapter, action, scheduler, source = make_tile_runtime_source(
        effect, (0, 0, 0, 1)
    )
    with (
        source,
        scheduler.complete(
            action, source.tile, adapter.initial_ports(action), adapter.wiring(action)
        ) as result,
    ):
        original_key = result._key
        original_root = result._tile
        alternate = adapter.power(action, 2)
        assert alternate != action
        assert adapter.signature_for(alternate) == adapter.signature_for(action)

        # Both actions are valid under the same authority and port signature,
        # so semantic validation of the replacement alone cannot authenticate
        # that this result lease was issued for it.
        result._key = replace(original_key, action=alternate)
        with pytest.raises(ValueError, match="binding changed after issuance"):
            cached_causal_output(result)

        # Fail closed while the association is corrupted. The issued root stays
        # pinned until the caller restores the exact binding, then normal close
        # releases it without ever trusting the alternate action.
        with pytest.raises(ValueError, match="binding changed after issuance"):
            result.close()
        assert result._closed is False
        assert original_root._closed is False
        result._key = original_key
        result.close()
        assert result._closed is True
        assert result._tile is original_root
        assert original_root._closed is True


def test_composite_key_encodes_exact_input_prefixes_separately_from_ports() -> None:
    effect = BaseBlockEffect(3)
    _ledger, _unused_tiles_binding, adapter, primitive, scheduler, source = (
        make_tile_runtime_source(effect, (0, 0, 0, 1))
    )
    action = adapter.power(primitive, 4)
    ports, wiring = adapter.initial_ports(action), adapter.wiring(action)
    left = BoundaryTileView(source.tile, 0, 2, 0, 0)
    right = BoundaryTileView(source.tile, 0, 1, 1, 3)
    try:
        first = causal_result_key(
            scheduler.results,
            action,
            source.tile,
            CompositeCausalPrefixes(ports, BoundaryTileOperands(left, right)),
            wiring,
        )
        second = causal_result_key(
            scheduler.results,
            action,
            source.tile,
            CompositeCausalPrefixes(ports, BoundaryTileOperands(left)),
            wiring,
        )
        assert first != second
        assert first.ports == ports
        assert first.boundaries == BoundaryTileOperands(left, right)
        assert lookup_causal_result(scheduler.results, first) is None
    finally:
        source.close()


def test_causal_payload_rejects_conflicting_observed_inputs_before_composition() -> (
    None
):
    ledger, tiles, adapter, action, scheduler = make_tile_runtime(BaseBlockEffect(3))
    with (
        make_tile_from_symbols(tiles, adapter, action, (0,)) as source,
        scheduler.complete(
            action,
            source.tile,
            adapter.initial_ports(action),
            adapter.wiring(action),
        ) as result,
    ):
        value = result.result
        semantics = ResultSemantics(
            value.outgoing,
            value.outgoing_ports,
            observed_input_ports=(0, 0),
        )
        assert_rejected_atomically(
            ledger,
            lambda: CausalCompletedOutput(result.output, semantics, (1, 0)),
            ValueError,
            match="disagree",
        )


@pytest.mark.parametrize("bad", (False, True, 0.0, 1.0))
def test_causal_finite_ports_reject_numeric_aliases_before_arena_work(
    bad: bool | float,
) -> None:
    effect = BaseBlockEffect(3)
    ledger, _unused_tiles_binding, adapter, action, scheduler, source = (
        make_tile_runtime_source(effect, (0,))
    )
    before = ledger.snapshot()
    try:
        with pytest.raises(TypeError, match="exact integers"):
            causal_result_key(
                scheduler.results,
                action,
                source.tile,
                PrimitiveCausalPorts(cast("int", bad), 0),
                adapter.wiring(action),
            )
        after = ledger.snapshot()
        assert after.entries == before.entries
        assert after.nodes == before.nodes
        assert after.inventory == before.inventory
    finally:
        source.close()


def test_outgoing_boundaries_are_validated_in_output_space_before_mutation() -> None:
    effect = BaseBlockEffect(3)
    ledger, tiles, adapter, action, scheduler, source = make_tile_runtime_source(
        effect, (0,)
    )
    ports, wiring = adapter.initial_ports(action), adapter.wiring(action)
    key = causal_result_key(
        scheduler.results,
        action,
        source.tile,
        PrimitiveCausalPorts(*ports),
        wiring,
    )
    interface = adapter.compile_interface(action, source.tile, wiring)
    wrong_alphabet = tiles.intern_alphabet(
        TileAlphabet(
            2,
            0,
            2,
            1,
            "causal-test",
            "causal-test-v1",
        )
    )
    wrong = tiles.leaf(wrong_alphabet, 1)
    try:
        before = ledger.snapshot()
        semantics = ResultSemantics(
            interface,
            ports,
            relative_extent=tiles.resolve(source.tile).extent,
            outgoing_boundaries=BoundaryTileOperands(
                BoundaryTileView(wrong.tile, 0, 1),
            ),
        )
        with pytest.raises(ValueError, match="alphabet"):
            publish_causal_result(
                scheduler.results,
                key,
                source.tile,
                semantics,
            )
        after = ledger.snapshot()
        assert after.entries == before.entries
        assert after.nodes == before.nodes
        assert after.inventory == before.inventory
    finally:
        wrong.close()
        source.close()


def test_causal_boundary_sorts_cannot_alias_across_temporal_depth() -> None:
    effect = BaseBlockEffect(3)
    _ledger, _unused_tiles_binding, adapter, primitive, scheduler, source = (
        make_tile_runtime_source(effect, (0,))
    )
    composite = adapter.power(primitive, 2)
    try:
        with pytest.raises(ValueError, match="composed causal"):
            causal_result_key(
                scheduler.results,
                composite,
                source.tile,
                PrimitiveCausalPorts(*adapter.initial_ports(composite)),
                adapter.wiring(composite),
            )
        with pytest.raises(ValueError, match="primitive causal"):
            causal_result_key(
                scheduler.results,
                primitive,
                source.tile,
                CompositeCausalPrefixes(adapter.initial_ports(primitive)),
                adapter.wiring(primitive),
            )
    finally:
        source.close()


def _payload(
    result: ResultLease,
    incoming_ports: tuple[int, ...],
) -> CausalCompletedOutput:
    value = result.result
    return CausalCompletedOutput(
        result.output,
        ResultSemantics(
            value.outgoing,
            value.outgoing_ports,
            value.physical_ticks,
            value.event_weight,
            value.frame_shift,
            value.relative_origin,
            value.relative_extent,
            value.outgoing_boundaries,
            value.fusion,
        ),
        cast(tuple[int, int], incoming_ports),
    )


def test_spatial_causal_composition_reuses_real_final_stage_interface() -> None:
    effect = BaseBlockEffect(3)
    _ledger, tiles, adapter, action, scheduler, source = make_tile_runtime_source(
        effect, (0, 0, 0, 1)
    )
    (
        _unused_node_binding,
        left_cell,
        right_cell,
        _unused_ports_binding,
        wiring,
        left_context,
        right_context,
    ) = runtime_spatial_inputs(tiles, adapter, action, source)
    left = scheduler.complete(
        action,
        left_cell,
        left_context.ports,
        left_context.wiring,
    )
    right = scheduler.complete(
        action,
        right_cell,
        right_context.ports,
        right_context.wiring,
    )
    try:
        with tiles.join(left.output, right.output) as output:
            right_payload = _payload(right, right_context.ports)
            assert right_payload.incoming_ports is not None
            corrupt = replace(
                right_payload,
                incoming_ports=(
                    right_payload.incoming_ports[0] ^ 1,
                    right_payload.incoming_ports[1],
                ),
            )
            before = scheduler.ledger.snapshot()
            with pytest.raises(ValueError, match="spatial midpoint"):
                combine_causal_outputs(
                    scheduler.results,
                    action,
                    output.tile,
                    _payload(left, left_context.ports),
                    corrupt,
                    wiring,
                )
            rejected = scheduler.ledger.snapshot()
            assert rejected.entries == before.entries
            assert rejected.nodes == before.nodes
            assert rejected.inventory == before.inventory
            combined = combine_causal_outputs(
                scheduler.results,
                action,
                output.tile,
                _payload(left, left_context.ports),
                right_payload,
                wiring,
            )
            expected_interface = adapter.compile_interface(
                action,
                source.tile,
                wiring,
            )
            assert combined.semantics.outgoing == expected_interface
            assert combined.semantics.outgoing_ports == (
                right.result.outgoing_ports[0],
                left.result.outgoing_ports[1],
            )
            assert combined.semantics.outgoing_boundaries.left is not None
            assert combined.semantics.outgoing_boundaries.right is not None
            assert combined.semantics.outgoing_boundaries.left.tile == output.tile
            assert combined.semantics.outgoing_boundaries.right.tile == output.tile
            cached = combine_causal_outputs(
                scheduler.results,
                action,
                output.tile,
                cached_causal_output(left),
                cached_causal_output(right),
                wiring,
            )
            assert cached.output == combined.output
            assert cached.incoming_ports == combined.incoming_ports
            mixed = combine_causal_outputs(
                scheduler.results,
                action,
                output.tile,
                cached_causal_output(left, tiles),
                right_payload,
                wiring,
            )
            assert mixed.incoming_ports == combined.incoming_ports
    finally:
        left.close()
        right.close()
        source.close()


def test_collatz_causal_spatial_events_sum_beyond_one_tick_cap() -> None:
    _ledger, _unused_tiles_binding, adapter, primitive, scheduler, source, node = (
        runtime_source_children(CollatzPhysicalBlockEffect(), (1, 1))
    )
    assert node.left is not None and node.right is not None
    action = adapter.power(primitive, 2)
    wiring = adapter.wiring(action)
    ports = adapter.initial_ports(action)
    left_interface = adapter.compile_interface(
        primitive,
        node.left,
        adapter.wiring(primitive),
    )
    right_interface = adapter.compile_interface(
        primitive,
        node.right,
        adapter.wiring(primitive),
    )
    left = CausalCompletedOutput(
        node.left,
        ResultSemantics(left_interface, ports, 2, 1, relative_extent=1),
        ports,
    )
    right = CausalCompletedOutput(
        node.right,
        ResultSemantics(right_interface, ports, 2, 1, relative_extent=1),
        ports,
    )
    try:
        combined = combine_causal_outputs(
            scheduler.results,
            action,
            source.tile,
            left,
            right,
            wiring,
        )
        assert combined.semantics.physical_ticks == 2
        assert combined.semantics.event_weight == 2
    finally:
        source.close()


def test_spatial_causal_composition_keeps_distinct_producer_and_consumer_tiles() -> (
    None
):
    effect = BaseBlockEffect(3)
    _ledger, tiles, adapter, primitive, scheduler, source = make_tile_runtime_source(
        effect, (0, 1)
    )
    producer_output = make_tile_from_symbols(tiles, adapter, primitive, (1, 0))
    node = tiles.resolve(source.tile)
    producer_node = tiles.resolve(producer_output.tile)
    assert node.left is not None and node.right is not None
    assert producer_node.left is not None and producer_node.right is not None
    action = adapter.power(primitive, 2)
    wiring = adapter.wiring(action)
    left_interface = adapter.compile_interface(primitive, node.left, wiring)
    right_interface = adapter.compile_interface(primitive, node.right, wiring)
    left_consumer, right_consumer = (0, 1), (1, 0)
    left_producer, right_producer = (1, 0), (0, 1)
    left_producer_boundaries = BoundaryTileOperands(
        BoundaryTileView(producer_node.left, 0, 1, 0, 0),
        BoundaryTileView(producer_node.left, 0, 1, 1, 0),
    )
    right_producer_boundaries = BoundaryTileOperands(
        BoundaryTileView(producer_node.right, 0, 1, 0, 0),
        BoundaryTileView(producer_node.right, 0, 1, 1, 0),
    )
    left = CausalCompletedOutput(
        node.left,
        ResultSemantics(
            left_interface,
            left_consumer,
            physical_ticks=2,
            relative_extent=1,
            fusion=FusedBoundaryContract(
                BoundPorts(left_producer, wiring, left_producer_boundaries),
                BoundPorts(left_consumer, wiring),
            ),
        ),
        (0, 0),
    )
    right = CausalCompletedOutput(
        node.right,
        ResultSemantics(
            right_interface,
            right_consumer,
            physical_ticks=2,
            relative_extent=1,
            fusion=FusedBoundaryContract(
                BoundPorts(right_producer, wiring, right_producer_boundaries),
                BoundPorts(right_consumer, wiring),
            ),
        ),
        (0, 0),
    )
    try:
        before = scheduler.ledger.snapshot()
        with pytest.raises(ValueError, match="exact producer output"):
            combine_causal_outputs(
                scheduler.results,
                action,
                source.tile,
                left,
                right,
                wiring,
            )
        rejected = scheduler.ledger.snapshot()
        assert rejected.entries == before.entries
        assert rejected.nodes == before.nodes
        assert rejected.inventory == before.inventory
        combined = combine_causal_outputs(
            scheduler.results,
            action,
            source.tile,
            left,
            right,
            wiring,
            producer_output=producer_output.tile,
        )
        fusion = combined.semantics.fusion
        assert fusion is not None
        assert fusion.producer.ports == (
            right_producer[0],
            left_producer[1],
        )
        assert fusion.consumer.ports == (
            right_consumer[0],
            left_consumer[1],
        )
        assert combined.semantics.outgoing_ports == fusion.consumer.ports
        for bound in (fusion.producer, fusion.consumer):
            assert bound.boundaries.left is not None
            assert bound.boundaries.right is not None
        assert producer_output is not None
        assert fusion.producer.boundaries.left is not None
        assert fusion.producer.boundaries.left.tile == producer_output.tile
        assert producer_output is not None
        assert fusion.producer.boundaries.right is not None
        assert fusion.producer.boundaries.right.tile == producer_output.tile
        assert source is not None
        assert fusion.consumer.boundaries.left is not None
        assert fusion.consumer.boundaries.left.tile == source.tile
        assert source is not None
        assert fusion.consumer.boundaries.right is not None
        assert fusion.consumer.boundaries.right.tile == source.tile
        assert producer_output.tile != source.tile
    finally:
        producer_output.close()
        source.close()

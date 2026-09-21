"""Completed causal siblings opportunistically publish their exact parent."""

from typing import Any, Never

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.execution.tile_causal_tasks import CausalFrame
from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
from number_compiler.hashlife.tiles.tiles import TileID
from tests.arithmetic.contracts.test_tile_kernel import _runtime, _tile


def _skip_promotion(
    _engine: object,
    frame: CausalFrame,
    _frames: object,
    values: list[Any],
) -> bool:
    if frame.op != "promote_midpoint":
        return False
    values.append(False)
    return True


def _symbols(engine: CausalTileEngine, tile: TileID) -> tuple[int, ...]:
    node = engine.tiles.resolve(tile)
    return tuple(engine.tiles.point(tile, index) for index in range(node.width))


def test_completed_p4_children_promote_without_more_output_work(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.hashlife.execution.tile_causal as causal

    causal_module: Any = causal
    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    fourth = adapter.power(primitive, 4)
    eighth = adapter.power(primitive, 8)
    with (
        _tile(tiles, adapter, primitive, (0, 0, 0, 1)) as source,
        scheduler.application(
            eighth,
            source.tile,
            adapter.initial_ports(eighth),
            adapter.wiring(eighth),
        ) as application,
    ):
        original = causal_module.promotion_step
        monkeypatch.setattr(causal_module, "promotion_step", _skip_promotion)
        assert tuple(application.point(index) for index in range(4)) == (2, 4, 0, 2)

        engine = CausalTileEngine(scheduler)
        left = engine._initial(fourth, 0)
        right = engine._initial(fourth, 1)
        parent_key = engine._composite_key(fourth, source.tile, left, right)
        assert isinstance(parent_key, PoweredResultKey)
        assert scheduler.results.lookup(parent_key) is None

        source_node = tiles.resolve(source.tile)
        assert source_node.left is not None and source_node.right is not None
        left_context, right_context = engine.child_states(
            fourth,
            source.tile,
            left,
            right,
        )
        left_key = engine._composite_key(
            fourth,
            source_node.left,
            *left_context,
        )
        right_key = engine._composite_key(
            fourth,
            source_node.right,
            *right_context,
        )
        assert isinstance(left_key, PoweredResultKey)
        assert isinstance(right_key, PoweredResultKey)
        left_result = scheduler.results.lookup(left_key)
        right_result = scheduler.results.lookup(right_key)
        assert left_result is not None and right_result is not None
        try:
            assert left_result.result.observed_input_ports == (0, 1)
            assert left_result.result.outgoing_ports == (1, 1)
            assert right_result.result.observed_input_ports == (1, 0)
            assert right_result.result.outgoing_ports == (3, 1)
        finally:
            left_result.close()
            right_result.close()

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("parent promotion constructed another exact output")

        monkeypatch.setattr(causal_module, "promotion_step", original)
        monkeypatch.setattr(adapter, "primitive_law", forbidden)
        monkeypatch.setattr(adapter, "leaf_interface", forbidden)
        monkeypatch.setattr(adapter, "leaf_interface_symbol", forbidden)
        before_emits = ledger.counters.get("tile_causal_primitive_emits", 0)
        before_boundaries = ledger.counters.get(
            "tile_causal_boundary_output_evaluations",
            0,
        )
        engine._application = application.identity
        promoted = engine._run(
            CausalFrame(
                "promote_midpoint",
                (
                    eighth,
                    source.tile,
                    engine._initial(eighth, 0),
                    engine._initial(eighth, 1),
                ),
            ),
            tile_result=False,
        )
        assert promoted is True
        parent = scheduler.results.lookup(parent_key)
        assert parent is not None
        try:
            assert _symbols(engine, parent.output) == (2, 0, 0, 4)
        finally:
            parent.close()
        assert ledger.counters.get("tile_causal_primitive_emits", 0) == before_emits
        assert (
            ledger.counters.get("tile_causal_boundary_output_evaluations", 0)
            == before_boundaries
        )

        # A retained parent remains reusable when one independently evicted
        # child can no longer satisfy the speculative promotion fallback.
        parent_guard = scheduler.results.lookup(parent_key)
        assert parent_guard is not None
        try:
            scheduler._release_pins(application.identity)
            scheduler.results._remove_key(left_key)
            assert left_key not in scheduler.results._memo
            retained_parent = scheduler.results.lookup(parent_key)
            assert retained_parent is not None
            retained_parent.close()

            monkeypatch.setattr(engine, "_append_prefix", forbidden)
            before_hits = ledger.counters.get("tile_causal_parent_promotion_hits", 0)
            engine._application = application.identity
            assert (
                engine._run(
                    CausalFrame(
                        "promote_midpoint",
                        (
                            eighth,
                            source.tile,
                            engine._initial(eighth, 0),
                            engine._initial(eighth, 1),
                        ),
                    ),
                    tile_result=False,
                )
                is True
            )
            assert ledger.counters["tile_causal_parent_promotion_hits"] > before_hits
        finally:
            parent_guard.close()


def test_cold_parent_promotion_declines_before_constructing_child_contexts(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.hashlife.execution.tile_causal_promotion as promotion

    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    eighth = adapter.power(primitive, 8)
    with (
        _tile(tiles, adapter, primitive, (0, 0, 0, 1)) as source,
        scheduler.application(
            eighth,
            source.tile,
            adapter.initial_ports(eighth),
            adapter.wiring(eighth),
        ) as application,
    ):
        engine = CausalTileEngine(scheduler)
        root = CausalFrame(
            "promote_midpoint",
            (
                eighth,
                source.tile,
                engine._initial(eighth, 0),
                engine._initial(eighth, 1),
            ),
        )

        def forbidden_frame(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("cold promotion constructed a child context")

        monkeypatch.setattr(promotion, "CausalFrame", forbidden_frame)
        engine._application = application.identity
        assert engine._run(root, tile_result=False) is False
        assert ledger.counters["tile_causal_parent_promotion_preflight_misses"] == 1
        assert ledger.counters.get("tile_causal_parent_promotion_misses", 0) == 0


def test_promoted_p4_parent_reduces_later_p8_completion_frames(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.hashlife.execution.tile_causal as causal

    causal_module: Any = causal

    def run(*, promote: bool) -> tuple[int, int]:
        ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
        eighth = adapter.power(primitive, 8)
        with (
            _tile(tiles, adapter, primitive, (0, 0, 0, 1)) as source,
            scheduler.application(
                eighth,
                source.tile,
                adapter.initial_ports(eighth),
                adapter.wiring(eighth),
            ) as application,
        ):
            if not promote:
                monkeypatch.setattr(causal_module, "promotion_step", _skip_promotion)
            for coordinate in range(4):
                application.point(coordinate)
            before_frames = ledger.counters.get("tile_causal_frames", 0)
            before_compositions = ledger.counters.get(
                "tile_temporal_complete_compositions",
                0,
            )
            application.complete()
            return (
                ledger.counters.get("tile_causal_frames", 0) - before_frames,
                ledger.counters.get("tile_temporal_complete_compositions", 0)
                - before_compositions,
            )

    original = causal_module.promotion_step
    baseline = run(promote=False)
    monkeypatch.setattr(causal_module, "promotion_step", original)
    promoted = run(promote=True)
    assert promoted[0] < baseline[0]
    assert promoted[1] < baseline[1]

"""A completed required dyadic boundary is consumed before producer scans."""

from collections.abc import Callable
from dataclasses import replace
from typing import Never, cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.execution.tile_causal_tasks import (
    CausalFrame,
    primitive_advance,
)
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.hashlife.tiles.tiles import TileArena, TileID
from number_compiler.resources.ledger import ResourceLedger
from tests.support.tile_kernel import _runtime, _tile


def _warm_boundary(
    request: Callable[[], BoundaryTileView], tiles: TileArena, ledger: ResourceLedger
) -> tuple[BoundaryTileView, tuple[int, ...], dict[str, int]]:
    view = request()
    symbols = tuple(tiles.point(view.tile, index) for index in range(4))
    return view, symbols, dict(ledger.counters)


def _same_boundary(
    request: Callable[[], BoundaryTileView], tiles: TileArena, expected: tuple[int, ...]
) -> BoundaryTileView:
    view = request()
    assert tuple(tiles.point(view.tile, index) for index in range(4)) == expected
    return view


@pytest.mark.parametrize("side", (0, 1))
def test_cold_literal_transition_does_not_construct_a_tile(
    monkeypatch: pytest.MonkeyPatch, side: int
) -> None:
    ledger, tiles, adapter, action, scheduler = _runtime(BaseBlockEffect(3))
    law = adapter.primitive_law(action)
    count = law.right_count if side else law.left_count
    expected = {
        (state, symbol): law.advance(BoundarySide(side), state, symbol)
        for state in range(count)
        for symbol in range(law.blank + 1)
    }

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("finite transition constructed a tile or interface")

    monkeypatch.setattr(tiles, "leaf", forbidden)
    monkeypatch.setattr(adapter, "_compile_interface", forbidden)
    engine = CausalTileEngine(scheduler)
    for (state, symbol), outgoing in expected.items():
        assert (
            engine._run(
                CausalFrame("advance_symbol", (action, side, state, symbol)),
                tile_result=False,
            )
            == outgoing
        )
    assert ledger.counters["tile_causal_direct_symbol_transfers"] == len(expected)


@pytest.mark.parametrize("side", (0, 1))
def test_parametric_parent_transfer_serves_all_states_before_descending(
    monkeypatch: pytest.MonkeyPatch, side: int
) -> None:
    ledger, tiles, adapter, action, _ = _runtime(BaseBlockEffect(3))
    law = adapter.primitive_law(action)
    symbols = (0, 2, 3, 4)
    count = law.right_count if side else law.left_count
    expected = []
    for incoming in range(count):
        state = incoming
        for symbol in reversed(symbols) if side else symbols:
            state = law.advance(BoundarySide(side), state, symbol)
        expected.append(state)
    with _tile(tiles, adapter, action, symbols) as source:
        adapter._compile_interface(action, source.tile, adapter.wiring(action))
        view = BoundaryTileView(source.tile, 0, 4, side)

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("parametric parent replayed a primitive transition")

        monkeypatch.setattr(type(law), "advance", forbidden)
        for incoming, outgoing in enumerate(expected):
            assert primitive_advance(adapter, action, side, incoming, view) == outgoing
        assert ledger.counters["tile_directed_transfer_interface_hits"] == count
        assert ledger.counters.get("tile_directed_transfer_leaf_evaluations", 0) == 0
        assert ledger.counters.get("tile_directed_transfer_parent_evaluations", 0) == 0


@pytest.mark.parametrize("side", (0, 1))
def test_primitive_parent_goes_directly_to_validated_transfer_memo(
    monkeypatch: pytest.MonkeyPatch,
    side: int,
) -> None:
    ledger, tiles, adapter, action, _ = _runtime(BaseBlockEffect(3))
    symbols = (0, 2, 3, 4)
    law = adapter.primitive_law(action)
    incoming = adapter.initial_ports(action)[side]
    expected = incoming
    for symbol in symbols if not side else reversed(symbols):
        expected = law.advance(BoundarySide(side), expected, symbol)
    with _tile(tiles, adapter, action, symbols) as source:
        view = BoundaryTileView(source.tile, 0, 4, side)

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("complete parent entered clipped-region traversal")

        monkeypatch.setattr(adapter, "transfer_view", forbidden)
        assert primitive_advance(adapter, action, side, incoming, view) == expected
        before = ledger.counters.get("tile_directed_transfer_leaf_evaluations", 0)
        monkeypatch.setattr(type(law), "advance", forbidden)
        assert primitive_advance(adapter, action, side, incoming, view) == expected
        assert (
            ledger.counters.get("tile_directed_transfer_leaf_evaluations", 0) == before
        )
        assert ledger.counters["tile_causal_direct_parent_transfers"] == 2
        assert ledger.counters.get("tile_boundary_transfer_frames", 0) == 0


@pytest.mark.parametrize("invalid", (True, 0.0))
def test_direct_parent_rejects_numeric_state_alias_before_warm_hit(
    invalid: object,
) -> None:
    ledger, tiles, adapter, action, _ = _runtime(BaseBlockEffect(3))
    with _tile(tiles, adapter, action, (0, 1, 2, 3)) as source:
        view = BoundaryTileView(source.tile, 0, 4)
        primitive_advance(adapter, action, 0, 0, view)
        before = ledger.snapshot()
        with pytest.raises((TypeError, ValueError)):
            primitive_advance(adapter, action, 0, cast(int, invalid), view)
        after = ledger.snapshot()
        assert (after.entries, after.nodes) == (before.entries, before.nodes)


def test_direct_parent_warm_hit_revalidates_action_metadata() -> None:
    ledger, tiles, adapter, action, _ = _runtime(BaseBlockEffect(3))
    with _tile(tiles, adapter, action, (0, 1, 2, 3)) as source:
        view = BoundaryTileView(source.tile, 0, 4)
        primitive_advance(adapter, action, 0, 0, view)
        record = adapter._actions[action.local_id]
        adapter._actions[action.local_id] = replace(record, repetitions=2)
        before = ledger.snapshot()
        try:
            with pytest.raises(ValueError, match="inconsistent metadata"):
                primitive_advance(adapter, action, 0, 0, view)
            after = ledger.snapshot()
            assert (after.entries, after.nodes) == (before.entries, before.nodes)
        finally:
            adapter._actions[action.local_id] = record


def test_direct_parent_keeps_concrete_opposite_port_admission(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _ledger, tiles, adapter, action, scheduler = _runtime(BaseBlockEffect(3))
    with _tile(tiles, adapter, action, (0, 1, 2, 3)) as source:
        view = BoundaryTileView(source.tile, 0, 4)
        primitive_advance(adapter, action, 0, 0, view)

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise ValueError("injected opposite-port admission failure")

        monkeypatch.setattr(type(scheduler.results), "_validate_ports", forbidden)
        with pytest.raises(ValueError, match="opposite-port"):
            primitive_advance(adapter, action, 0, 0, view)


def test_transfer_task_identity_ignores_nonsemantic_relative_origin(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.hashlife.execution.tile_causal as causal

    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    with _tile(tiles, adapter, primitive, (0, 1, 2, 3)) as source:
        engine = CausalTileEngine(scheduler)
        engine._hold_workspace = True

        def advance(origin: int) -> object:
            return engine._run(
                CausalFrame(
                    "advance",
                    (
                        primitive,
                        0,
                        engine._initial(primitive, 0),
                        BoundaryTileView(source.tile, origin, 4),
                    ),
                ),
                tile_result=False,
            )

        try:
            expected = advance(17)
            evaluations = ledger.counters["tile_causal_advance_evaluations"]

            def forbidden(*_args: object, **_kwargs: object) -> Never:
                raise AssertionError("relative origin alias repeated a transfer")

            monkeypatch.setattr(causal, "primitive_advance", forbidden)
            assert advance(-23) == expected
            assert ledger.counters["tile_causal_advance_evaluations"] == evaluations
            assert ledger.counters["tile_causal_advance_hits"] >= 1
        finally:
            engine._hold_workspace = False
            engine._release_workspace()


@pytest.mark.parametrize("alias", (False, 0.0, True, 1.0))
def test_transfer_origin_numeric_alias_rejects_before_warm_memo_hit(
    alias: object,
) -> None:
    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    with _tile(tiles, adapter, primitive, (0, 1)) as source:
        engine = CausalTileEngine(scheduler)
        engine._hold_workspace = True
        valid = BoundaryTileView(source.tile, 0, 2)
        try:
            engine._run(
                CausalFrame(
                    "advance",
                    (primitive, 0, engine._initial(primitive, 0), valid),
                ),
                tile_result=False,
            )
            hits = ledger.counters.get("tile_causal_advance_hits", 0)
            evaluations = ledger.counters["tile_causal_advance_evaluations"]
            forged = BoundaryTileView(source.tile, 0, 2)
            object.__setattr__(forged, "relative_origin", alias)
            with pytest.raises(TypeError, match="origin"):
                engine._run(
                    CausalFrame(
                        "advance",
                        (primitive, 0, engine._initial(primitive, 0), forged),
                    ),
                    tile_result=False,
                )
            assert ledger.counters.get("tile_causal_advance_hits", 0) == hits
            assert ledger.counters["tile_causal_advance_evaluations"] == evaluations
        finally:
            engine._hold_workspace = False
            engine._release_workspace()


@pytest.mark.parametrize("exponent", (4, 8))
def test_repeated_boundary_hits_completed_region_before_descendants(
    monkeypatch: pytest.MonkeyPatch, exponent: int
) -> None:
    import number_compiler.hashlife.execution.tile_causal as causal

    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    action = adapter.power(primitive, exponent)
    with (
        _tile(tiles, adapter, primitive, (0, 0, 0, 1)) as source,
        scheduler.application(
            action,
            source.tile,
            adapter.initial_ports(action),
            adapter.wiring(action),
        ) as application,
    ):
        engine = CausalTileEngine(scheduler)

        def request() -> BoundaryTileView:
            engine._application = application.identity
            result: object = engine._run(
                CausalFrame(
                    "output_boundary",
                    (
                        action,
                        0,
                        BoundaryTileView(source.tile, 0, 4),
                        engine._initial(action, 0),
                        engine._initial(action, 1),
                    ),
                ),
                tile_result=False,
            )
            assert isinstance(result, BoundaryTileView)
            return result

        first, expected, before = _warm_boundary(request, tiles, ledger)

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError(
                "completed causal boundary executed producer descendants"
            )

        monkeypatch.setattr(causal, "boundary_step", forbidden)
        monkeypatch.setattr(adapter, "leaf_interface_symbol", forbidden)
        monkeypatch.setattr(tiles, "leaf", forbidden)
        monkeypatch.setattr(tiles, "join", forbidden)
        second = _same_boundary(request, tiles, expected)
        assert second.tile == first.tile
        assert ledger.counters["tile_causal_boundary_output_hits"] > before.get(
            "tile_causal_boundary_output_hits", 0
        )
        assert (
            ledger.counters["tile_causal_boundary_output_evaluations"]
            == before["tile_causal_boundary_output_evaluations"]
        )
        assert application._root is None


def test_clipped_equal_regions_normalize_before_transient_task_lookup(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Backing occurrence identity cannot split one exact causal dependency."""
    import number_compiler.hashlife.execution.tile_causal as causal

    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    action = adapter.power(primitive, 4)
    first_symbols = (4, 4, 0, 1, 2, 4, 4, 4)
    second_symbols = (4, 0, 1, 2, 4, 3, 3, 3)
    with (
        _tile(tiles, adapter, primitive, first_symbols) as first,
        _tile(tiles, adapter, primitive, second_symbols) as second,
    ):
        engine = CausalTileEngine(scheduler)
        engine._hold_workspace = True

        def request(tile: TileID, offset: int) -> BoundaryTileView:
            result: object = engine._run(
                CausalFrame(
                    "output_boundary",
                    (
                        action,
                        0,
                        BoundaryTileView(tile, -7, 3, 0, offset),
                        engine._initial(action, 0),
                        engine._initial(action, 1),
                    ),
                ),
                tile_result=False,
            )
            assert isinstance(result, BoundaryTileView)
            return result

        try:
            expected = request(first.tile, 2)
            evaluations = ledger.counters["tile_causal_boundary_output_evaluations"]
            publications = ledger.counters.get("tile_publications", 0)

            def forbidden(*_args: object, **_kwargs: object) -> Never:
                raise AssertionError(
                    "normalized causal alias traversed producer descendants"
                )

            monkeypatch.setattr(causal, "boundary_step", forbidden)
            actual = request(second.tile, 1)
            assert actual.tile == expected.tile
            assert (
                ledger.counters["tile_causal_boundary_output_evaluations"]
                == evaluations
            )
            assert ledger.counters.get("tile_publications", 0) == publications
            assert ledger.counters["tile_causal_task_memo_hits"] >= 1
            assert ledger.counters["tile_boundary_region_normalization_aliases"] >= 2
        finally:
            engine._hold_workspace = False
            engine._release_workspace()


def test_clipped_region_memo_hits_before_cross_observation_construction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A released task workspace still reuses its application-pinned clip."""
    import number_compiler.hashlife.tiles.tile_boundary_concat_memo as boundary_runtime
    import number_compiler.hashlife.tiles.tile_region_memo as region_memo

    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    action = adapter.power(primitive, 4)
    with (
        _tile(
            tiles,
            adapter,
            primitive,
            (4, 4, 0, 1, 2, 3, 4, 4),
        ) as source,
        scheduler.application(
            action,
            source.tile,
            adapter.initial_ports(action),
            adapter.wiring(action),
        ) as application,
    ):
        engine = CausalTileEngine(scheduler)

        def request() -> BoundaryTileView:
            engine._application = application.identity
            result: object = engine._run(
                CausalFrame(
                    "output_boundary",
                    (
                        action,
                        0,
                        BoundaryTileView(source.tile, -9, 4, 0, 2),
                        engine._initial(action, 0),
                        engine._initial(action, 1),
                    ),
                ),
                tile_result=False,
            )
            assert isinstance(result, BoundaryTileView)
            return result

        _unused_expected_binding, expected_symbols, before = _warm_boundary(
            request, tiles, ledger
        )

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("warm clipped boundary rebuilt spatial content")

        monkeypatch.setattr(region_memo, "normalize_boundary_view", forbidden)
        monkeypatch.setattr(boundary_runtime, "concat_boundary_views", forbidden)
        monkeypatch.setattr(tiles, "join", forbidden)
        _same_boundary(request, tiles, expected_symbols)
        assert ledger.counters["tile_region_normalization_early_hits"] > before.get(
            "tile_region_normalization_early_hits",
            0,
        )
        assert (
            ledger.counters["tile_causal_boundary_output_evaluations"]
            == before["tile_causal_boundary_output_evaluations"]
        )

"""Point demand consumes a completed spatial child before visiting its leaves."""

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.execution.tile_causal_interface_step import interface_step
from number_compiler.hashlife.execution.tile_causal_tasks import CausalFrame
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.hashlife.tiles.tile_results import ResultLease
from number_compiler.resources.causal_workspace import CausalFrameStack, CausalResults
from tests.support.tile_kernel import _runtime, _tile


def test_point_reuses_completed_interior_parent(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    fourth = adapter.power(primitive, 4)
    with (
        _tile(tiles, adapter, primitive, (0, 0, 0, 1)) as source,
        scheduler.application(
            fourth,
            source.tile,
            adapter.initial_ports(fourth),
            adapter.wiring(fourth),
        ) as application,
    ):
        engine = CausalTileEngine(scheduler)
        engine._application = application.identity
        engine._hold_workspace = True
        left, right = engine._initial(fourth, 0), engine._initial(fourth, 1)
        contexts = engine.child_states(fourth, source.tile, left, right)
        child = tiles.resolve(source.tile).left
        assert child is not None
        completed = engine._run(
            CausalFrame("output", (fourth, child, *contexts[0])),
            tile_result=True,
            return_result=True,
        )
        assert isinstance(completed, ResultLease)
        engine._hold_workspace = False
        engine._release_workspace()
        with completed:
            expected = tiles.point(completed.output, 0)

            def forbidden(*_args: object, **_kwargs: object) -> Never:
                raise AssertionError("point revisited a completed child's leaves")

            monkeypatch.setattr(adapter, "leaf_interface", forbidden)
            monkeypatch.setattr(adapter, "leaf_interface_symbol", forbidden)
            before_hits = ledger.counters.get("tile_causal_point_parent_hits", 0)
            before_descents = ledger.counters.get(
                "tile_causal_point_demanded_descents", 0
            )
            assert application.point(0) == expected == 2
            assert ledger.counters["tile_causal_point_parent_hits"] == before_hits + 1
            assert (
                ledger.counters["tile_causal_point_demanded_descents"]
                == before_descents + 1
            )


@pytest.mark.parametrize("side", (0, 1))
def test_selected_child_context_matches_full_parent_context(
    monkeypatch: pytest.MonkeyPatch,
    side: int,
) -> None:
    _ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    action = adapter.power(primitive, 4)
    with _tile(tiles, adapter, primitive, (0, 0, 0, 1)) as source:
        engine = CausalTileEngine(scheduler)
        engine._hold_workspace = True
        try:
            left, right = engine._initial(action, 0), engine._initial(action, 1)
            contexts = engine.child_states(action, source.tile, left, right)
            parent = tiles.resolve(source.tile)
            child = parent.right if side else parent.left
            assert child is not None
            completed = engine._run(
                CausalFrame("output", (action, child, *contexts[side])),
                tile_result=True,
                return_result=True,
            )
            assert isinstance(completed, ResultLease)
            with completed:
                coordinate = side * (parent.width // 2)
                expected = tiles.point(completed.output, 0)

                def forbidden(*_args: object, **_kwargs: object) -> Never:
                    raise AssertionError(
                        "selected context differed from the full oracle"
                    )

                monkeypatch.setattr(adapter, "leaf_interface", forbidden)
                monkeypatch.setattr(adapter, "leaf_interface_symbol", forbidden)
                assert engine.point(action, source.tile, coordinate) == expected
        finally:
            engine._hold_workspace = False
            engine._release_workspace()


@pytest.mark.parametrize("side", (0, 1))
def test_point_does_not_construct_unselected_child_context(
    monkeypatch: pytest.MonkeyPatch,
    side: int,
) -> None:
    import number_compiler.hashlife.execution.tile_causal as causal

    _ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    action = adapter.power(primitive, 4)
    with _tile(tiles, adapter, primitive, (0, 0, 0, 1)) as source:
        engine = CausalTileEngine(scheduler)
        parent = tiles.resolve(source.tile)
        selected = parent.right if side else parent.left
        sibling = parent.left if side else parent.right
        assert selected is not None and sibling is not None and selected != sibling
        original = interface_step

        def guarded(
            active_engine: CausalTileEngine,
            frame: CausalFrame,
            frames: CausalFrameStack,
            values: CausalResults,
        ) -> bool:
            if frame.op == "advance":
                frame_action, direction, _state, view = frame.args
                if (
                    frame_action == action
                    and direction == side
                    and type(view) is BoundaryTileView
                    and view.tile == selected
                ):
                    raise AssertionError("point requested the unselected child context")
            return original(active_engine, frame, frames, values)

        monkeypatch.setattr(causal, "interface_step", guarded)
        coordinate = side * (parent.width // 2)
        assert type(engine.point(action, source.tile, coordinate)) is int

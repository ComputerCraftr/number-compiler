"""Point demand consumes a completed spatial child before visiting its leaves."""

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.execution.tile_causal_tasks import CausalFrame
from number_compiler.hashlife.tiles.tile_results import ResultLease
from tests.arithmetic.contracts.test_tile_kernel import _runtime, _tile


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

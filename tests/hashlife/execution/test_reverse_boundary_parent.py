"""A single reverse interval needs its interface, not two unused exit scans."""

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.hashlife.execution.causal_frames import (
    CausalTaskFrame,
    OutputBoundaryFrame,
    OutputChunkListFrame,
    ReverseBoundaryFrame,
    ScanChunksFrame,
)
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.execution.tile_causal_boundary_step import boundary_step
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.resources.causal_stacks import CausalFrameStack, CausalResults
from number_compiler.resources.causal_types import CausalTaskValue
from tests.arithmetic.contracts.test_tile_causal_private import _scan
from tests.support.tile_kernel import make_tile_from_symbols, make_tile_runtime


@pytest.mark.parametrize("exponent", (1, 2, 4))
@pytest.mark.parametrize("side", (0, 1))
@pytest.mark.parametrize("operation", ("reverse_boundary", "output_boundary"))
@pytest.mark.parametrize("noninitial", (False, True))
def test_single_reverse_boundary_uses_original_exteriors_without_scans(
    monkeypatch: pytest.MonkeyPatch,
    exponent: int,
    side: int,
    operation: str,
    noninitial: bool,
) -> None:
    import number_compiler.hashlife.execution.tile_causal as causal

    ledger, tiles, adapter, primitive, scheduler = make_tile_runtime(BaseBlockEffect(3))
    action = adapter.power(primitive, exponent)
    symbols = (0, 0, 0, 1)
    ports = (1, 2) if noninitial else adapter.initial_ports(primitive)
    produced: tuple[int, ...] = symbols
    for index in range(exponent):
        produced = _scan(
            adapter.primitive_law(primitive),
            produced,
            ports if index == exponent - 1 else adapter.initial_ports(primitive),
        )
    expected = ReverseBoundOutput.leaf(3, produced[0])
    for symbol in produced[1:]:
        expected = expected.then(ReverseBoundOutput.leaf(3, symbol), ledger)

    def guarded(
        engine: CausalTileEngine,
        frame: CausalTaskFrame,
        frames: CausalFrameStack[CausalTaskFrame],
        values: CausalResults[CausalTaskValue],
    ) -> bool:
        if isinstance(frame, ScanChunksFrame) and frame.args[0] == action:
            raise AssertionError("single interval computed unused producer exits")
        if not isinstance(
            frame, (OutputBoundaryFrame, OutputChunkListFrame, ScanChunksFrame)
        ):
            return False
        return boundary_step(engine, frame, frames, values)

    monkeypatch.setattr(causal, "boundary_step", guarded)
    with make_tile_from_symbols(tiles, adapter, primitive, symbols) as source:
        engine = CausalTileEngine(scheduler)
        engine._hold_workspace = True
        try:
            arguments = (
                action,
                side,
                BoundaryTileView(source.tile, 0, 4, side),
                engine._initial(action, side, ports[side]),
                engine._initial(action, 1 - side, ports[1 - side]),
            )
            request = (
                ReverseBoundaryFrame(arguments)
                if operation == "reverse_boundary"
                else OutputBoundaryFrame(arguments)
            )
            actual = engine._run(
                request,
                tile_result=False,
            )
            if operation == "reverse_boundary":
                assert actual == expected
                assert ledger.counters["reverse_boundary_single_tile_transfers"] > 0
            else:
                assert isinstance(actual, BoundaryTileView)
                assert tuple(tiles.point(actual.tile, i) for i in range(4)) == (
                    tuple(reversed(produced)) if side else produced
                )
                assert ledger.counters["tile_causal_boundary_single_tile_outputs"] > 0
        finally:
            engine._hold_workspace = False
            engine._release_workspace()

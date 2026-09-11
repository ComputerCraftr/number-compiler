"""Bounded audit reproductions; no production edits or replacement algorithms."""

import json
from unittest.mock import patch

from number_compiler.api.number_api import PoweredCollatzTermPayload
from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.execution.tile_causal_tasks import (
    CausalFrame,
    CausalPrefix,
)
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from tests.arithmetic.contracts.test_tile_causal_private import _scan
from tests.arithmetic.contracts.test_tile_kernel import _runtime, _tile


def radix_cases() -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for seed in (1, 2, 63, 64, 82):
        for index in range(2):
            term = PoweredCollatzTerm(seed, 0)
            expected: object = (
                (seed // 64**index) % 64 if seed >= 64**index else "IndexError"
            )
            try:
                actual: object = PoweredCollatzTermPayload(term, 64).digit(index)
            except IndexError as error:
                actual = f"IndexError: {error}"
            rows.append(
                {
                    "seed": seed,
                    "index": index,
                    "expected": expected,
                    "actual": actual,
                    "maximum_width": term.maximum_width,
                }
            )
    return rows


def dead_setup_cases() -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for side in (0, 1):
        ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(10))
        action = adapter.compose(primitive, primitive)
        law = adapter.primitive_law(primitive)
        symbols, ports = (0, 9, 10, 19), (31, 3)
        produced = _scan(law, symbols[:3], ports)
        expected = 0
        for symbol in reversed(produced) if side else produced:
            expected = law.advance(BoundarySide(side), expected, symbol)
        with _tile(tiles, adapter, primitive, symbols) as source:
            prefix = CausalPrefix(
                action, side, ports[side], 0, BoundaryTileView(source.tile, 0, 3, side)
            )
            with (
                patch.object(adapter, "wiring", wraps=adapter.wiring) as wiring,
                patch.object(
                    adapter, "initial_ports", wraps=adapter.initial_ports
                ) as initial,
                patch(
                    "number_compiler.hashlife.execution.tile_causal_pair_transfer.fused_interface",
                    side_effect=AssertionError("decimal morphism used fallback"),
                ),
            ):
                result = CausalTileEngine(scheduler)._run(
                    CausalFrame("residual", (action, side, prefix, ports[1 - side])),
                    tile_result=False,
                )
            assert result == expected
            rows.append(
                {
                    "side": side,
                    "width": 3,
                    "result": result,
                    "oracle": expected,
                    "wiring_calls": wiring.call_count,
                    "initial_ports_calls": initial.call_count,
                    "morphism_observations": ledger.counters.get(
                        "reverse_morphism_transfer_observations", 0
                    ),
                    "fallback_poisoned": True,
                }
            )
    return rows


print(json.dumps({"radix": radix_cases(), "dead_setup": dead_setup_cases()}, indent=2))

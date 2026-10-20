"""Compare the finite Isabelle publisher data with the actual compiled owner."""

from __future__ import annotations

import ast
import re
from pathlib import Path
from typing import cast

from devtools.paths import isabelle_root
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from tests.support.tile_kernel import make_tile_runtime


def _proof_rows(name: str) -> list[list[int | bool]]:
    theory = isabelle_root(Path(__file__).resolve().parents[3]) / (
        "integration/etale/etale/Physical_Collatz_Bound_Consumer.thy"
    )
    declaration = re.search(
        rf'definition {name} :: "[^"]+" where\s*"([^"]+)"', theory.read_text()
    )
    assert declaration is not None
    # Accept exactly the selector proved in Isabelle, not arbitrary lists
    # elsewhere in the file or changed admission predicates.
    selector = re.fullmatch(
        rf"{name} symbol =\s*\(if symbol = 0 then (\[[^\]]+\])"
        r"\s+else if symbol = 1 then (\[[^\]]+\])\s+else (\[[^\]]+\])\)",
        declaration.group(1),
    )
    assert selector is not None
    rows: list[list[int | bool]] = []
    for text in selector.groups():
        row = ast.literal_eval(text)
        assert type(row) is list and len(cast(list[object], row)) == 6
        assert all(type(value) in (int, bool) for value in cast(list[object], row))
        rows.append(cast(list[int | bool], row))
    return rows


def test_proved_publisher_matches_every_compiled_port_binding() -> None:
    uses_right = _proof_rows("compiled_uses_right")
    local_output = _proof_rows("compiled_local_output")
    effect = CollatzPhysicalBlockEffect()
    _ledger, tiles, adapter, action, _scheduler = make_tile_runtime(effect)
    kernel = adapter.primitive_law(action)
    assert kernel.behavior is not None
    alphabet = adapter.alphabet(action)
    for symbol in range(3):
        with tiles.leaf(alphabet, symbol) as source:
            interface = adapter.compile_interface(
                action, source.tile, adapter.wiring(action)
            )
        publisher = adapter.interface_components(interface)[2]
        for left in range(6):
            assert effect.output_consumer(left, symbol) == (
                uses_right[symbol][left],
                local_output[symbol][left],
            )
            for right in range(3):
                expected = (
                    right if uses_right[symbol][left] else local_output[symbol][left]
                )
                binding = {
                    PortVariable(0, 0, "tile-left", 0): left,
                    PortVariable(0, 1, "tile-right", 0): right,
                }
                assert adapter.bits.evaluate(publisher, binding) == expected
                # Event weight is a separate observation in the installed
                # minimized behavior; matching output symbols alone is weaker.
                assert kernel.observe(left, symbol, right) == (
                    int(left == 0 and symbol == 1),
                    0,
                    0,
                )

"""Compare the legacy joint table with the production decimal factor compiler.

Run this as ``python -m devtools.benchmarks.decimal_leaf_output_compiler``.
Each candidate owns a fresh runtime.  Timing covers only compilation of the
twenty leaf-output functions; primitive-kernel admission is outside the timer.
"""

from __future__ import annotations

import json
from time import perf_counter, process_time
from typing import Literal

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
from number_compiler.hashlife.interfaces.diamond_quotient import DiamondQuotientArena
from number_compiler.hashlife.interfaces.semantic_bits import FactoredFunctionID
from number_compiler.hashlife.interfaces.tile_decimal_functions import (
    decimal_leaf_output,
)
from number_compiler.hashlife.interfaces.tile_interface_compilation import (
    input_ports_for_kernel,
    output_sorts_for_kernel,
)
from number_compiler.hashlife.tiles.tiles import TileArena
from number_compiler.resources.ledger import ResourceLedger

_COUNTERS = (
    "primitive_output_evaluations",
    "semantic_function_staged_nodes",
    "semantic_function_published_nodes",
    "semantic_bit_boolean_nodes_published",
    "semantic_factored_nodes_published",
    "semantic_function_workspace_allocated_nodes",
    "semantic_function_workspace_peak_nodes",
)


def _compile(mode: Literal["joint-table", "factored"]) -> dict[str, object]:
    ledger = ResourceLedger()
    kernels = DiamondKernelArena(ledger)
    quotients = DiamondQuotientArena(SemanticFunctionArena(ledger))
    adapter = PrimitiveTileKernelAdapter(TileArena(ledger), kernels, quotients)
    action = adapter.admit(BaseBlockEffect(10))
    kernel = adapter.primitive_law(action)
    ports = input_ports_for_kernel(kernel)
    left_port, right_port = ports
    output_sort = output_sorts_for_kernel(kernel)[2]
    before = dict(ledger.counters)
    function_nodes_before = len(adapter.bits.functions.nodes)
    factored_nodes_before = len(adapter.bits.nodes)
    wall_started, cpu_started = perf_counter(), process_time()
    outputs: list[FactoredFunctionID] = []
    for symbol in range(kernel.blank + 1):
        if mode == "factored":
            output = decimal_leaf_output(
                adapter.bits,
                kernel,
                symbol,
                ports,
                left_port,
                right_port,
                output_sort,
            )
        else:
            output = adapter.tabulated(
                ports,
                output_sort,
                (left_port, right_port),
                tuple(
                    kernel.emit(left, symbol, right)
                    for left in range(kernel.left_count)
                    for right in range(kernel.right_count)
                ),
            )
        outputs.append(output)
    wall_seconds = perf_counter() - wall_started
    cpu_seconds = process_time() - cpu_started
    after = dict(ledger.counters)
    # Verify every admissible assignment after the timed/counted construction.
    for symbol, output in enumerate(outputs):
        node = adapter.bits.resolve(output)
        if node.signature.inputs != ports or node.signature.output != output_sort:
            raise AssertionError("decimal candidates produced different signatures")
        for left in range(kernel.left_count):
            for right in range(kernel.right_count):
                observed = adapter.bits.evaluate(
                    output,
                    {
                        left_port.variable: left,
                        right_port.variable: right,
                    },
                )
                expected = kernel.effect.emit(
                    kernel.decode(BoundarySide.LEFT, left),
                    symbol,
                    kernel.decode(BoundarySide.RIGHT, right),
                )
                if observed != expected:
                    raise AssertionError(
                        (mode, symbol, left, right, observed, expected)
                    )
    return {
        "mode": mode,
        "wall_seconds": wall_seconds,
        "cpu_seconds": cpu_seconds,
        "semantic_function_nodes": (
            len(adapter.bits.functions.nodes) - function_nodes_before
        ),
        "factored_function_nodes": len(adapter.bits.nodes) - factored_nodes_before,
        "counter_deltas": {
            name: after.get(name, 0) - before.get(name, 0) for name in _COUNTERS
        },
        "verified_assignments": (kernel.blank + 1)
        * kernel.left_count
        * kernel.right_count,
    }


def main() -> None:
    table = _compile("joint-table")
    factored = _compile("factored")
    table_seconds = table["wall_seconds"]
    factored_seconds = factored["wall_seconds"]
    if type(table_seconds) is not float or type(factored_seconds) is not float:
        raise AssertionError("decimal compiler benchmark omitted its timings")
    print(
        json.dumps(
            {
                "schema": "decimal-leaf-output-compiler-v1",
                "joint_table": table,
                "factored": factored,
                "speedup": table_seconds / factored_seconds,
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))

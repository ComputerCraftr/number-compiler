"""Separate unbound geometry powering from source-bound harmonic projection."""

from __future__ import annotations

import argparse
import json
from time import perf_counter
from unittest.mock import patch

from devtools.proofs import exact_oracle
from devtools.proofs.reverse_geometry_context import ReverseGeometryContext
from number_compiler.arithmetic.carry.event_memory import forcing_event, pair_step
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.radix import reverse_pair_sums
from number_compiler.arithmetic.formula.symmetry_frame import (
    FixedRealCyclotomicGerm,
    ReverseAddSymmetryInnovationBlock,
    ReverseAddSymmetryProjection,
)
from number_compiler.arithmetic.functions.decision import MultiTerminalDecisionArena
from number_compiler.hashlife.interfaces.semantic_bits import BitFunctionArena
from number_compiler.sequences.reverse_add.cocycle_carrier import CocycleReverseCarrier
from number_compiler.sequences.reverse_add.factored_carrier import (
    FactoredReverseCarrier,
)


def geometry_probe(capacity: int, steps: int, seed: int) -> dict[str, object]:
    started = perf_counter()
    context = ReverseGeometryContext(capacity)
    rows: list[dict[str, object]] = []
    stage = 1
    action_seconds = 0.0
    observation_seconds = 0.0
    try:
        action = context.primitive()
        action_seconds = perf_counter() - started
        # The action is complete and unbound before this source is supplied.
        source = reverse_pair_sums(seed, 10)
        binding = context.binding(source)
        expected = source
        previous = 0
        while action.events <= steps:
            observed_at = perf_counter()
            for _ in range(previous, action.events):
                expected = pair_step(expected, 10)[0]
            previous = action.events
            before_nodes = context.expressions.observed_nodes
            before_tables = context.expressions.observed_tables
            output = context.observe(action, binding)
            if output is None:
                assert len(expected) > capacity
                return {
                    "status": "capacity_overflow",
                    "events": action.events,
                    "required_width": len(expected),
                    "rows": rows,
                }
            assert output == expected, (action.events, output, expected)
            observation_seconds += perf_counter() - observed_at
            row: dict[str, object] = {
                **context.metrics(action),
                "width": len(expected),
                "observed_expression_nodes": context.expressions.observed_nodes
                - before_nodes,
                "observed_consumer_tables": context.expressions.observed_tables
                - before_tables,
                "action_seconds": action_seconds,
                "oracle_and_observation_seconds": observation_seconds,
            }
            rows.append(row)
            print(json.dumps({"checkpoint": row}), flush=True)
            if action.events == steps:
                break
            stage = 2 * action.events
            failure = AssertionError(
                "primitive replay, point evaluation, or general Boolean expansion"
            )
            with (
                patch.object(context, "primitive", side_effect=failure),
                patch.object(context, "observe", side_effect=failure),
                patch.object(context.expressions, "evaluate", side_effect=failure),
                patch.object(
                    MultiTerminalDecisionArena,
                    "build_labeled_boxes",
                    side_effect=failure,
                ),
                patch.object(BitFunctionArena, "substitute", side_effect=failure),
                patch.object(CocycleReverseCarrier, "successor", side_effect=failure),
                patch.object(
                    CocycleReverseCarrier, "successor_with_actions", side_effect=failure
                ),
                patch.object(FactoredReverseCarrier, "successor", side_effect=failure),
                patch.object(
                    FactoredReverseCarrier, "successor_with_action", side_effect=failure
                ),
                patch.object(
                    ReverseAddSymmetryProjection,
                    "from_coefficients",
                    side_effect=failure,
                ),
            ):
                begin = perf_counter()
                try:
                    action = context.compose(action, action)
                finally:
                    action_seconds += perf_counter() - begin
        return {"status": "complete", "capacity": capacity, "rows": rows}
    except BlockContextBudgetExceeded as error:
        return {
            "status": "budget_exceeded",
            "stage": stage,
            "capacity": capacity,
            "retained_expression_nodes": len(context.expressions.nodes),
            "retained_schema_nodes": len(context.expressions.schemas),
            "retained_total_nodes": len(context.expressions.nodes)
            + len(context.expressions.schemas),
            "primitive_successors": context.primitive_successors,
            "error": str(error),
            "rows": rows,
        }


def harmonic_probe(steps: int, seed: int) -> dict[str, object]:
    orders = (2, 4, 8)
    source = reverse_pair_sums(seed, 10)
    direct = {
        order: ReverseAddSymmetryInnovationBlock.identity(
            start_parity=len(source) % 2, order=order, bits=5
        )
        for order in orders
    }
    stack: list[dict[int, ReverseAddSymmetryInnovationBlock] | None] = []
    rows = []
    for number in range(1, steps + 1):
        target, growth = pair_step(source, 10)
        event = forcing_event(source, target, growth)
        block = {
            order: ReverseAddSymmetryInnovationBlock.atom(
                event, growth, source_width=len(source), order=order, bits=5
            )
            for order in orders
        }
        direct = {order: direct[order].then(block[order]) for order in orders}
        level = 0
        while level < len(stack) and stack[level] is not None:
            left = stack[level]
            assert left is not None
            block = {order: left[order].then(block[order]) for order in orders}
            stack[level] = None
            level += 1
        if level == len(stack):
            stack.append(block)
        else:
            stack[level] = block
        source = target
        if number & (number - 1) == 0:
            assert all(
                direct[o].canonical_key == block[o].canonical_key for o in orders
            )
            germ = FixedRealCyclotomicGerm.from_fixed_views(
                {o: block[o].fixed_innovation for o in orders}, bits=5
            )
            row = {
                "events": number,
                "growths": block[2].growth,
                "harmonic": (
                    block[2].end_parity,
                    germ.r0,
                    germ.r1,
                    germ.q0,
                    germ.q02_slope,
                ),
                "projection_bits": 1 + germ.description_bits,
                "oracle_primitive_successors": number,
            }
            rows.append(row)
            print(json.dumps({"checkpoint": row}), flush=True)
    return {
        "status": "complete",
        "scope": "source-bound projection; two chronological halves, not repeated unknown forcing",
        "rows": rows,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("geometry", "harmonic"), default="geometry")
    parser.add_argument("--capacity", type=int, default=9)
    parser.add_argument("--steps", type=int, default=16)
    parser.add_argument("--seed", type=int, default=196)
    args = parser.parse_args()
    if args.steps < 1 or args.steps > 1024 or args.steps & (args.steps - 1):
        raise ValueError("probe horizon must be a power of two through 1024")
    with exact_oracle():
        result = (
            geometry_probe(args.capacity, args.steps, args.seed)
            if args.mode == "geometry"
            else harmonic_probe(args.steps, args.seed)
        )
    print(json.dumps(result, indent=2), flush=True)


if __name__ == "__main__":
    main()

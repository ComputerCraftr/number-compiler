"""Guarded contextual squaring and separate endpoint parity-plane diagnostics."""

from __future__ import annotations

import argparse
import json
from time import perf_counter
from unittest.mock import patch

from devtools.experiments.reverse_add.cocycle_carrier import CocycleReverseCarrier
from devtools.experiments.reverse_add.factored_carrier import (
    DOMAINS,
    FactoredReverseCarrier,
)
from devtools.verification import exact_oracle
from devtools.verification.reverse_cocycle_context import BoundedReverseCocycle
from number_compiler.arithmetic.carry.event_memory import pair_step
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.radix import reverse_pair_sums
from number_compiler.arithmetic.formula.decimal_pair_coordinates import (
    decimal_cocycle_value,
)


def contextual(
    capacity: int, seed: int, steps: int, max_nodes: int, *, symmetric: bool = False
) -> dict[str, object]:
    started = perf_counter()
    context: BoundedReverseCocycle | None = None
    rows: list[dict[str, object]] = []
    action_seconds = 0.0
    observation_seconds = 0.0
    stage = "context"
    try:
        context = BoundedReverseCocycle(
            capacity, max_nodes=max_nodes, symmetric=symmetric
        )
        stage = "A1"
        print(json.dumps({"stage": stage, "capacity": capacity}), flush=True)
        action = context.compile_primitive()
        action_seconds = perf_counter() - started
        field = reverse_pair_sums(seed, 10)
        binding = context.binding(field)
        previous = 0
        while action.events <= steps:
            observation_started = perf_counter()
            for _ in range(previous, action.events):
                field, _ = pair_step(field, 10)
            previous = action.events
            width = context.bits.evaluate(action.outputs[0], binding)
            if width is None:
                if len(field) <= capacity:
                    raise AssertionError("admitted oracle output was lost")
                return {
                    "status": "capacity_overflow",
                    "event": action.events,
                    "required_width": len(field),
                    "capacity": capacity,
                    "rows": rows,
                    "primitive_successors": context.temporal.primitive_successors,
                }
            if width != len(field):
                raise AssertionError((width, len(field)))
            for i, expected in enumerate(field):
                slot = min(i, width - 1 - i) if symmetric else i
                values = tuple(
                    context.bits.evaluate(f, binding)
                    for f in action.outputs[1 + 3 * slot : 4 + 3 * slot]
                )
                if any(v is None for v in values):
                    raise AssertionError("coordinate undefined under admitted context")
                domain, alpha, epsilon = (int(v) for v in values if v is not None)
                if decimal_cocycle_value(DOMAINS[domain], alpha, epsilon) != expected:
                    raise AssertionError((action.events, i, expected, values))
            observation_seconds += perf_counter() - observation_started
            t, k = context.temporal, context.cocycles
            row: dict[str, object] = {
                "event": action.events,
                "width": width,
                "f5_nodes": t.nodes(action.outputs[2::3]),
                "f2_nodes": t.nodes(action.outputs[3::3]),
                "domain_nodes": t.nodes(action.outputs[1::3]),
                "kappa_residual_ids": k.residual_count,
                "endpoint_kappa_ids": len(set(action.cocycles)),
                "kappa_decision_nodes": t.nodes(
                    tuple(k.resolve(r) for r in action.cocycles)
                ),
                "retained_function_nodes": len(context.bits.functions.nodes),
                "primitive_successors": t.primitive_successors,
                "temporal_compositions": t.temporal_compositions,
                "primitive_kappa_precompositions": context.kappa_precompositions,
                "action_seconds": action_seconds,
                "oracle_observation_seconds": observation_seconds,
                "seconds": perf_counter() - started,
            }
            rows.append(row)
            print(json.dumps({"checkpoint": row}), flush=True)
            if action.events == steps:
                break
            stage = f"A{2 * action.events}"
            print(json.dumps({"stage": stage}), flush=True)
            failure = AssertionError("primitive replay or midpoint value evaluation")
            with (
                patch.object(context, "compile_primitive", side_effect=failure),
                patch.object(t, "primitive", side_effect=failure),
                patch.object(context.bits, "evaluate", side_effect=failure),
                patch.object(FactoredReverseCarrier, "successor", side_effect=failure),
                patch.object(
                    FactoredReverseCarrier, "successor_with_action", side_effect=failure
                ),
                patch.object(CocycleReverseCarrier, "successor", side_effect=failure),
                patch.object(
                    CocycleReverseCarrier, "successor_with_actions", side_effect=failure
                ),
            ):
                composition_started = perf_counter()
                try:
                    action = t.compose(action, action)
                finally:
                    action_seconds += perf_counter() - composition_started
            if t.primitive_successors != 1:
                raise AssertionError(
                    "primitive compilation counter changed during squaring"
                )
        return {"status": "complete", "seed": seed, "capacity": capacity, "rows": rows}
    except BlockContextBudgetExceeded as error:
        return {
            "status": "budget_exceeded",
            "stage": stage,
            "seed": seed,
            "capacity": capacity,
            "max_nodes": max_nodes,
            "error": str(error),
            "rows": rows,
            "primitive_successors": context.temporal.primitive_successors
            if context
            else 0,
            "seconds": perf_counter() - started,
        }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--symmetric", action="store_true")
    parser.add_argument("--capacity", type=int, default=3)
    parser.add_argument("--seed", type=int, default=196)
    parser.add_argument("--steps", type=int, default=16)
    parser.add_argument("--max-nodes", type=int, default=30000)
    args = parser.parse_args()
    if args.steps < 1 or args.steps & (args.steps - 1):
        raise ValueError("the cocycle power probe requires a positive power of two")
    with exact_oracle():
        result = contextual(
            args.capacity,
            args.seed,
            args.steps,
            args.max_nodes,
            symmetric=args.symmetric,
        )
        result["symmetric"] = args.symmetric
    print(json.dumps(result, indent=2), flush=True)


if __name__ == "__main__":
    main()

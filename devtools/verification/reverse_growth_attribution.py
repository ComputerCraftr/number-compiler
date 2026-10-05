"""Attribute bounded reverse/add growth without calling syntax a quotient.

Free-action reachability and a separately labelled bound oracle slice are both
reported. The latter cannot license pruning a branch on an unbound interface.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from unittest.mock import patch

from devtools.verification import exact_oracle
from devtools.verification.reverse_consumer_audit import audit
from devtools.verification.reverse_geometry_context import (
    GeometryAction,
    ReverseGeometryContext,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.radix import reverse_pair_sums


def projected_growth(
    capacity: int, steps: int, slots: tuple[int, ...]
) -> dict[str, object]:
    """Cold final-half pullback into only the requested endpoint channels."""
    if steps < 2 or steps & (steps - 1):
        raise ValueError("projection comparison requires a dyadic horizon >=2")
    context = ReverseGeometryContext(capacity, value_quotient="mod9")
    action = context.primitive()
    while action.events < steps // 2:
        action = context.compose(action, action)
    e = context.expressions
    before = len(e.nodes) + len(e.schemas) + e.auxiliary_nodes
    consumer = context.project(action, slots)
    forbidden = AssertionError("consumer pullback executed a primitive or oracle")
    with (
        patch.object(context, "primitive", side_effect=forbidden),
        patch.object(e, "evaluate", side_effect=forbidden),
    ):
        pulled = context.pullback(action, consumer)
    reached = e.reachable((*pulled.outputs, pulled.admitted))
    return {
        "events": steps,
        "requested_output_slots": slots,
        "retained_before_final_pullback": before,
        "retained_after_final_pullback": len(e.nodes)
        + len(e.schemas)
        + e.auxiliary_nodes,
        "reachable_projected_nodes": len(reached),
        "reachable_by_kind": dict(
            sorted(Counter(e.nodes[i].kind for i in reached).items())
        ),
        "primitive_successors": context.primitive_successors,
        "raw_midpoint_ports_after_publish": sum(
            e.nodes[i].kind == "variable" and e.nodes[i].data[0] >= len(context.sizes)
            for i in reached
        ),
        "admission_preserved": True,
    }


def attribute_growth(
    context: ReverseGeometryContext,
    action: GeometryAction,
    *,
    previous: GeometryAction | None = None,
    binding: tuple[int, ...] | None = None,
) -> dict[str, object]:
    e = context.expressions
    output = e.reachable(action.outputs)
    admission = e.reachable((action.admitted,))
    reached = output | admission
    support: dict[int, int] = {}
    depth: dict[int, int] = {}
    for index in sorted(reached):
        node = e.nodes[index]
        mask = (1 << node.data[0]) if node.kind == "variable" else 0
        for child in node.args:
            mask |= support[child]
        support[index] = mask
        depth[index] = 1 + max((depth[c] for c in node.args), default=0)
    consumers = {
        i
        for i in reached
        if e.nodes[i].kind
        in (
            "table",
            "mirror_domain",
            "decimal_sum_domain",
            "growth_domain",
            "skew_pair_domain",
        )
    }
    previous_reached = (
        e.reachable((*previous.outputs, previous.admitted)) if previous else set()
    )
    slots = {e.nodes[i].data[0] for i in reached if e.nodes[i].kind == "variable"}
    result: dict[str, object] = {
        "reachable_by_kind": dict(
            sorted(Counter(e.nodes[i].kind for i in reached).items())
        ),
        "new_reachable_by_kind": dict(
            sorted(Counter(e.nodes[i].kind for i in reached - previous_reached).items())
        ),
        "retained_unreachable_nodes": len(e.nodes) - len(reached),
        "output_only_nodes": len(output - admission),
        "admission_only_nodes": len(admission - output),
        "shared_output_admission_nodes": len(output & admission),
        "consumer_input_arity_histogram": dict(
            sorted(Counter(support[i].bit_count() for i in consumers).items())
        ),
        "max_consumer_dependency_depth": max((depth[i] for i in consumers), default=0),
        "declared_source_ports": len(context.sizes),
        "reachable_source_ports": len(slots),
        "raw_midpoint_ports_after_publish": len(slots - set(range(len(context.sizes)))),
        "prior_endpoint_expressions_still_reachable": sum(
            v.index in reached for v in previous.outputs
        )
        if previous
        else 0,
        "consumer_expr_occurrences_with_input_dependencies": sum(
            bool(support[i]) for i in consumers
        ),
        "extensional_consumer_classes": None,
        "free_action_successor_conflicts": None,
    }
    if binding is not None:
        ordered = sorted(reached)
        values = dict(
            zip(
                ordered,
                e.evaluate(tuple(e.handle(i) for i in ordered), binding),
                strict=True,
            )
        )
        live: set[int] = set()
        pending = [action.admitted.index]
        if values[action.admitted.index]:
            pending.extend(v.index for v in action.outputs)
        while pending:
            index = pending.pop()
            if index in live:
                continue
            live.add(index)
            node = e.nodes[index]
            if node.kind == "select":
                condition, yes, no = node.args
                pending.extend((condition, yes if values[condition] else no))
            else:
                pending.extend(node.args)
        result["bound_oracle_slice"] = {
            "admitted": bool(values[action.admitted.index]),
            "demanded_nodes": len(live),
            "demanded_consumers": len(consumers & live),
            "unchosen_nodes": len(reached - live),
            "unchosen_consumers": len(consumers - live),
            "licenses_free_branch_pruning": False,
        }
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--capacity", type=int, default=16)
    parser.add_argument("--steps", type=int, default=64)
    args = parser.parse_args()
    if (
        not 3 <= args.capacity <= 64
        or not 1 <= args.steps <= 1024
        or args.steps & (args.steps - 1)
    ):
        raise ValueError("bounded capacity3..64 and dyadic horizon1..1024 required")
    with exact_oracle():
        context = ReverseGeometryContext(args.capacity, value_quotient="mod9")
        action = context.primitive()
        binding = context.binding(reverse_pair_sums(196, 10))
        previous = None
        rows: list[dict[str, object]] = []
        stage = 1
        try:
            while True:
                rows.append(
                    {
                        **context.metrics(action),
                        **audit(context, action),
                        **attribute_growth(
                            context, action, previous=previous, binding=binding
                        ),
                    }
                )
                if action.events >= args.steps:
                    result: dict[str, object] = {"status": "complete", "rows": rows}
                    break
                stage = 2 * action.events
                previous = action
                forbidden = AssertionError("composition executed a primitive or oracle")
                with (
                    patch.object(context, "primitive", side_effect=forbidden),
                    patch.object(
                        context.expressions, "evaluate", side_effect=forbidden
                    ),
                ):
                    action = context.compose(action, action)
        except BlockContextBudgetExceeded as error:
            result = {
                "status": "budget_exceeded",
                "stage": stage,
                "error": str(error),
                "retained_after_failed_stage": len(context.expressions.nodes)
                + len(context.expressions.schemas)
                + context.expressions.auxiliary_nodes,
                "rows": rows,
            }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))

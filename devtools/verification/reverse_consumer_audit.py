"""Measure consumer programs separately from their bound expression occurrences.

Translation/reflection families below are structural expression families with
coordinate maps retained conceptually, not successor-minimized semantic states.
No harmonic transport is asserted merely from sharing a local consumer law.
"""

from __future__ import annotations

import argparse
import json
from unittest.mock import patch

from devtools.verification import exact_oracle
from devtools.verification.reverse_geometry_context import (
    GeometryAction,
    ReverseGeometryContext,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.radix import reverse_pair_sums


def audit(context: ReverseGeometryContext, action: GeometryAction) -> dict[str, object]:
    e = context.expressions
    reached = e.reachable((*action.outputs, action.admitted))
    # Each slot after width has a domain/F5/parity role and a spatial orbit.
    family_keys: dict[tuple[object, ...], int] = {}
    family: dict[int, tuple[int, int]] = {}
    extent: dict[int, tuple[int, int] | None] = {}
    support: dict[int, int] = {}
    work = 0
    for index in sorted(reached):
        node = e.nodes[index]
        work += 1 + len(node.args)
        if work > 1000000:
            raise BlockContextBudgetExceeded(
                "consumer family audit work budget exceeded"
            )
        if node.kind == "variable":
            slot = node.data[0]
            role = (slot - 1) % context.stride if slot else -1
            extent[index] = (
                ((slot - 1) // context.stride, (slot - 1) // context.stride)
                if slot
                else None
            )
            support[index] = 1 << slot
            payload: object = ("coordinate-role", role)
        else:
            locations = [
                extent[child] for child in node.args if extent[child] is not None
            ]
            extent[index] = (
                (
                    min(span[0] for span in locations if span is not None),
                    max(span[1] for span in locations if span is not None),
                )
                if locations
                else None
            )
            inputs = 0
            for child in node.args:
                inputs |= support[child]
            support[index] = inputs
            payload = (
                e.consumer_program(e.handle(index))
                if node.kind == "table"
                else node.data
            )
        variants = []
        for reflected in (0, 1):
            children = []
            parent_span = extent[index]
            for position, child in enumerate(node.args):
                child_span = extent[child]
                shift = 0
                if parent_span is not None and child_span is not None:
                    shift = (
                        parent_span[1] - child_span[1]
                        if reflected
                        else child_span[0] - parent_span[0]
                    )
                coefficient = node.data[position + 1] if node.kind == "affine" else 0
                children.append((family[child][reflected], shift, coefficient))
            if node.kind == "affine":
                # Argument ID order is not semantic for a modular affine sum.
                children.sort()
                variant_payload: object = node.data[0]
            else:
                variant_payload = payload
            key = node.kind, node.size, variant_payload, tuple(children)
            value = family_keys.get(key)
            if value is None:
                value = len(family_keys)
                family_keys[key] = value
            variants.append(value)
        family[index] = variants[0], variants[1]
    occurrences = [i for i in reached if e.nodes[i].kind == "table"]
    programs = {e.consumer_program(e.handle(i)) for i in occurrences}
    tables_by_identity = {
        id(e.consumer_program(e.handle(i))[2]): e.consumer_program(e.handle(i))[2]
        for i in occurrences
    }
    binding_families = {min(family[e.nodes[i].args[0]]) for i in occurrences}
    bindings = {e.nodes[i].args[0] for i in occurrences}
    source_roles = dict.fromkeys(("width", *context.coordinate_roles), 0)
    for index in reached:
        node = e.nodes[index]
        if node.kind == "variable":
            slot = node.data[0]
            input_role = (
                "width"
                if slot == 0
                else context.coordinate_roles[(slot - 1) % context.stride]
            )
            source_roles[input_role] += 1
    geometry_mask = 1 | sum(
        1 << slot for slot in range(1, len(context.sizes), context.stride)
    )
    geometry_only_bindings = sum(not support[i] & ~geometry_mask for i in bindings)
    native = [
        i
        for i in reached
        if e.nodes[i].kind
        in (
            "mirror_pair",
            "mirror_domain",
            "decimal_sum_domain",
            "growth_symbol",
            "growth_domain",
            "growth_value_plane",
            "skew_pair_domain",
        )
    ]
    mirrored = [
        i for i in native if e.nodes[i].kind in ("mirror_pair", "mirror_domain")
    ]
    adjacent = [i for i in native if e.nodes[i].kind == "decimal_sum_domain"]
    return {
        "events": action.events,
        "unresolved_consumer_occurrences": len(occurrences),
        "unique_consumer_schema_ids": len(programs),
        "unique_binding_ids": len(bindings),
        "finite_consumers_including_native": len(occurrences) + len(native),
        "native_consumer_occurrences": len(native),
        "native_operand_tuple_bindings": len({e.nodes[i].args for i in native}),
        "mirror_residue_response_bindings": len({e.nodes[i].args[0] for i in mirrored}),
        "mirror_carry_sum_bindings": len({e.nodes[i].args[1] for i in mirrored}),
        "growth_normalized_residue_bindings": len(
            {arg for i in adjacent for arg in e.nodes[i].args}
        ),
        "unique_binding_family_ids": len(binding_families),
        "max_residual_hole_arity": max(
            (len(e.nodes[i].args) for i in occurrences), default=0
        ),
        "max_binding_input_arity": max(
            (support[e.nodes[i].args[0]].bit_count() for i in occurrences), default=0
        ),
        "max_boundary_interface_arity": len(context.sizes),
        "consumer_program_entries_counted_per_occurrence": sum(
            len(e.consumer_program(e.handle(i))[2]) for i in occurrences
        ),
        "unique_consumer_program_entries": sum(len(program[2]) for program in programs),
        "physical_consumer_table_tuples": len(tables_by_identity),
        "physical_consumer_table_entries": sum(map(len, tables_by_identity.values())),
        "successor_refinement_classes": None,
        "successor_conflicts": None,
        "successor_refinement_status": "not established: schema sharing retains operand bindings and their full transformations",
        "independent_harmonic_factors_in_action": 0,
        "source_input_roles": source_roles,
        "independent_carry_border_harmonic_inputs": 0,
        "derived_carry_operation_nodes": sum(
            e.nodes[i].kind in ("carry_apply", "carry_compose") for i in reached
        ),
        "bindings_depending_only_on_initial_geometry_and_width": geometry_only_bindings,
        "bindings_with_initial_value_dependencies": len(bindings)
        - geometry_only_bindings,
        "family_audit_work": work,
        "family_audit_work_unit": "nodes plus argument edges; excludes hashing and set allocation",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--capacity", type=int, default=9)
    parser.add_argument("--steps", type=int, default=16)
    parser.add_argument("--growth-coboundary", action="store_true")
    parser.add_argument("--mod9", action="store_true")
    args = parser.parse_args()
    if args.steps < 1 or args.steps > 1024 or args.steps & (args.steps - 1):
        raise ValueError("audit horizon must be a power of two through 1024")
    with exact_oracle():
        context = ReverseGeometryContext(
            args.capacity,
            growth_quotient=args.growth_coboundary,
            value_quotient="mod9" if args.mod9 else "crt",
        )
        rows = []
        stage = 1
        try:
            action = context.primitive()
            binding = context.binding(reverse_pair_sums(196, 10))
            while action.events <= args.steps:
                row = {**context.metrics(action), **audit(context, action)}
                rows.append(row)
                print(json.dumps({"checkpoint": row}), flush=True)
                assert context.observe(action, binding) is not None
                if action.events == args.steps:
                    break
                stage = action.events * 2
                failure = AssertionError(
                    "audit composition replayed a primitive or observation"
                )
                with (
                    patch.object(context, "primitive", side_effect=failure),
                    patch.object(context.expressions, "evaluate", side_effect=failure),
                ):
                    action = context.compose(action, action)
            result: dict[str, object] = {"status": "complete", "rows": rows}
        except BlockContextBudgetExceeded as error:
            result = {
                "status": "budget_exceeded",
                "stage": stage,
                "retained_expression_nodes": len(context.expressions.nodes),
                "retained_schema_nodes": len(context.expressions.schemas),
                "retained_total_nodes": len(context.expressions.nodes)
                + len(context.expressions.schemas)
                + context.expressions.auxiliary_nodes,
                "retained_auxiliary_nodes": context.expressions.auxiliary_nodes,
                "error": str(error),
                "rows": rows,
            }
    print(json.dumps(result, indent=2), flush=True)


if __name__ == "__main__":
    main()

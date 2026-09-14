"""Per-temporal-layer audit for the powered HashLife/block runtime.

This intentionally reports cache *ownership* and carrier cutovers separately.
It is a diagnostic for late cache hits / representation fallbacks, not a timing
benchmark and not part of the sequence semantics.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from typing import TYPE_CHECKING

from devtools.proofs.block_runtime import ComposedRuntimeMixin
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.block_effect import BlockEffect


@dataclass(frozen=True, slots=True)
class LayerAudit:
    exponent: int
    node_id: int
    left_carrier: str
    right_carrier: str
    left_states: int
    right_states: int
    left_partition_domain: int
    right_partition_domain: int
    scalar_emit_entries: int
    scalar_emit_hits: int
    scalar_emit_misses: int
    compiler_scalar_probes: int
    symbolic_row_entries: int
    symbolic_row_hits: int
    symbolic_row_misses: int
    symbolic_group_evals: int
    tile_advance_entries: int
    tile_advance_hits: int
    tile_advance_misses: int
    tile_output_entries: int
    tile_output_hits: int
    tile_output_misses: int
    boundary_advance_entries: int
    boundary_output_entries: int
    reverse_boundary_advance_entries: int
    recursive_action_nodes: int
    recursive_value_entries: int
    recursive_value_hits: int
    recursive_value_misses: int


def _carrier(node: ComposedRuntimeMixin, side: int) -> str:
    if node._partition_enabled[side]:
        return "partition"
    if node._functional_enabled[side]:
        return "functional"
    if node._recursive_enabled[side]:
        return "recursive"
    return "sparse"


def layer_audit(
    root: BlockEffect | None,
) -> list[LayerAudit]:
    seen: set[int] = set()
    stack = [root]
    out: list[LayerAudit] = []
    while stack:
        node = stack.pop()
        ident = id(node)
        if ident in seen:
            continue
        seen.add(ident)
        if not isinstance(node, ComposedRuntimeMixin):
            continue
        p0, p1 = node._partition_domains
        out.append(
            LayerAudit(
                exponent=int(node.exponent),
                node_id=int(node.node_id),
                left_carrier=_carrier(node, 0),
                right_carrier=_carrier(node, 1),
                left_states=int(node._states[0]),
                right_states=int(node._states[1]),
                left_partition_domain=0 if p0 is None else len(p0),
                right_partition_domain=0 if p1 is None else len(p1),
                scalar_emit_entries=0
                if node._output_slots is None
                else len(node._output_slots),
                scalar_emit_hits=int(node._output_cache_hits),
                scalar_emit_misses=int(node._output_cache_misses),
                compiler_scalar_probes=int(node._output_uncached_probes),
                symbolic_row_entries=sum(
                    len(cache) for cache in node._symbolic_output_rows
                ),
                symbolic_row_hits=int(node._symbolic_output_row_hits),
                symbolic_row_misses=int(node._symbolic_output_row_misses),
                symbolic_group_evals=int(node._symbolic_output_group_evals),
                tile_advance_entries=len(node._macro_tile_advance_cache),
                tile_advance_hits=int(node._macro_tile_advance_hits),
                tile_advance_misses=int(node._macro_tile_advance_misses),
                tile_output_entries=len(node._macro_tile_output_cache),
                tile_output_hits=int(node._macro_tile_output_hits),
                tile_output_misses=int(node._macro_tile_output_misses),
                boundary_advance_entries=0,
                boundary_output_entries=0,
                reverse_boundary_advance_entries=0,
                recursive_action_nodes=sum(
                    (0 if pool is None else len(pool))
                    for pool in node._recursive_residual_intern
                )
                + sum(1 for x in node._recursive_constant if x is not None),
                recursive_value_entries=len(node._recursive_value_cache),
                recursive_value_hits=int(node._recursive_value_cache_hits),
                recursive_value_misses=int(node._recursive_value_cache_misses),
            )
        )
        stack.extend((node.first, node.second))
    out.sort(key=lambda x: (x.exponent, x.node_id))
    return out


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("family", choices=("collatz", "reverse"))
    parser.add_argument("seed", type=int)
    parser.add_argument("steps", type=int)
    parser.add_argument("--position", type=int, default=0)
    parser.add_argument(
        "--pretty", action="store_true", help="pretty-print JSON for interactive use"
    )
    args = parser.parse_args()

    term: PoweredCollatzTerm | ReverseAddPoweredTerm
    if args.family == "collatz":
        term = PoweredCollatzTerm(args.seed, args.steps)
    else:
        term = ReverseAddPoweredTerm(args.seed, args.steps)
    # Preserve the construction/compile phase explicitly. Per-layer counters are
    # cumulative owners, so publishing only the post-query rows made eager work
    # look like query-time reuse.
    compiler_layers = layer_audit(term.effect)
    value = term.digit(args.position)
    metrics = term.metrics()
    behavior = term.behavior_metrics()
    payload = {
        "behavior_description": asdict(behavior),
        "family": args.family,
        "seed": args.seed,
        "steps": args.steps,
        "position": args.position,
        "value": value,
        "metrics_schema_version": metrics.metrics_schema_version,
        "resource_inventory": [asdict(item) for item in metrics.resource_inventory],
        "resource_work_counters": metrics.resource_work_counters,
        "resource_ledger_entries": metrics.resource_ledger_entries,
        "cache_slots": metrics.cache_slots,
        "exact_source_occurrences": metrics.exact_source_occurrences,
        "spatial_occurrence_bindings": metrics.spatial_occurrence_bindings,
        "spatial_binding_nodes": metrics.spatial_binding_nodes,
        "canonical_transfer_nodes": metrics.canonical_transfer_nodes,
        "temporal_program_nodes": metrics.temporal_program_nodes,
        "finite_port_state_nodes": metrics.finite_port_state_nodes,
        "other_retained_nodes": metrics.other_retained_nodes,
        "resource_ledger_nodes": metrics.resource_ledger_nodes,
        "resource_observed_entries": metrics.resource_observed_entries,
        "resource_observed_nodes": metrics.resource_observed_nodes,
        "resource_accounting_mismatch": metrics.resource_accounting_mismatch,
        "resource_audit_complete": metrics.resource_audit_complete,
        "resource_unregistered_containers": metrics.resource_unregistered_containers,
        "resource_unregistered_payload_resolvers": metrics.resource_unregistered_payload_resolvers,
        "forbidden_future_payloads": metrics.forbidden_future_payloads,
        "retained_unbounded_future_integers": metrics.retained_unbounded_future_integers,
        "compiler_program_nodes": metrics.compiler_program_nodes,
        "application_program_nodes": metrics.application_program_nodes,
        "bounded_limb_operations": metrics.bounded_limb_operations,
        "maximum_arithmetic_bits": metrics.maximum_arithmetic_bits,
        "explicitly_materialized_endpoints": metrics.explicitly_materialized_endpoints,
        "retained_cache_entries": metrics.retained_cache_entries,
        "bounded_application_enabled": metrics.bounded_application_enabled,
        "bounded_application_temporal_state_classes": metrics.bounded_application_temporal_state_classes,
        "bounded_application_temporal_action_classes": metrics.bounded_application_temporal_action_classes,
        "bounded_application_exact_spatial_occurrences": metrics.bounded_application_exact_spatial_occurrences,
        "bounded_application_symbolic_action_nodes": metrics.bounded_application_symbolic_action_nodes,
        "bounded_application_jump_entries": metrics.bounded_application_jump_entries,
        "bounded_application_primitive_step_evaluations": metrics.bounded_application_primitive_step_evaluations,
        "bounded_application_action_compositions": metrics.bounded_application_action_compositions,
        "bounded_application_action_applications": metrics.bounded_application_action_applications,
        "bounded_application_nonlinear_branch_evaluations": metrics.bounded_application_nonlinear_branch_evaluations,
        "bounded_application_exact_endpoint_entries": metrics.bounded_application_exact_endpoint_entries,
        "bounded_application_query_requests": metrics.bounded_application_query_requests,
        "bounded_application_quotient_builds": metrics.bounded_application_quotient_builds,
        "bounded_application_residual_physical_steps": metrics.bounded_application_residual_physical_steps,
        "bounded_application_retained_entries": metrics.bounded_application_retained_entries,
        "budgeted_cache_entries": metrics.budgeted_cache_entries,
        "leaf_effect_cache_entries": metrics.leaf_effect_cache_entries,
        "algebraic_memo_cache_entries": metrics.algebraic_memo_cache_entries,
        "compiler_retained_cache_entries": metrics.compiler_retained_cache_entries,
        "query_retained_cache_entries": metrics.query_retained_cache_entries,
        "compiler_algebraic_memo_cache_entries": metrics.compiler_algebraic_memo_cache_entries,
        "query_algebraic_memo_cache_entries": metrics.query_algebraic_memo_cache_entries,
        "compiler_retained_execution_nodes": metrics.compiler_retained_execution_nodes,
        "query_retained_execution_nodes": metrics.query_retained_execution_nodes,
        "hashlife_high_level_tile_hits": metrics.hashlife_high_level_tile_hits
        if hasattr(metrics, "hashlife_high_level_tile_hits")
        else metrics.high_level_tile_hits,
        "hashlife_high_level_tile_misses": metrics.hashlife_high_level_tile_misses
        if hasattr(metrics, "hashlife_high_level_tile_misses")
        else metrics.high_level_tile_misses,
        "finite_action_cache_entries": metrics.finite_action_cache_entries,
        "spacetime_macro_cache_hits": metrics.spacetime_macro_cache_hits,
        "spacetime_macro_cache_misses": metrics.spacetime_macro_cache_misses,
        "spacetime_macro_cache_entries": metrics.spacetime_macro_cache_entries,
        "spacetime_macro_cache_hit_rate": (
            metrics.spacetime_macro_cache_hits
            / (
                metrics.spacetime_macro_cache_hits
                + metrics.spacetime_macro_cache_misses
            )
            if metrics.spacetime_macro_cache_hits + metrics.spacetime_macro_cache_misses
            else 0.0
        ),
        "spacetime_tile_advance_cache_hits": metrics.spacetime_tile_advance_cache_hits,
        "spacetime_tile_advance_cache_misses": metrics.spacetime_tile_advance_cache_misses,
        "spacetime_tile_advance_cache_entries": metrics.spacetime_tile_advance_cache_entries,
        "spacetime_tile_output_cache_hits": metrics.spacetime_tile_output_cache_hits,
        "spacetime_tile_output_cache_misses": metrics.spacetime_tile_output_cache_misses,
        "spacetime_tile_output_cache_entries": metrics.spacetime_tile_output_entries,
        "scalar_emit_cache_entries": metrics.scalar_emit_cache_entries,
        "scalar_emit_compiler_probes": metrics.scalar_emit_compiler_probes,
        "symbolic_output_row_cache_hits": metrics.symbolic_output_row_cache_hits,
        "symbolic_output_row_cache_misses": metrics.symbolic_output_row_cache_misses,
        "symbolic_output_row_cache_entries": metrics.symbolic_output_row_cache_entries,
        "symbolic_output_group_evals": metrics.symbolic_output_group_evals,
        "partition_preimage_cache_hits": metrics.partition_preimage_cache_hits,
        "partition_preimage_cache_misses": metrics.partition_preimage_cache_misses,
        "partition_preimage_cache_entries": metrics.partition_preimage_cache_entries,
        "partition_preimage_map_cache_entries": metrics.partition_preimage_map_cache_entries,
        "partition_emit_mask_cache_entries": metrics.partition_emit_mask_cache_entries,
        "boundary_anchor_mask_cache_entries": metrics.boundary_anchor_mask_cache_entries,
        "boundary_value_mask_cache_entries": metrics.boundary_value_mask_cache_entries,
        "compiler_partition_preimage_cache_hits": metrics.compiler_partition_preimage_cache_hits,
        "compiler_partition_preimage_cache_misses": metrics.compiler_partition_preimage_cache_misses,
        "compiler_partition_preimage_cache_entries": metrics.compiler_partition_preimage_cache_entries,
        "compiler_symbolic_output_row_cache_hits": metrics.compiler_symbolic_output_row_cache_hits,
        "compiler_symbolic_output_row_cache_misses": metrics.compiler_symbolic_output_row_cache_misses,
        "compiler_symbolic_output_row_cache_entries": metrics.compiler_symbolic_output_row_cache_entries,
        "compiler_symbolic_output_group_evals": metrics.compiler_symbolic_output_group_evals,
        "compiler_partition_preimage_map_cache_entries": metrics.compiler_partition_preimage_map_cache_entries,
        "compiler_partition_emit_mask_cache_entries": metrics.compiler_partition_emit_mask_cache_entries,
        "compiler_boundary_anchor_mask_cache_entries": metrics.compiler_boundary_anchor_mask_cache_entries,
        "compiler_boundary_value_mask_cache_entries": metrics.compiler_boundary_value_mask_cache_entries,
        "functional_carrier_layers_left": metrics.functional_carrier_layers_left,
        "functional_carrier_layers_right": metrics.functional_carrier_layers_right,
        "partition_carrier_layers_left": metrics.partition_carrier_layers_left,
        "partition_carrier_layers_right": metrics.partition_carrier_layers_right,
        "recursive_carrier_layers_left": metrics.recursive_carrier_layers_left,
        "recursive_carrier_layers_right": metrics.recursive_carrier_layers_right,
        "mixed_finite_carrier_layers": metrics.mixed_finite_carrier_layers,
        "max_partition_domain_left": metrics.max_partition_domain_left,
        "max_partition_domain_right": metrics.max_partition_domain_right,
        "first_recursive_exponent_left": metrics.first_recursive_exponent_left,
        "first_recursive_exponent_right": metrics.first_recursive_exponent_right,
        "canonical_recursive_left_states": metrics.canonical_recursive_left_states,
        "canonical_recursive_right_states": metrics.canonical_recursive_right_states,
        "recursive_action_left_nodes": metrics.recursive_action_left_nodes,
        "recursive_action_right_nodes": metrics.recursive_action_right_nodes,
        "recursive_action_nodes": metrics.recursive_action_left_nodes
        + metrics.recursive_action_right_nodes,
        "recursive_state_intern_hits": metrics.recursive_state_intern_hits,
        "recursive_state_intern_misses": metrics.recursive_state_intern_misses,
        "compiler_recursive_state_intern_hits": metrics.compiler_recursive_state_intern_hits,
        "compiler_recursive_state_intern_misses": metrics.compiler_recursive_state_intern_misses,
        "recursive_action_intern_hits": metrics.recursive_action_intern_hits,
        "recursive_action_intern_misses": metrics.recursive_action_intern_misses,
        "compiler_recursive_action_intern_hits": metrics.compiler_recursive_action_intern_hits,
        "compiler_recursive_action_intern_misses": metrics.compiler_recursive_action_intern_misses,
        "recursive_value_cache_entries": metrics.recursive_value_cache_entries,
        "recursive_value_cache_hits": metrics.recursive_value_cache_hits,
        "recursive_value_cache_misses": metrics.recursive_value_cache_misses,
        "compiler_recursive_value_cache_entries": metrics.compiler_recursive_value_cache_entries,
        "compiler_recursive_value_cache_hits": metrics.compiler_recursive_value_cache_hits,
        "compiler_recursive_value_cache_misses": metrics.compiler_recursive_value_cache_misses,
        "raw_spacetime_boundary_cache_entries": metrics.raw_spacetime_boundary_cache_entries,
        "retained_cache_accounting_delta": metrics.retained_cache_accounting_delta,
        "source_index_cache_entries": metrics.source_index_cache_entries,
        "total_hashlife_retained_entries": metrics.total_hashlife_retained_entries,
        "canonical_tile_arena_nodes": metrics.canonical_tile_arena_nodes,
        "canonical_tile_arena_nodes_global": metrics.canonical_tile_arena_nodes_global,
        "canonical_tile_arena_nodes_index_build": metrics.canonical_tile_arena_nodes_index_build,
        "canonical_tile_arena_nodes_query": metrics.canonical_tile_arena_nodes_query,
        "canonical_tile_intern_hits_index_build": metrics.canonical_tile_intern_hits_index_build,
        "canonical_tile_intern_misses_index_build": metrics.canonical_tile_intern_misses_index_build,
        "canonical_tile_intern_hits_query": metrics.canonical_tile_intern_hits_query,
        "canonical_tile_intern_misses_query": metrics.canonical_tile_intern_misses_query,
        "canonical_tile_mirror_hits_query": metrics.canonical_tile_mirror_hits_query,
        "canonical_tile_mirror_misses_query": metrics.canonical_tile_mirror_misses_query,
        "canonical_tile_node_id_collisions": metrics.canonical_tile_node_id_collisions,
        "canonical_tile_invalid_intern_entries": metrics.canonical_tile_invalid_intern_entries,
        "canonical_tile_mirror_involution_violations": metrics.canonical_tile_mirror_involution_violations,
        "operator_node_id_collisions": metrics.operator_node_id_collisions,
        "semantic_effect_duplicate_owners": metrics.semantic_effect_duplicate_owners,
        "spacetime_tile_advance_repeated_cold_misses": metrics.spacetime_tile_advance_repeated_cold_misses,
        "spacetime_tile_output_repeated_cold_misses": metrics.spacetime_tile_output_repeated_cold_misses,
        "scalar_emit_repeated_cold_misses": metrics.scalar_emit_repeated_cold_misses,
        "recursive_value_repeated_cold_misses": metrics.recursive_value_repeated_cold_misses,
        "sparse_carrier_layers_left": metrics.sparse_carrier_layers_left,
        "sparse_carrier_layers_right": metrics.sparse_carrier_layers_right,
        "first_sparse_exponent_left": metrics.first_sparse_exponent_left,
        "first_sparse_exponent_right": metrics.first_sparse_exponent_right,
        "layers_compiler_baseline": [asdict(row) for row in compiler_layers],
        "layers_after_query_total": [asdict(row) for row in layer_audit(term.effect)],
    }
    print(
        json.dumps(
            payload,
            indent=2 if args.pretty else None,
            sort_keys=True,
            separators=None if args.pretty else (",", ":"),
        )
    )


if __name__ == "__main__":
    main()

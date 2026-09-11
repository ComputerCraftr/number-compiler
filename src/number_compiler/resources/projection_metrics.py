"""Projection metric compatibility derived from one ledger snapshot."""

from __future__ import annotations

from dataclasses import fields
from typing import TYPE_CHECKING

from number_compiler.resources.metric_collection import (
    collect_ledger_metrics,
    ledger_fields_from,
)
from number_compiler.resources.metric_records import HashLifeProjectionMetrics
from number_compiler.resources.metric_registry import normalized_role as _role
from number_compiler.resources.metric_replace import replace_metric

if TYPE_CHECKING:
    from number_compiler.hashlife.observation.hashlife_projection import (
        HashLifeBlockIndex,
    )


def collect_projection_metrics(index: HashLifeBlockIndex) -> HashLifeProjectionMetrics:
    """Compiler snapshots and index-owned work have separate accounting scopes."""
    from number_compiler.arithmetic.fields.dyadic_tile import (
        tile_arena_metrics,
        tile_metrics,
    )
    from number_compiler.hashlife.observation.tile_projection import (
        LazyProjection as TileProjection,
    )

    ledger = collect_ledger_metrics(index._ledger)
    baseline = dict(index._effect_metric_baseline)
    geometry = tile_metrics(index.evaluation_root)
    tile_nodes = index._retained_tile_node_count()
    values = ledger_fields_from(ledger)
    compiler_entries = sum(
        item.entries
        for item in ledger.resource_inventory
        if _role(item.role) in ("compiled_action_program", "compiled_action_interner")
    )
    source_entries = sum(
        item.entries
        for item in ledger.resource_inventory
        if _role(item.role) == "exact_source"
    )
    # Compiler counts are frozen at index construction. They never inherit work
    # performed later by another index sharing an operator or a global arena.
    for item in fields(HashLifeProjectionMetrics):
        if item.name in values:
            continue
        if item.name.startswith("compiler_"):
            values[item.name] = baseline.get(item.name.removeprefix("compiler_"), 0)
        elif item.name.startswith(
            ("canonical_function_", "canonical_partition_", "canonical_recursive_")
        ):
            values[item.name] = baseline.get(item.name, 0)
    values.update(
        point_queries=index._point_queries,
        direct_powered_point_queries=index._direct_powered_point_queries,
        canonical_tile_roots=len(index._tile_roots),
        retained_execution_nodes=ledger.resource_ledger_nodes
        - ledger.source_payload_nodes,
        compiler_retained_execution_nodes=ledger.compiler_program_nodes,
        query_retained_execution_nodes=(
            ledger.resource_ledger_nodes
            - ledger.source_payload_nodes
            - ledger.compiler_program_nodes
        ),
        canonical_program_word_roots=baseline.get("canonical_program_word_roots", 0),
        dyadic_forest_chunks=geometry["forest_chunks"],
        dyadic_max_level=geometry["max_level"],
        peak_live_tile_roots=tile_nodes,
        tile_observations=ledger.resource_work_counters.get("source_leaf_reads", 0),
        canonical_tile_arena_nodes=tile_nodes,
        canonical_tile_arena_nodes_index_build=tile_nodes,
        canonical_tile_arena_nodes_query=0,
        # Compatibility population of shared immutable source-geometry tiles.
        # Index-owned execution content is reported by canonical_tile_nodes.
        canonical_tile_arena_nodes_global=tile_arena_metrics()["canonical_nodes"],
        retained_cache_entries=ledger.resource_ledger_entries,
        compiler_retained_cache_entries=compiler_entries,
        query_retained_cache_entries=ledger.resource_ledger_entries
        - compiler_entries
        - source_entries,
        budgeted_cache_entries=ledger.resource_ledger_entries,
        retained_cache_accounting_delta=ledger.resource_accounting_mismatch,
        total_hashlife_retained_entries=ledger.cache_slots,
        source_index_cache_entries=source_entries,
    )
    application_view: object = index._lazy_application
    if type(application_view) is TileProjection:
        from number_compiler.resources.application_metrics import (
            tile_application_compatibility_values,
        )
        from number_compiler.resources.behavior_metrics import (
            _tile_runtime_blocker,
        )

        values.update(
            tile_application_compatibility_values(index, ledger, compiler_entries)
        )
        action_hits = ledger.tile_temporal_action_hits
        action_aliases = ledger.tile_temporal_action_semantic_alias_hits
        action_evaluations = ledger.tile_temporal_action_publications + action_aliases
        values.update(
            temporal_parent_requests=action_hits + action_evaluations,
            temporal_parent_early_hits=action_hits,
            temporal_parent_compositions=action_evaluations,
            temporal_parent_late_duplicate_reductions=action_aliases,
            bounded_application_action_compositions=action_evaluations,
            scheduler_transitions=ledger.resource_work_counters.get(
                "tile_causal_frames", 0
            )
            + ledger.tile_temporal_complete_frames,
            scheduler_workspace_peak=max(
                ledger.resource_work_counters.get("tile_causal_workspace_peak", 0),
                ledger.tile_scheduler_workspace_peak,
                ledger.tile_fused_workspace_peak,
            ),
        )
        # The issued action was compiled from immutable, admitted kernels into
        # the executable tile action DAG.  Attest that sealed carrier from
        # identities and leases; reporting must not re-run semantic admission.
        values["bimachine_composition_certified"] = int(
            not _tile_runtime_blocker(index)
        )
    return replace_metric(HashLifeProjectionMetrics(*([0] * 15)), values)

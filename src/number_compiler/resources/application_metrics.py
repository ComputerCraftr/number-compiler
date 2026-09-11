"""Compatibility values derived from the canonical tile application."""

from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from number_compiler.hashlife.observation.hashlife_projection import (
        HashLifeBlockIndex,
    )
    from number_compiler.resources.metric_records import LedgerMetrics


__all__ = ["tile_application_compatibility_values"]


def tile_application_compatibility_values(
    index: HashLifeBlockIndex,
    ledger: LedgerMetrics,
    compiler_entries: int,
) -> dict[str, int]:
    """Forward actual canonical-tile execution from the same ledger snapshot."""
    work = ledger.resource_work_counters
    completed_misses = (
        ledger.completed_result_requests - ledger.completed_result_early_hits
    )
    tile_intern_misses = ledger.tile_intern_requests - ledger.tile_intern_early_hits
    mirror_misses = ledger.tile_mirror_requests - ledger.tile_mirror_early_hits
    boundary_requests = work.get("tile_causal_boundary_output_requests", 0)
    boundary_hits = work.get("tile_causal_boundary_output_hits", 0)
    tile_records = index._lazy_application.scheduler.tiles._nodes.values()
    maximum_tile_level = max((record.level for record in tile_records), default=0)
    return {
        "bounded_application_enabled": 1,
        "bounded_application_temporal_state_classes": ledger.local_interface_nodes,
        "bounded_application_temporal_action_classes": ledger.field_action_nodes,
        "bounded_application_exact_spatial_occurrences": ledger.canonical_tile_nodes,
        "bounded_application_symbolic_action_nodes": (
            ledger.field_action_nodes + ledger.canonical_transfer_nodes
        ),
        "bounded_application_jump_entries": ledger.completed_result_entries,
        "bounded_application_primitive_step_evaluations": ledger.sequential_generation_advances,
        "bounded_application_action_compositions": ledger.temporal_parent_compositions,
        "bounded_application_action_applications": work.get(
            "tile_scheduler_leaf_function_applications", 0
        ),
        "bounded_application_nonlinear_branch_evaluations": ledger.primitive_transition_evaluations,
        "bounded_application_exact_endpoint_entries": ledger.exact_endpoint_nodes,
        "bounded_application_query_requests": (
            index._point_queries + work.get("tile_projection_width_observations", 0)
        ),
        "bounded_application_quotient_builds": (
            work.get("primitive_tile_interface_publications", 0)
            + ledger.spatial_interface_composition_publications
            + ledger.fused_interface_publications
        ),
        "bounded_application_residual_physical_steps": ledger.sequential_generation_advances,
        "bounded_application_retained_entries": ledger.cache_slots - compiler_entries,
        "canonical_spacetime_macrocell_roots": ledger.pinned_completed_roots,
        "spacetime_macro_cache_hits": ledger.completed_result_early_hits,
        "spacetime_macro_cache_misses": completed_misses,
        "spacetime_macro_cache_entries": ledger.completed_result_entries,
        "spacetime_tile_advance_cache_hits": ledger.spatial_interface_composition_early_hits,
        "spacetime_tile_advance_cache_misses": (
            ledger.spatial_interface_composition_requests
            - ledger.spatial_interface_composition_early_hits
        ),
        "spacetime_tile_advance_cache_entries": ledger.spatial_interface_composition_entries,
        "spacetime_boundary_advance_cache_hits": ledger.powered_interface_early_hits,
        "spacetime_boundary_advance_cache_misses": ledger.powered_interface_requests
        - ledger.powered_interface_early_hits,
        "spacetime_boundary_advance_cache_entries": ledger.powered_interface_entries,
        "spacetime_tile_output_cache_hits": ledger.completed_result_early_hits,
        "spacetime_tile_output_cache_misses": completed_misses,
        "spacetime_tile_output_entries": ledger.completed_result_entries,
        "spacetime_tile_output_max_level": maximum_tile_level,
        "spacetime_boundary_output_cache_hits": boundary_hits,
        "spacetime_boundary_output_cache_misses": boundary_requests - boundary_hits,
        "spacetime_boundary_output_cache_entries": ledger.normalized_region_entries,
        "spacetime_temporal_absorption_max": ledger.powered_absorption_max_span,
        "temporal_leaf_applications": ledger.tile_scheduler_leaf_function_applications,
        "finite_action_unique": ledger.local_interface_nodes,
        "finite_action_alias_hits": work.get("quotient_semantic_interner_hits", 0),
        "finite_action_retained_entries": (
            ledger.canonical_transfer_nodes
            + ledger.powered_interface_entries
            + ledger.spatial_interface_composition_entries
            + ledger.fused_interface_entries
        ),
        "high_level_tile_hits": ledger.tile_scheduler_parent_early_hits
        + ledger.tile_scheduler_demand_parent_hits,
        "high_level_tile_misses": (
            ledger.tile_scheduler_direct_requests
            + ledger.tile_scheduler_fused_requests
            + ledger.tile_scheduler_temporal_complete_requests
            + ledger.tile_scheduler_demand_parent_misses
        ),
        "tile_observations": (
            work.get("source_leaf_reads", 0)
            + ledger.tile_observation_descents
            + ledger.tile_width_descents
            + ledger.tile_fused_observation_descents
        ),
        "canonical_tile_roots": ledger.tile_root_leases,
        "peak_live_tile_roots": ledger.tile_root_lease_peak,
        "canonical_tile_arena_nodes": ledger.canonical_tile_nodes,
        "canonical_tile_arena_nodes_index_build": index._canonical_tiles_at_build,
        "canonical_tile_arena_nodes_query": ledger.canonical_tile_nodes
        - index._canonical_tiles_at_build,
        "canonical_tile_intern_hits": ledger.tile_intern_early_hits,
        "canonical_tile_intern_misses": tile_intern_misses,
        "canonical_tile_mirror_hits": ledger.tile_mirror_early_hits,
        "canonical_tile_mirror_misses": mirror_misses,
    }

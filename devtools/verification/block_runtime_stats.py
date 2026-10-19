"""Metrics aggregation for composed block effects.

Kept separate from the execution mixin so instrumentation cannot regrow the hot
runtime implementation past the repository module-size policy.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BlockEffect, _effect_key

if TYPE_CHECKING:
    from devtools.verification.block_composed import ComposedBlockEffect


def _record_first_exponent(values: list[int], side: int, exponent: int) -> None:
    old = values[side]
    if old == 0 or exponent < old:
        values[side] = exponent


def composed_runtime_stats(self: ComposedBlockEffect) -> dict[str, int]:
    # Lazy import avoids a construction-time cycle; this function is called only
    # after ``_block_runtime`` has finished defining the mixin class.
    from devtools.verification.block_composed import ComposedBlockEffect

    seen: set[int] = set()
    seen_node_ids: set[int] = set()
    operator_node_id_collisions = 0
    semantic_effect_keys: set[object] = set()
    semantic_effect_duplicate_owners = 0
    stack: list[BlockEffect] = [self]
    states = [0, 0]
    hits = misses = 0
    output_hits = output_misses = output_uncached_probes = 0
    sparse_emit_delegations = 0
    sparse_emit_first_seen = sparse_emit_admissions = 0
    sparse_emit_admission_filter_nodes = 0
    output_slots = output_occupied = 0
    transition_entries = [0, 0]
    blank_hits = [0, 0]
    finite_kernel_states = [0, 0]
    finite_kernel_storage = 0
    functional_hits = functional_misses = 0
    canonical_function_states = [0, 0]
    canonical_partition_states = [0, 0]
    canonical_recursive_states = [0, 0]
    recursive_action_nodes = [0, 0]
    recursive_action_max_spatial_extent = [0, 0]
    recursive_action_max_depth = [0, 0]
    recursive_state_hits = recursive_state_misses = 0
    recursive_action_hits = recursive_action_misses = 0
    recursive_value_hits = recursive_value_misses = recursive_value_entries = 0
    provenance_path_states = [0, 0]
    partition_hits = partition_misses = 0
    partition_preimage_hits = partition_preimage_misses = 0
    behavioral_aliases = [0, 0]
    behavioral_alias_hits = [0, 0]
    behavioral_refinement_runs = [0, 0]
    spacetime_tile_output_entries = 0
    spacetime_tile_output_max_level = 0
    spacetime_temporal_absorption_max = 0
    spacetime_tile_advance_hits = spacetime_tile_advance_misses = 0
    spacetime_boundary_advance_hits = spacetime_boundary_advance_misses = 0
    spacetime_reverse_boundary_advance_hits = (
        spacetime_reverse_boundary_advance_misses
    ) = 0
    spacetime_tile_output_hits = spacetime_tile_output_misses = 0
    spacetime_boundary_output_hits = spacetime_boundary_output_misses = 0
    spacetime_sparse_transition_hits = spacetime_sparse_transition_misses = 0
    spacetime_tile_advance_entries = 0
    spacetime_boundary_advance_entries = 0
    spacetime_reverse_boundary_advance_entries = 0
    spacetime_boundary_output_entries = 0
    spacetime_sparse_transition_entries = 0
    symbolic_output_row_hits = symbolic_output_row_misses = 0
    symbolic_output_group_evals = boundary_value_index_builds = 0
    symbolic_output_row_entries = 0
    partition_preimage_entries = 0
    partition_preimage_map_entries = 0
    partition_emit_mask_entries = 0
    boundary_anchor_mask_entries = 0
    boundary_value_mask_entries = 0
    leaf_effect_transition_cache_entries = 0
    leaf_effect_output_cache_entries = 0
    leaf_effect_cache_entries = 0
    functional_carrier_layers = [0, 0]
    partition_carrier_layers = [0, 0]
    recursive_carrier_layers = [0, 0]
    first_recursive_exponent = [0, 0]
    sparse_carrier_layers = [0, 0]
    first_sparse_exponent = [0, 0]
    max_partition_domain = [0, 0]
    mixed_finite_carrier_layers = 0
    while stack:
        node = stack.pop()
        ident = id(node)
        if ident in seen:
            continue
        seen.add(ident)
        snapshot = (
            node.runtime_snapshot() if isinstance(node, ComposedBlockEffect) else None
        )
        node_id = snapshot.node_id if snapshot is not None else int(node.node_id)
        if node_id in seen_node_ids:
            operator_node_id_collisions += 1
        else:
            seen_node_ids.add(node_id)
        semantic_key = (
            snapshot.semantic_key if snapshot is not None else _effect_key(node)
        )
        if semantic_key in semantic_effect_keys:
            semantic_effect_duplicate_owners += 1
        else:
            semantic_effect_keys.add(semantic_key)
        if snapshot is not None:
            counters = snapshot.counters
            states[0] += snapshot.states[0]
            states[1] += snapshot.states[1]
            mixed_finite_carrier_layers += snapshot.mixed_finite_carrier_layers
            for side_index in (0, 1):
                canonical_partition_states[side_index] += snapshot.partition_states[
                    side_index
                ]
                partition_carrier_layers[side_index] += snapshot.partition_layers[
                    side_index
                ]
                canonical_function_states[side_index] += snapshot.functional_states[
                    side_index
                ]
                functional_carrier_layers[side_index] += snapshot.functional_layers[
                    side_index
                ]
                canonical_recursive_states[side_index] += snapshot.recursive_states[
                    side_index
                ]
                recursive_carrier_layers[side_index] += snapshot.recursive_layers[
                    side_index
                ]
                recursive_action_nodes[side_index] += snapshot.recursive_action_nodes[
                    side_index
                ]
                recursive_action_max_spatial_extent[side_index] = max(
                    recursive_action_max_spatial_extent[side_index],
                    snapshot.recursive_action_max_spatial_extent[side_index],
                )
                recursive_action_max_depth[side_index] = max(
                    recursive_action_max_depth[side_index],
                    snapshot.recursive_action_max_depth[side_index],
                )
                if snapshot.recursive_layers[side_index]:
                    _record_first_exponent(
                        first_recursive_exponent, side_index, snapshot.exponent
                    )
                sparse_carrier_layers[side_index] += snapshot.sparse_layers[side_index]
                max_partition_domain[side_index] = max(
                    max_partition_domain[side_index],
                    snapshot.max_partition_domain[side_index],
                )
                if snapshot.sparse_layers[side_index]:
                    _record_first_exponent(
                        first_sparse_exponent, side_index, snapshot.exponent
                    )
            hits += counters["map_eval_hits"]
            misses += counters["map_eval_misses"]
            output_hits += counters["output_cache_hits"]
            output_misses += counters["output_cache_misses"]
            output_uncached_probes += counters["output_uncached_probes"]
            sparse_emit_delegations += counters["sparse_emit_delegations"]
            sparse_emit_first_seen += counters["sparse_emit_first_seen"]
            sparse_emit_admissions += counters["sparse_emit_admissions"]
            sparse_emit_admission_filter_nodes += counters[
                "sparse_emit_admission_filter_nodes"
            ]
            output_slots += counters["output_cache_entries"]
            output_occupied += counters["output_cache_entries"]
            transition_entries[0] += counters["left_transition_entries"]
            transition_entries[1] += counters["right_transition_entries"]
            blank_hits[0] += counters["blank_left_saturation_hits"]
            blank_hits[1] += counters["blank_right_saturation_hits"]
            functional_hits += counters["functional_intern_hits"]
            functional_misses += counters["functional_intern_misses"]
            partition_hits += counters["partition_intern_hits"]
            partition_misses += counters["partition_intern_misses"]
            partition_preimage_hits += counters["partition_preimage_hits"]
            partition_preimage_misses += counters["partition_preimage_misses"]
            partition_preimage_entries += counters["partition_preimage_entries"]
            partition_preimage_map_entries += counters["partition_preimage_map_entries"]
            partition_emit_mask_entries += counters["partition_emit_mask_entries"]
            boundary_anchor_mask_entries += counters["boundary_anchor_mask_entries"]
            boundary_value_mask_entries += counters["boundary_value_mask_entries"]
            # Recursive boundary wrappers/interner are deleted.  Compatibility
            # state-interner counters remain hard zero in the public schema.
            recursive_action_hits += counters["recursive_action_intern_hits"]
            recursive_action_misses += counters["recursive_action_intern_misses"]
            recursive_value_hits += counters["recursive_value_cache_hits"]
            recursive_value_misses += counters["recursive_value_cache_misses"]
            recursive_value_entries += counters["recursive_value_cache_entries"]
            symbolic_output_row_hits += counters["symbolic_output_row_hits"]
            symbolic_output_row_misses += counters["symbolic_output_row_misses"]
            symbolic_output_group_evals += counters["symbolic_output_group_evals"]
            boundary_value_index_builds += counters["boundary_value_index_builds"]
            symbolic_output_row_entries += counters["symbolic_output_row_entries"]
            spacetime_tile_advance_hits += counters["spacetime_tile_advance_hits"]
            spacetime_tile_advance_misses += counters["spacetime_tile_advance_misses"]
            # Boundary-wrapper memo families are retired.  All composed
            # spatial actions are owned by the tile caches below.
            spacetime_tile_output_hits += counters["spacetime_tile_output_hits"]
            spacetime_tile_output_misses += counters["spacetime_tile_output_misses"]
            spacetime_tile_advance_entries += counters["spacetime_tile_advance_entries"]
            spacetime_tile_output_entries += counters["spacetime_tile_output_entries"]
            spacetime_temporal_absorption_max = max(
                spacetime_temporal_absorption_max,
                counters["spacetime_temporal_absorption"],
            )
            if snapshot.tile_output_levels:
                spacetime_tile_output_max_level = max(
                    spacetime_tile_output_max_level, max(snapshot.tile_output_levels)
                )
            stack.extend((snapshot.first, snapshot.second))
        else:
            child = node.runtime_stats()
            transition_entries[0] += child["left_transition_entries"]
            transition_entries[1] += child["right_transition_entries"]
            finite_kernel_states[0] += child.get("finite_kernel_left_states", 0)
            finite_kernel_states[1] += child.get("finite_kernel_right_states", 0)
            finite_kernel_storage += child.get("finite_kernel_storage_bytes", 0)
            leaf_effect_transition_cache_entries += child.get(
                "leaf_effect_transition_cache_entries", 0
            )
            leaf_effect_output_cache_entries += child.get(
                "leaf_effect_output_cache_entries", 0
            )
            leaf_effect_cache_entries += child.get("leaf_effect_cache_entries", 0)

    budgeted_cache_entries = int(self.budget.cache_entries)
    algebraic_memo_cache_entries = (
        partition_preimage_map_entries
        + partition_preimage_entries
        + partition_emit_mask_entries
        + symbolic_output_row_entries
        + boundary_anchor_mask_entries
        + boundary_value_mask_entries
    )
    # Persistent effect-owned memo dictionaries.  The BlockContextBudget
    # charges the execution memos inserted through _memo_store(); exact
    # partition/symbolic algebra tables and leaf-effect caches are retained
    # too, but historically were invisible to retained_cache_entries.
    retained_cache_entries = (
        budgeted_cache_entries
        + leaf_effect_cache_entries
        + algebraic_memo_cache_entries
    )
    composed_accounted_entries = (
        output_occupied
        + recursive_value_entries
        + spacetime_tile_advance_entries
        + spacetime_tile_output_entries
    )
    all_accounted_entries = (
        composed_accounted_entries
        + leaf_effect_cache_entries
        + algebraic_memo_cache_entries
    )
    return {
        "operator_nodes": len(seen),
        "operator_node_id_collisions": operator_node_id_collisions,
        "semantic_effect_duplicate_owners": semantic_effect_duplicate_owners,
        "left_boundary_residuals": states[0],
        "right_boundary_residuals": states[1],
        "residual_cache_hits": hits,
        "residual_cache_misses": misses,
        # Historical ``output_cache_*`` names refer only to scalar local
        # ``emit(left,symbol,right)`` memoization.  Keep them for API
        # compatibility, and expose an unambiguous name beside them so
        # callers cannot mistake this for HashLife tile-output reuse.
        "output_cache_hits": output_hits,
        "output_cache_misses": output_misses,
        "output_cache_slots": output_slots,
        "output_cache_occupied": output_occupied,
        "scalar_emit_cache_hits": output_hits,
        "scalar_emit_cache_misses": output_misses,
        "scalar_emit_cache_entries": output_occupied,
        "scalar_emit_compiler_probes": output_uncached_probes,
        "sparse_emit_delegations": sparse_emit_delegations,
        "sparse_emit_first_seen": sparse_emit_first_seen,
        "sparse_emit_admissions": sparse_emit_admissions,
        "sparse_emit_admission_filter_nodes": sparse_emit_admission_filter_nodes,
        "sparse_emit_admission_filter_bits_per_node": 65536,
        "left_transition_entries": transition_entries[0],
        "right_transition_entries": transition_entries[1],
        "finite_kernel_left_states": finite_kernel_states[0],
        "finite_kernel_right_states": finite_kernel_states[1],
        "finite_kernel_storage_bytes": finite_kernel_storage,
        "blank_left_saturation_hits": blank_hits[0],
        "blank_right_saturation_hits": blank_hits[1],
        "residual_cache_dropped_entries": 0,
        "functional_residual_intern_hits": functional_hits,
        "functional_residual_intern_misses": functional_misses,
        "canonical_function_left_states": canonical_function_states[0],
        "canonical_function_right_states": canonical_function_states[1],
        "canonical_partition_left_states": canonical_partition_states[0],
        "canonical_partition_right_states": canonical_partition_states[1],
        "canonical_recursive_left_states": canonical_recursive_states[0],
        "canonical_recursive_right_states": canonical_recursive_states[1],
        "recursive_action_left_nodes": recursive_action_nodes[0],
        "recursive_action_right_nodes": recursive_action_nodes[1],
        "recursive_action_left_max_spatial_extent": recursive_action_max_spatial_extent[
            0
        ],
        "recursive_action_right_max_spatial_extent": recursive_action_max_spatial_extent[
            1
        ],
        "recursive_action_left_max_depth": recursive_action_max_depth[0],
        "recursive_action_right_max_depth": recursive_action_max_depth[1],
        "recursive_state_intern_hits": recursive_state_hits,
        "recursive_state_intern_misses": recursive_state_misses,
        "recursive_action_intern_hits": recursive_action_hits,
        "recursive_action_intern_misses": recursive_action_misses,
        "recursive_value_cache_hits": recursive_value_hits,
        "recursive_value_cache_misses": recursive_value_misses,
        "recursive_value_cache_entries": recursive_value_entries,
        "partition_residual_intern_hits": partition_hits,
        "partition_residual_intern_misses": partition_misses,
        "partition_preimage_cache_hits": partition_preimage_hits,
        "partition_preimage_cache_misses": partition_preimage_misses,
        "partition_preimage_cache_entries": partition_preimage_entries,
        "partition_preimage_map_cache_entries": partition_preimage_map_entries,
        "partition_emit_mask_cache_entries": partition_emit_mask_entries,
        "boundary_anchor_mask_cache_entries": boundary_anchor_mask_entries,
        "boundary_value_mask_cache_entries": boundary_value_mask_entries,
        "symbolic_output_row_cache_hits": symbolic_output_row_hits,
        "symbolic_output_row_cache_misses": symbolic_output_row_misses,
        "symbolic_output_row_cache_entries": symbolic_output_row_entries,
        "symbolic_output_group_evals": symbolic_output_group_evals,
        "boundary_value_index_builds": boundary_value_index_builds,
        "functional_carrier_layers_left": functional_carrier_layers[0],
        "functional_carrier_layers_right": functional_carrier_layers[1],
        "partition_carrier_layers_left": partition_carrier_layers[0],
        "partition_carrier_layers_right": partition_carrier_layers[1],
        "recursive_carrier_layers_left": recursive_carrier_layers[0],
        "recursive_carrier_layers_right": recursive_carrier_layers[1],
        "first_recursive_exponent_left": first_recursive_exponent[0],
        "first_recursive_exponent_right": first_recursive_exponent[1],
        "sparse_carrier_layers_left": sparse_carrier_layers[0],
        "sparse_carrier_layers_right": sparse_carrier_layers[1],
        "first_sparse_exponent_left": first_sparse_exponent[0],
        "first_sparse_exponent_right": first_sparse_exponent[1],
        "max_partition_domain_left": max_partition_domain[0],
        "max_partition_domain_right": max_partition_domain[1],
        "mixed_finite_carrier_layers": mixed_finite_carrier_layers,
        "behavioral_partition_left_aliases": behavioral_aliases[0],
        "behavioral_partition_right_aliases": behavioral_aliases[1],
        "behavioral_partition_left_alias_hits": behavioral_alias_hits[0],
        "behavioral_partition_right_alias_hits": behavioral_alias_hits[1],
        "behavioral_partition_left_refinement_runs": behavioral_refinement_runs[0],
        "behavioral_partition_right_refinement_runs": behavioral_refinement_runs[1],
        "behavioral_partition_left_states": max(
            0, canonical_partition_states[0] - behavioral_aliases[0]
        ),
        "behavioral_partition_right_states": max(
            0, canonical_partition_states[1] - behavioral_aliases[1]
        ),
        "provenance_path_left_states": provenance_path_states[0],
        "provenance_path_right_states": provenance_path_states[1],
        "canonical_program_word_roots": 0,
        # Compatibility metric: the retired raw boundary carrier is gone.
        "canonical_spacetime_boundary_roots": 0,
        "spacetime_tile_output_entries": spacetime_tile_output_entries,
        "spacetime_tile_output_max_level": spacetime_tile_output_max_level,
        "spacetime_temporal_absorption_max": spacetime_temporal_absorption_max,
        "spacetime_tile_advance_cache_hits": spacetime_tile_advance_hits,
        "spacetime_tile_advance_cache_misses": spacetime_tile_advance_misses,
        "spacetime_tile_advance_cache_entries": spacetime_tile_advance_entries,
        "spacetime_boundary_advance_cache_hits": spacetime_boundary_advance_hits,
        "spacetime_boundary_advance_cache_misses": spacetime_boundary_advance_misses,
        "spacetime_boundary_advance_cache_entries": spacetime_boundary_advance_entries,
        "spacetime_reverse_boundary_advance_cache_hits": spacetime_reverse_boundary_advance_hits,
        "spacetime_reverse_boundary_advance_cache_misses": spacetime_reverse_boundary_advance_misses,
        "spacetime_reverse_boundary_advance_cache_entries": spacetime_reverse_boundary_advance_entries,
        "spacetime_tile_output_cache_hits": spacetime_tile_output_hits,
        "spacetime_tile_output_cache_misses": spacetime_tile_output_misses,
        "spacetime_boundary_output_cache_hits": spacetime_boundary_output_hits,
        "spacetime_boundary_output_cache_misses": spacetime_boundary_output_misses,
        "spacetime_boundary_output_cache_entries": spacetime_boundary_output_entries,
        "spacetime_sparse_transition_cache_hits": spacetime_sparse_transition_hits,
        "spacetime_sparse_transition_cache_misses": spacetime_sparse_transition_misses,
        "spacetime_sparse_transition_cache_entries": spacetime_sparse_transition_entries,
        "spacetime_macro_cache_hits": (
            spacetime_tile_advance_hits
            + spacetime_boundary_advance_hits
            + spacetime_reverse_boundary_advance_hits
            + spacetime_tile_output_hits
            + spacetime_boundary_output_hits
            + spacetime_sparse_transition_hits
        ),
        "spacetime_macro_cache_misses": (
            spacetime_tile_advance_misses
            + spacetime_boundary_advance_misses
            + spacetime_reverse_boundary_advance_misses
            + spacetime_tile_output_misses
            + spacetime_boundary_output_misses
            + spacetime_sparse_transition_misses
        ),
        "spacetime_macro_cache_entries": (
            spacetime_tile_advance_entries
            + spacetime_boundary_advance_entries
            + spacetime_reverse_boundary_advance_entries
            + spacetime_tile_output_entries
            + spacetime_boundary_output_entries
            + spacetime_sparse_transition_entries
        ),
        "program_word_intern_hits": 0,
        "program_word_intern_misses": 0,
        "retained_semantic_state_nodes": self.budget.created_nodes,
        "behavioral_semantic_state_nodes": max(
            0, self.budget.created_nodes - behavioral_aliases[0] - behavioral_aliases[1]
        ),
        "retained_execution_nodes": self.budget.created_nodes,
        "behavioral_execution_nodes": max(
            0, self.budget.created_nodes - behavioral_aliases[0] - behavioral_aliases[1]
        ),
        "budgeted_cache_entries": budgeted_cache_entries,
        "algebraic_memo_cache_entries": algebraic_memo_cache_entries,
        "unbudgeted_algebraic_cache_entries": algebraic_memo_cache_entries,
        "leaf_effect_transition_cache_entries": leaf_effect_transition_cache_entries,
        "leaf_effect_output_cache_entries": leaf_effect_output_cache_entries,
        "leaf_effect_cache_entries": leaf_effect_cache_entries,
        "unbudgeted_leaf_cache_entries": leaf_effect_cache_entries,
        # Actual persistent memo dictionaries retained by the complete
        # operator DAG.  ``budgeted_cache_entries`` remains available because
        # the BlockContextBudget governs execution memos inserted through
        # _memo_store(), while exact algebra tables and leaf caches are tracked
        # explicitly as unbudgeted retained structures.
        "retained_cache_entries": retained_cache_entries,
        "raw_spacetime_boundary_cache_entries": (
            spacetime_boundary_advance_entries
            + spacetime_reverse_boundary_advance_entries
            + spacetime_boundary_output_entries
            + spacetime_sparse_transition_entries
        ),
        "budgeted_cache_accounting_delta": (
            budgeted_cache_entries - composed_accounted_entries
        ),
        "retained_cache_accounting_delta": (
            retained_cache_entries - all_accounted_entries
        ),
        "spacetime_tile_advance_repeated_cold_misses": max(
            0, spacetime_tile_advance_misses - spacetime_tile_advance_entries
        ),
        "spacetime_tile_output_repeated_cold_misses": max(
            0, spacetime_tile_output_misses - spacetime_tile_output_entries
        ),
        "scalar_emit_repeated_cold_misses": max(0, output_misses - output_occupied),
        "recursive_value_repeated_cold_misses": max(
            0, recursive_value_misses - recursive_value_entries
        ),
    }


__all__ = ["composed_runtime_stats"]

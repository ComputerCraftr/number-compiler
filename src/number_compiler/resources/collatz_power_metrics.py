"""Demanded metric view; importing a term does not construct this schema."""

from dataclasses import dataclass

from number_compiler.resources.metric_records import LedgerMetrics


@dataclass(frozen=True, slots=True)
class CollatzPhysicalBlockMetrics(LedgerMetrics):
    seed: int
    steps: int
    operator_nodes: int
    compose_operations: int
    syntax_depth_bound: int
    descriptor_bits: int
    point_queries: int
    retained_execution_nodes: int
    canonical_program_word_roots: int
    left_boundary_residuals: int
    right_boundary_residuals: int
    direct_powered_point_queries: int
    temporal_leaf_applications: int
    collatz_physical_factored_output_compilations: int = 0
    collatz_physical_joint_output_tables_elided: int = 0
    canonical_spacetime_macrocell_roots: int = 0
    spacetime_tile_output_entries: int = 0
    spacetime_tile_output_max_level: int = 0
    spacetime_temporal_absorption_max: int = 0
    high_level_tile_hits: int = 0
    high_level_tile_misses: int = 0
    retained_cache_entries: int = 0
    raw_spacetime_boundary_cache_entries: int = 0
    retained_cache_accounting_delta: int = 0
    spacetime_macro_cache_hits: int = 0
    spacetime_macro_cache_misses: int = 0
    spacetime_macro_cache_entries: int = 0
    spacetime_tile_advance_cache_hits: int = 0
    spacetime_tile_advance_cache_misses: int = 0
    spacetime_tile_advance_cache_entries: int = 0
    spacetime_tile_output_cache_hits: int = 0
    spacetime_tile_output_cache_misses: int = 0
    spacetime_boundary_advance_cache_hits: int = 0
    spacetime_boundary_advance_cache_misses: int = 0
    spacetime_boundary_advance_cache_entries: int = 0
    spacetime_reverse_boundary_advance_cache_hits: int = 0
    spacetime_reverse_boundary_advance_cache_misses: int = 0
    spacetime_reverse_boundary_advance_cache_entries: int = 0
    spacetime_boundary_output_cache_hits: int = 0
    spacetime_boundary_output_cache_misses: int = 0
    spacetime_boundary_output_cache_entries: int = 0
    spacetime_sparse_transition_cache_hits: int = 0
    spacetime_sparse_transition_cache_misses: int = 0
    spacetime_sparse_transition_cache_entries: int = 0
    scalar_emit_cache_hits: int = 0
    scalar_emit_cache_misses: int = 0
    scalar_emit_cache_entries: int = 0
    scalar_emit_compiler_probes: int = 0
    canonical_tile_arena_nodes: int = 0
    canonical_tile_intern_hits: int = 0
    canonical_tile_intern_misses: int = 0
    canonical_tile_mirror_hits: int = 0
    canonical_tile_mirror_misses: int = 0
    total_hashlife_retained_entries: int = 0
    canonical_function_left_states: int = 0
    canonical_function_right_states: int = 0
    canonical_partition_left_states: int = 0
    canonical_partition_right_states: int = 0
    canonical_recursive_left_states: int = 0
    canonical_recursive_right_states: int = 0
    recursive_action_left_nodes: int = 0
    recursive_action_right_nodes: int = 0
    recursive_state_intern_hits: int = 0
    recursive_state_intern_misses: int = 0
    recursive_action_intern_hits: int = 0
    recursive_action_intern_misses: int = 0
    recursive_value_cache_hits: int = 0
    recursive_value_cache_misses: int = 0
    recursive_value_cache_entries: int = 0
    partition_preimage_cache_hits: int = 0
    partition_preimage_cache_misses: int = 0
    symbolic_output_row_cache_hits: int = 0
    symbolic_output_row_cache_misses: int = 0
    symbolic_output_row_cache_entries: int = 0
    symbolic_output_group_evals: int = 0
    boundary_value_index_builds: int = 0
    functional_carrier_layers_left: int = 0
    functional_carrier_layers_right: int = 0
    partition_carrier_layers_left: int = 0
    partition_carrier_layers_right: int = 0
    recursive_carrier_layers_left: int = 0
    recursive_carrier_layers_right: int = 0
    first_recursive_exponent_left: int = 0
    first_recursive_exponent_right: int = 0
    sparse_carrier_layers_left: int = 0
    sparse_carrier_layers_right: int = 0
    first_sparse_exponent_left: int = 0
    first_sparse_exponent_right: int = 0
    max_partition_domain_left: int = 0
    max_partition_domain_right: int = 0
    mixed_finite_carrier_layers: int = 0
    compiler_retained_execution_nodes: int = 0
    query_retained_execution_nodes: int = 0
    compiler_retained_cache_entries: int = 0
    query_retained_cache_entries: int = 0
    budgeted_cache_entries: int = 0
    leaf_effect_cache_entries: int = 0
    source_index_cache_entries: int = 0
    finite_action_cache_entries: int = 0
    canonical_tile_arena_nodes_global: int = 0
    canonical_tile_arena_nodes_index_build: int = 0
    canonical_tile_arena_nodes_query: int = 0
    canonical_tile_intern_hits_index_build: int = 0
    canonical_tile_intern_misses_index_build: int = 0
    canonical_tile_mirror_hits_index_build: int = 0
    canonical_tile_mirror_misses_index_build: int = 0
    canonical_tile_intern_hits_query: int = 0
    canonical_tile_intern_misses_query: int = 0
    canonical_tile_mirror_hits_query: int = 0
    canonical_tile_mirror_misses_query: int = 0
    canonical_tile_node_id_collisions: int = 0
    canonical_tile_invalid_intern_entries: int = 0
    canonical_tile_mirror_involution_violations: int = 0
    operator_node_id_collisions: int = 0
    semantic_effect_duplicate_owners: int = 0
    compiler_recursive_state_intern_hits: int = 0
    compiler_recursive_state_intern_misses: int = 0
    compiler_recursive_action_intern_hits: int = 0
    compiler_recursive_action_intern_misses: int = 0
    compiler_recursive_value_cache_hits: int = 0
    compiler_recursive_value_cache_misses: int = 0
    compiler_recursive_value_cache_entries: int = 0
    compiler_partition_preimage_cache_hits: int = 0
    compiler_partition_preimage_cache_misses: int = 0
    compiler_partition_preimage_cache_entries: int = 0
    compiler_symbolic_output_row_cache_hits: int = 0
    compiler_symbolic_output_row_cache_misses: int = 0
    compiler_symbolic_output_row_cache_entries: int = 0
    compiler_symbolic_output_group_evals: int = 0
    spacetime_tile_advance_repeated_cold_misses: int = 0
    spacetime_tile_output_repeated_cold_misses: int = 0
    scalar_emit_repeated_cold_misses: int = 0
    recursive_value_repeated_cold_misses: int = 0
    algebraic_memo_cache_entries: int = 0
    compiler_algebraic_memo_cache_entries: int = 0
    query_algebraic_memo_cache_entries: int = 0
    partition_preimage_cache_entries: int = 0
    partition_preimage_map_cache_entries: int = 0
    partition_emit_mask_cache_entries: int = 0
    boundary_anchor_mask_cache_entries: int = 0
    boundary_value_mask_cache_entries: int = 0
    compiler_partition_preimage_map_cache_entries: int = 0
    compiler_partition_emit_mask_cache_entries: int = 0
    compiler_boundary_anchor_mask_cache_entries: int = 0
    compiler_boundary_value_mask_cache_entries: int = 0
    bounded_application_enabled: int = 0
    bounded_application_temporal_state_classes: int = 0
    bounded_application_temporal_action_classes: int = 0
    bounded_application_exact_spatial_occurrences: int = 0
    bounded_application_symbolic_action_nodes: int = 0
    bounded_application_jump_entries: int = 0
    bounded_application_primitive_step_evaluations: int = 0
    bounded_application_action_compositions: int = 0
    bounded_application_action_applications: int = 0
    bounded_application_nonlinear_branch_evaluations: int = 0
    bounded_application_exact_endpoint_entries: int = 0
    bounded_application_query_requests: int = 0
    bounded_application_quotient_builds: int = 0
    bounded_application_residual_physical_steps: int = 0
    bounded_application_retained_entries: int = 0

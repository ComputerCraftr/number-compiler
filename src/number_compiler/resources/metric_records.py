"""Public metric records for the HashLife projection engine.

Kept separate from :mod:`hashlife_projection` so instrumentation does not
inflate the hot projection module or blur execution logic with reporting.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from number_compiler.resources.ledger import ResourceInventory
from number_compiler.resources.temporal_diagnostics import (
    METRICS_SCHEMA_VERSION,
    TemporalExecutionDiagnostics,
)


@dataclass(frozen=True, slots=True, kw_only=True)
class LedgerMetrics:
    """Schema-eight accounting with a typed temporal diagnostic view."""

    metrics_schema_version: int = METRICS_SCHEMA_VERSION
    temporal_diagnostics: TemporalExecutionDiagnostics = field(
        default_factory=TemporalExecutionDiagnostics
    )
    tile_representation_policy: str = "canonical-future-tiles-and-boundary-operands-v2"
    future_behavior_profile_nodes: int = 0
    future_behavior_class_nodes: int = 0
    future_behavior_requests: int = 0
    future_behavior_early_hits: int = 0
    future_behavior_binding_requests: int = 0
    future_behavior_binding_early_hits: int = 0
    future_behavior_publication_requests: int = 0
    future_behavior_binding_publications: int = 0
    future_behavior_aliases: int = 0
    future_behavior_publication_failures: int = 0
    future_behavior_new_classes: int = 0
    future_behavior_profile_early_hits: int = 0
    future_behavior_classification_evaluations: int = 0
    future_behavior_classification_work: int = 0
    future_behavior_refinement_observation_checks: int = 0
    future_behavior_refinement_successor_checks: int = 0
    behavior_classification_summary_checks: int = 0
    behavior_classification_port_checks: int = 0
    behavior_point_observations: int = 0
    behavior_width_observations: int = 0
    exact_causal_fallback_requests: int = 0
    causal_extent_discharged_by_behavior: int = 0
    tile_causal_quiescent_boundary_reuses: int = 0
    tile_region_normalization_requests: int = 0
    tile_region_normalization_misses: int = 0
    tile_region_normalization_early_hits: int = 0
    tile_region_normalization_publication_requests: int = 0
    tile_region_normalization_publications: int = 0
    tile_region_normalization_late_duplicates: int = 0
    tile_region_application_validation_visits: int = 0
    normalized_region_entries: int = 0
    canonical_tile_nodes: int = 0
    canonical_tile_peak: int = 0
    tile_alphabet_nodes: int = 0
    tile_root_leases: int = 0
    pinned_completed_roots: int = 0
    tile_root_lease_peak: int = 0
    tile_child_reverse_index_entries: int = 0
    completed_result_entries: int = 0
    tile_execution_memo_entries: int = 0
    powered_interface_entries: int = 0
    spatial_interface_composition_entries: int = 0
    spatial_interface_composition_requests: int = 0
    spatial_interface_composition_early_hits: int = 0
    spatial_interface_composition_late_aliases: int = 0
    spatial_interface_composition_publications: int = 0
    spatial_interface_composition_publication_requests: int = 0
    fused_interface_entries: int = 0
    fused_interface_requests: int = 0
    fused_interface_early_hits: int = 0
    fused_interface_publications: int = 0
    fused_interface_publication_requests: int = 0
    fused_interface_late_aliases: int = 0
    tile_fused_frames: int = 0
    tile_fused_leaf_evaluations: int = 0
    tile_fused_observation_descents: int = 0
    tile_fused_workspace_peak: int = 0
    tile_fused_observation_requests: int = 0
    powered_absorption_requests: int = 0
    powered_absorption_early_hits: int = 0
    powered_absorption_evaluations: int = 0
    powered_absorption_successes: int = 0
    powered_absorption_max_span: int = 0
    proof_artifact_builds: int = 0
    proof_artifact_hits: int = 0
    proof_artifact_loading_work: int = 0
    proof_artifact_build_failures: int = 0
    proof_artifact_loading_failures: int = 0
    powered_interface_requests: int = 0
    powered_interface_early_hits: int = 0
    powered_interface_publications: int = 0
    powered_interface_publication_requests: int = 0
    powered_interface_late_aliases: int = 0
    completed_result_reverse_index_entries: int = 0
    completed_result_variant_entries: int = 0
    completed_result_port_variants_peak: int = 0
    completed_result_port_validation_requests: int = 0
    completed_result_port_validation_visits: int = 0
    boundary_tile_operand_references: int = 0
    boundary_tile_unique_live: int = 0
    boundary_tile_leases: int = 0
    boundary_tile_lease_peak: int = 0
    boundary_tile_operand_extent_total: int = 0
    boundary_tile_operand_source_offset_total: int = 0
    boundary_tile_memo_operand_references: int = 0
    boundary_tile_leased_operand_references: int = 0
    boundary_tile_leased_operand_unique_live: int = 0
    tile_boundary_transfer_requests: int = 0
    tile_boundary_transfer_frames: int = 0
    tile_boundary_transfer_parent_observations: int = 0
    tile_boundary_transfer_descents: int = 0
    tile_boundary_transfer_workspace_peak: int = 0
    tile_width_descents: int = 0
    tile_source_imports: int = 0
    tile_endpoint_projection_descents: int = 0
    tile_endpoint_emissions: int = 0
    tile_projection_width_observations: int = 0
    tile_radix_stage_publications: int = 0
    tile_radix_digit_observations: int = 0
    tile_temporal_action_hits: int = 0
    tile_temporal_action_publications: int = 0
    tile_temporal_action_semantic_alias_hits: int = 0
    # Compiler publication work. This does not claim a scheduler sector
    # evaluation or a source-annihilation observation.
    reverse_frobenius_plan_compositions: int = 0
    reverse_frobenius_retained_component_nodes: int = 0
    reverse_field_action_source_annihilation_derivations: int = 0
    collatz_field_action_source_annihilation_derivations: int = 0
    tile_temporal_complete_compositions: int = 0
    tile_temporal_complete_frames: int = 0
    tile_scheduler_direct_requests: int = 0
    tile_scheduler_sibling_transfer_requests: int = 0
    tile_scheduler_sibling_transfer_evaluations: int = 0
    tile_scheduler_demanded_result_pins: int = 0
    primitive_tile_interface_publications: int = 0
    tile_leaf_product_requests: int = 0
    tile_leaf_product_early_hits: int = 0
    tile_leaf_product_evaluations: int = 0
    tile_leaf_product_publications: int = 0
    tile_leaf_product_late_aliases: int = 0
    tile_application_result_pins: int = 0
    completed_result_requests: int = 0
    completed_result_publication_requests: int = 0
    completed_result_evaluations: int = 0
    completed_result_late_duplicate_reductions: int = 0
    completed_result_early_hits: int = 0
    completed_result_publications: int = 0
    completed_result_tile_retirements: int = 0
    completed_result_evictions: int = 0
    completed_result_evicted_entries: int = 0
    completed_result_retirement_memo_removals: int = 0
    completed_result_reverse_index_removals: int = 0
    completed_result_presence_index_visits: int = 0
    completed_result_retirement_traversal_steps: int = 0
    completed_result_eviction_reverse_index_entries: int = 0
    completed_result_recomputation_attribution_unknown: int = 0
    result_cache_kind_classification_visits: int = 0
    result_cache_result_evicted_entries: int = 0
    result_cache_interface_evicted_entries: int = 0
    result_cache_behavior_evicted_entries: int = 0
    result_cache_region_evicted_entries: int = 0
    result_cache_spatial_evicted_entries: int = 0
    result_cache_result_retirement_removals: int = 0
    result_cache_interface_retirement_removals: int = 0
    result_cache_behavior_retirement_removals: int = 0
    result_cache_region_retirement_removals: int = 0
    result_cache_spatial_retirement_removals: int = 0
    result_cache_result_post_eviction_misses_attribution_unknown: int = 0
    result_cache_interface_post_eviction_misses_attribution_unknown: int = 0
    result_cache_behavior_post_eviction_misses_attribution_unknown: int = 0
    result_cache_region_post_eviction_misses_attribution_unknown: int = 0
    result_cache_spatial_post_eviction_misses_attribution_unknown: int = 0
    tile_intern_requests: int = 0
    tile_intern_early_hits: int = 0
    tile_mirror_requests: int = 0
    tile_mirror_early_hits: int = 0
    tile_mirror_evaluations: int = 0
    tile_mirror_publications: int = 0
    tile_mirror_relation_entries: int = 0
    tile_publications: int = 0
    tile_retirements: int = 0
    tile_retirement_work_ns: int = 0
    python_gc_collections_during_tile_retirement: int = 0
    python_gc_collected_during_tile_retirement: int = 0
    python_gc_uncollectable_during_tile_retirement: int = 0
    tile_recreation_attribution_unknown: int = 0
    cache_events_by_spatial_level: dict[str, int] = field(default_factory=dict)
    cache_events_by_temporal_span: dict[str, int] = field(default_factory=dict)
    cache_event_histogram_dropped: int = 0
    cache_event_histogram_capacity: int = 1_024
    tile_lease_acquisitions: int = 0
    tile_lease_releases: int = 0
    tile_observation_descents: int = 0
    tile_scheduler_frames: int = 0
    tile_scheduler_demand_descents: int = 0
    tile_scheduler_width_descents: int = 0
    tile_scheduler_parent_early_hits: int = 0
    tile_scheduler_demand_parent_hits: int = 0
    tile_scheduler_demand_parent_misses: int = 0
    tile_scheduler_midpoint_hits: int = 0
    tile_scheduler_fused_requests: int = 0
    tile_scheduler_temporal_complete_requests: int = 0
    tile_scheduler_leaf_function_applications: int = 0
    tile_scheduler_spatial_compositions: int = 0
    tile_scheduler_workspace_peak: int = 0
    microblock_representation_policy: str = (
        "capped-leaf-64bits-1024blocks-8192bytes-transient256bytes-v1"
    )
    # Policy permission is not implementation evidence. Populations and work
    # below are observed independently; no cache is enabled by this record.
    exact_microblock_nodes: int = 0
    exact_microblock_entries: int = 0
    semantic_function_nodes: int = 0
    diamond_quotient_nodes: int = 0
    semantic_signature_nodes: int = 0
    field_action_nodes: int = 0
    field_geometry_nodes: int = 0
    algebraic_component_nodes: int = 0
    primitive_behavioral_quotient_nodes: int = 0
    production_residual_state_nodes: int = 0
    production_residual_state_classes: int = 0
    algebraic_instrumentation_complete: int = 0
    temporal_parent_requests: int = 0
    temporal_parent_early_hits: int = 0
    temporal_parent_compositions: int = 0
    temporal_parent_late_duplicate_reductions: int = 0
    radial_action_operations: int = 0
    carry_action_operations: int = 0
    character_action_operations: int = 0
    affine_action_operations: int = 0
    innovation_action_operations: int = 0
    output_morphism_operations: int = 0
    residual_refinement_operations: int = 0
    source_annihilations: int = 0
    root_germ_skips: int = 0
    whole_word_sweeps: int = 0
    whole_word_symbol_visits: int = 0
    proof_machine_applications: int = 0
    spatial_descents: int = 0
    canonical_expression_node_visits: int = 0
    field_action_component_operations: int = 0
    post_publish_equivalence_merges: int = 0
    point_observations: int = 0
    width_observations: int = 0
    higher_point_observations: int = 0
    higher_width_observations: int = 0
    higher_observation_fallback: int = 0
    higher_range_dyadic_cells: int = 0
    higher_concrete_operation_evaluations: int = 0
    higher_concrete_operation_hits: int = 0
    higher_concrete_initial_evaluations: int = 0
    higher_concrete_step_evaluations: int = 0
    higher_concrete_emit_evaluations: int = 0
    higher_concrete_apply_evaluations: int = 0
    higher_concrete_force_evaluations: int = 0
    higher_primitive_step_hits: int = 0
    higher_primitive_step_publications: int = 0
    higher_primitive_output_hits: int = 0
    higher_primitive_output_publications: int = 0
    higher_summary_temporal_compositions: int = 0
    higher_summary_spatial_compositions: int = 0
    higher_context_spatial_compositions: int = 0
    reverse_temporal_leaf_substitutions: int = 0
    reverse_temporal_parent_substitutions: int = 0
    reverse_temporal_prefix_image_observations: int = 0
    collatz_temporal_leaf_substitutions: int = 0
    collatz_temporal_parent_substitutions: int = 0
    collatz_temporal_prefix_image_observations: int = 0
    collatz_complete_leaf_interface_observations: int = 0
    collatz_complete_leaf_interface_early_hits: int = 0
    collatz_source_root_match_requests: int = 0
    collatz_source_root_match_early_hits: int = 0
    collatz_source_root_match_evaluations: int = 0
    collatz_source_root_match_publications: int = 0
    collatz_source_root_match_late_duplicates: int = 0
    opaque_higher_operation_publications: int = 0
    higher_operation_early_hits: int = 0
    radix_observations: int = 0
    tile_radix_affine_compositions: int = 0
    tile_radix_activation_compositions: int = 0
    tile_radix_algebraic_observations: int = 0
    tile_radix_arithmetic_parent_interfaces: int = 0
    quotient_arithmetic_normalizations: int = 0
    reverse_port_function_observations: int = 0
    reverse_port_function_compositions: int = 0
    reverse_port_primitive_output_evaluations: int = 0
    reverse_port_parent_interfaces: int = 0
    reverse_port_carry_compositions: int = 0
    reverse_port_predicate_state_evaluations: int = 0
    reverse_port_construction_workspace_peak: int = 0
    reverse_active_transfer_evaluations: int = 0
    reverse_active_transfer_declines: int = 0
    reverse_boundary_transfer_publications: int = 0
    reverse_boundary_transfer_completions: int = 0
    reverse_boundary_extent_discharged: int = 0
    reverse_bound_output_requests: int = 0
    reverse_bound_output_early_hits: int = 0
    reverse_bound_output_evaluations: int = 0
    reverse_bound_output_failures: int = 0
    reverse_bound_output_publication_requests: int = 0
    reverse_bound_output_publications: int = 0
    reverse_bound_output_late_duplicates: int = 0
    reverse_bound_output_leaf_evaluations: int = 0
    reverse_bound_output_parent_compositions: int = 0
    reverse_bound_output_evictions: int = 0
    reverse_bound_output_post_eviction_misses_attribution_unknown: int = 0
    reverse_interval_forcing_requests: int = 0
    reverse_interval_forcing_failures: int = 0
    reverse_interval_forcing_evaluations: int = 0
    reverse_interval_observation_requests: int = 0
    reverse_interval_observation_failures: int = 0
    reverse_interval_observation_evaluations: int = 0
    reverse_sector_product_source_elisions: int = 0
    tile_causal_interface_primitive_parent_shortcuts: int = 0
    tile_causal_interface_midpoint_reuse: int = 0
    tile_causal_interface_midpoint_publications: int = 0
    tile_causal_direct_parent_transfers: int = 0
    tile_causal_midpoint_port_reuses: int = 0
    tile_boundary_concat_cache_requests: int = 0
    tile_boundary_concat_cache_misses: int = 0
    tile_boundary_concat_cache_early_hits: int = 0
    tile_boundary_concat_cache_evaluations: int = 0
    tile_boundary_concat_cache_failures: int = 0
    tile_boundary_concat_cache_publication_requests: int = 0
    tile_boundary_concat_cache_publications: int = 0
    tile_boundary_concat_cache_late_duplicates: int = 0
    tile_boundary_concat_application_validation_visits: int = 0
    tile_boundary_concat_backing_hits: int = 0
    reverse_sector_width_observations: int = 0
    reverse_port_retained_coefficient_slots: int = 0
    reverse_port_retained_limb_slots: int = 0
    reverse_sector_retained_slots: int = 0
    reverse_port_unique_live_function_objects: int = 0
    reverse_port_unique_live_coefficient_slots: int = 0
    reverse_port_unique_live_limb_slots: int = 0
    reverse_sector_unique_live_objects: int = 0
    reverse_sector_unique_live_slots: int = 0
    reverse_sector_compose_requests: int = 0
    reverse_sector_compose_failures: int = 0
    reverse_sector_compose_evaluations: int = 0
    reverse_sector_component_outputs: int = 0
    reverse_sector_ring_scalar_operations: int = 0
    reverse_sector_carry_input_evaluations: int = 0
    reverse_sector_product_observation_requests: int = 0
    reverse_sector_product_observation_failures: int = 0
    reverse_sector_product_observation_evaluations: int = 0
    reverse_sector_product_action_spine_visits: int = 0
    reverse_sector_product_arithmetic_evaluations: int = 0
    reverse_sector_product_sector_evaluations: int = 0
    quotient_publication_failures: int = 0
    quotient_atomic_mask_elisions: int = 0
    quotient_atomic_mask_validation_nodes: int = 0
    semantic_bit_boolean_identity_reductions: int = 0
    semantic_bit_boolean_absorption_reductions: int = 0
    tile_spatial_identity_substitutions_elided: int = 0
    original_affine_summary_requests: int = 0
    original_affine_summary_hits: int = 0
    original_affine_summary_publications: int = 0
    original_affine_summary_failures: int = 0
    original_affine_summary_source_cells: int = 0
    original_affine_summary_parent_cells: int = 0
    original_affine_summary_division_cells: int = 0
    original_affine_summary_transition_evaluations: int = 0
    original_affine_prefix_summary_visits: int = 0
    original_affine_shift_summary_visits: int = 0
    original_affine_summary_limb_operations: int = 0
    original_affine_shift_compositions: int = 0
    original_affine_summary_workspace_slots_peak: int = 0
    radix_original_affine_digit_queries: int = 0
    radix_original_affine_carry_cells: int = 0
    radix_fixed_cycle_observations: int = 0
    radix_provider_digit_requests: int = 0
    radix_provider_digit_early_hits: int = 0
    radix_provider_digit_evaluations: int = 0
    radix_temporal_action_requests: int = 0
    radix_temporal_action_early_hits: int = 0
    radix_temporal_action_evaluations: int = 0
    radix_recursive_transfer_requests: int = 0
    radix_recursive_transfer_early_hits: int = 0
    radix_recursive_transfer_evaluations: int = 0
    radix_recursive_descents: int = 0
    radix_source_bit_visits: int = 0
    radix_limb_operations: int = 0
    endpoint_emissions: int = 0
    field_action_publications: int = 0
    output_morphism_publications: int = 0
    image_publications: int = 0
    # Direct schema-seven spellings of the recursive-image runtime instruments.
    # The older normalized aliases below remain for compatibility.
    new_field_image_nodes: int = 0
    field_image_binding_requests: int = 0
    field_image_binding_early_hits: int = 0
    # M(N, X): canonical recursive field images newly published by this index.
    new_canonical_field_images_published: int = 0
    field_image_publication_requests: int = 0
    field_image_early_hits: int = 0
    field_image_parent_observation_requests: int = 0
    field_image_parent_observation_early_hits: int = 0
    field_image_parent_observation_evaluations: int = 0
    provider_fused_point_requests: int = 0
    provider_fused_point_early_hits: int = 0
    provider_fused_point_evaluations: int = 0
    provider_fused_width_requests: int = 0
    provider_fused_width_early_hits: int = 0
    provider_fused_width_evaluations: int = 0
    concrete_port_task_frames: int = 0
    concrete_irrelevant_port_elisions: int = 0
    temporal_leaf_diamond_descents: int = 0
    higher_semantic_evaluations: int = 0
    higher_semantic_task_frames: int = 0
    higher_action_continuation_requests: int = 0
    temporal_leaf_parent_hits: int = 0
    temporal_leaf_parent_publications: int = 0
    higher_identity_transfer_elisions: int = 0
    generic_higher_action_early_hits: int = 0
    generic_higher_action_publications: int = 0
    parametric_width_forest_visits: int = 0
    parametric_width_parent_visits: int = 0
    parametric_width_descent_steps: int = 0
    parametric_width_contexts_peak: int = 0
    higher_boundary_resolution_hits: int = 0
    higher_runtime_composition_requests: int = 0
    higher_runtime_composition_hits: int = 0
    higher_runtime_interchange_compositions: int = 0
    higher_finite_transfer_state_visits: int = 0
    higher_finite_transfer_evaluations: int = 0
    higher_finite_transfer_compositions: int = 0
    endpoint_mirror_reuses: int = 0
    endpoint_mirror_buffer_peak_bytes: int = 0
    concrete_provider_layer_publications: int = 0
    concrete_provider_layer_alias_hits: int = 0
    concrete_port_task_requests: int = 0
    concrete_port_task_early_hits: int = 0
    concrete_port_task_evaluations: int = 0
    concrete_virtual_interface_requests: int = 0
    concrete_virtual_interface_early_hits: int = 0
    concrete_virtual_interface_evaluations: int = 0
    concrete_virtual_interface_publications: int = 0
    concrete_virtual_interface_alias_hits: int = 0
    recursive_field_image_requests: int = 0
    recursive_field_image_early_hits: int = 0
    recursive_field_image_temporal_compositions: int = 0
    recursive_field_image_spatial_compositions: int = 0
    recursive_field_image_primitive_evaluations: int = 0
    recursive_field_forest_requests: int = 0
    recursive_field_forest_early_hits: int = 0
    recursive_field_forest_spatial_compositions: int = 0
    recursive_field_forest_primitive_evaluations: int = 0
    field_interface_publications: int = 0
    field_interface_early_hits: int = 0
    field_image_nodes: int = 0
    field_interface_nodes: int = 0
    source_cell_nodes: int = 0
    image_input_reference_nodes: int = 0
    runtime_query_state_nodes: int = 0
    runtime_query_environment_nodes: int = 0
    runtime_operation_memo_entries: int = 0
    field_transfer_nodes: int = 0
    field_transfer_binding_entries: int = 0
    recursive_field_image_nodes: int = 0
    local_interface_nodes: int = 0
    output_morphism_nodes: int = 0
    new_field_transfer_nodes: int = 0
    field_transfer_binding_requests: int = 0
    field_transfer_binding_early_hits: int = 0
    field_transfer_binding_publications: int = 0
    field_transfer_semantic_alias_hits: int = 0
    local_interface_compositions: int = 0
    local_interface_alias_hits: int = 0
    output_morphism_visits: int = 0
    total_internal_action_work: int = 0
    collatz_radix_boundary_validation_requests: int = 0
    collatz_radix_boundary_validation_visits: int = 0
    collatz_radix_boundary_proof_hits: int = 0
    collatz_radix_boundary_proof_publications: int = 0
    microblock_publications: int = 0
    microblock_payload_bytes: int = 0
    microblock_payload_high_water_bytes: int = 0
    microblock_entry_high_water: int = 0
    source_leaf_visits: int = 0
    transient_buffer_allocations: int = 0
    transient_buffer_bytes_peak: int = 0
    proof_machine_artifacts_loaded_by_runtime: int = 0
    extensional_family_executor_instances: int = 0
    algebraic_executor_capability_validated: int = 0
    nonlinear_branch_evaluations: int = 0
    # Fixed original-interface certificate slots, not bytes or extra node terms.
    reachable_profile_definition_records: int = 0
    reachable_profile_definition_integer_slots: int = 0
    reachable_profile_codec_records: int = 0
    reachable_profile_decoder_cache_entries: int = 0
    # Complete primitive-cell requests, independent from quotient reduction hits.
    primitive_macro_requests: int = 0
    primitive_macro_early_hits: int = 0
    primitive_macro_evaluations: int = 0
    primitive_macro_compilations: int = 0
    primitive_macro_source_frames: int = 0
    primitive_macro_spatial_compositions: int = 0
    primitive_macro_observation_requests: int = 0
    primitive_macro_observation_evaluations: int = 0
    primitive_macro_cache_entries: int = 0
    primitive_behavioral_class_population: int = 0
    primitive_occurrence_observation_evaluations: int = 0
    primitive_behavior_refinement_observation_checks: int = 0
    primitive_behavior_refinement_successor_checks: int = 0
    semantic_structure_declaration_requests: int = 0
    semantic_structure_declaration_identity_hits: int = 0
    semantic_structure_declaration_early_hits: int = 0
    semantic_structure_declaration_evaluations: int = 0
    semantic_structure_declaration_cache_entries: int = 0
    quotient_parent_requests: int = 0
    quotient_parent_early_hits: int = 0
    quotient_parent_publications: int = 0
    quotient_complete_normalizations: int = 0
    # Validated canonical-record reuse before totality checks or rewriting.
    quotient_normal_form_early_hits: int = 0
    quotient_semantic_interner_evaluations: int = 0
    quotient_semantic_interner_hits: int = 0
    semantic_function_requests: int = 0
    semantic_function_request_hits: int = 0
    semantic_function_evaluations: int = 0
    semantic_function_decision_visits: int = 0
    semantic_function_ite_frames: int = 0
    semantic_function_rewrite_frames: int = 0
    semantic_function_staged_nodes: int = 0
    semantic_function_published_nodes: int = 0
    semantic_bit_admissibility_requests: int = 0
    semantic_bit_admissibility_early_hits: int = 0
    semantic_bit_admissibility_evaluations: int = 0
    semantic_bit_admissibility_publications: int = 0
    semantic_expression_tasks: int = 0
    semantic_expression_finite_lift_requests: int = 0
    semantic_expression_finite_lift_hits: int = 0
    semantic_expression_finite_lift_evaluations: int = 0
    semantic_expression_finite_lift_frames: int = 0
    semantic_binary_division_compilations: int = 0
    resource_ledger_entries: int = 0
    resource_ledger_nodes: int = 0
    resource_peak_entries: int = 0
    resource_peak_nodes: int = 0
    resource_observed_entries: int = 0
    resource_observed_nodes: int = 0
    resource_unregistered_containers: int = 0
    resource_unregistered_payload_resolvers: int = 0
    resource_accounting_mismatch: int = 0
    resource_inventory: tuple[ResourceInventory, ...] = ()
    resource_work_counters: dict[str, int] = field(default_factory=dict)
    # Named component high-water marks, never summed into an invented total.
    # Values count the unit named by their key, not bytes or arithmetic bits.
    resource_workspace_peaks: dict[str, int] = field(default_factory=dict)
    finite_port_applications: int = 0
    finite_port_decision_visits: int = 0
    reverse_carry_function_classifications: int = 0
    representation_boundary_complete: int = 0
    bimachine_composition_certified: int = 0
    diamond_cache_entries: int = 0
    macro_transfer_requests: int = 0
    macro_transfer_cache_hits: int = 0
    macro_transfer_evaluations: int = 0
    macro_transfer_cache_entries: int = 0
    # This memo canonicalizes parent syntax. A hit skips identity construction,
    # not boundary-function execution or observation.
    image_program_requests: int = 0
    image_program_cache_hits: int = 0
    image_program_evaluations: int = 0
    image_program_cache_entries: int = 0
    canonical_parent_identity_entries: int = 0
    boundary_substitution_requests: int = 0
    boundary_substitution_cache_hits: int = 0
    boundary_substitution_evaluations: int = 0
    boundary_substitution_cache_entries: int = 0
    spatial_parent_requests: int = 0
    spatial_parent_cache_hits: int = 0
    spatial_parent_evaluations: int = 0
    spatial_parent_cache_entries: int = 0
    primitive_transition_evaluations: int = 0
    primitive_output_evaluations: int = 0
    scalar_observation_requests: int = 0
    sequential_generation_advances: int = 0
    scheduler_transitions: int = 0
    scheduler_workspace_peak: int = 0
    # Disjoint node categories reconcile resource_observed_nodes. Container
    # slots are another resource dimension and must never be added to nodes.
    cache_slots: int = 0
    exact_source_occurrences: int = 0
    spatial_occurrence_bindings: int = 0
    spatial_binding_nodes: int = 0
    reverse_leaf_binding_entries: int = 0
    reverse_parent_binding_entries: int = 0
    reverse_source_tile_binding_entries: int = 0
    collatz_range_binding_entries: int = 0
    collatz_source_tile_binding_entries: int = 0
    collatz_event_binding_entries: int = 0
    canonical_transfer_nodes: int = 0
    # Syntax-canonical complete spatial programs; not reduced extensional classes.
    spatial_action_program_nodes: int = 0
    primitive_spatial_requests: int = 0
    primitive_spatial_cache_hits: int = 0
    primitive_spatial_evaluations: int = 0
    primitive_spatial_observations: int = 0
    primitive_spatial_cache_entries: int = 0
    image_action_nodes: int = 0
    diamond_cell_nodes: int = 0
    # Typed-record subsets of the node partition, not extra partition terms.
    boundary_state_nodes: int = 0
    boundary_function_nodes: int = 0
    primitive_kernel_nodes: int = 0
    finite_expression_nodes: int = 0
    macro_transfer_action_nodes: int = 0
    context_program_nodes: int = 0
    boundary_expression_program_nodes: int = 0
    boundary_expression_free_port_references: int = 0
    boundary_expression_max_free_ports: int = 0
    higher_context_program_nodes: int = 0
    higher_unary_program_nodes: int = 0
    higher_observation_cache_entries: int = 0
    expression_closure_program_nodes: int = 0
    expression_closure_parameter_references: int = 0
    expression_call_argument_references: int = 0
    expression_head_cache_entries: int = 0
    context_observation_cache_entries: int = 0
    unary_function_cache_entries: int = 0
    context_observation_requests: int = 0
    context_observation_cache_hits: int = 0
    context_observation_evaluations: int = 0
    unary_function_composition_requests: int = 0
    unary_function_composition_hits: int = 0
    unary_function_composition_evaluations: int = 0
    unary_kernel_application_requests: int = 0
    unary_kernel_application_hits: int = 0
    unary_kernel_application_evaluations: int = 0
    causal_geometry_nodes: int = 0
    right_reset_certificate_nodes: int = 0
    finite_cycle_certificate_nodes: int = 0
    output_function_requests: int = 0
    output_function_cache_hits: int = 0
    output_function_evaluations: int = 0
    output_function_cache_entries: int = 0
    temporal_program_nodes: int = 0
    finite_port_state_nodes: int = 0
    other_retained_nodes: int = 0
    source_payload_nodes: int = 0
    source_summary_nodes: int = 0
    action_program_nodes: int = 0
    compiler_program_nodes: int = 0
    application_program_nodes: int = 0
    # Compatibility alias for canonical_transfer_nodes; excludes range bindings.
    transfer_summary_nodes: int = 0
    exact_endpoint_nodes: int = 0
    # Subset of other_retained_nodes: bounded caller-observed response records,
    # never an endpoint tape, quadtree payload, or canonical transfer action.
    retained_point_response_scalars: int = 0
    lowering_cache_entries: int = 0
    forbidden_future_payloads: int = 0
    retained_unbounded_future_integers: int = 0
    resource_audit_unknown_payloads: int = 0
    resource_audit_complete: int = 0
    collatz_mul3_summary_requests: int = 0
    collatz_mul3_summary_cache_hits: int = 0
    collatz_mul3_summary_evaluations: int = 0
    joint_interval_composition_requests: int = 0
    joint_interval_composition_cache_hits: int = 0
    joint_interval_composition_evaluations: int = 0
    interval_literal_requests: int = 0
    interval_literal_cache_hits: int = 0
    interval_literal_evaluations: int = 0
    interval_reflection_requests: int = 0
    interval_reflection_cache_hits: int = 0
    interval_reflection_identity_hits: int = 0
    interval_reflection_evaluations: int = 0
    interval_effect_intern_hits: int = 0
    interval_effect_intern_misses: int = 0
    reverse_summary_lookup_requests: int = 0
    reverse_summary_lookup_hits: int = 0
    reverse_summary_lookup_misses: int = 0
    reverse_summary_reflection_hits: int = 0
    composition_requests: int = 0
    composition_cache_hits: int = 0
    composition_evaluations: int = 0
    retained_composition_entries: int = 0
    summary_evaluations: int = 0
    summary_cache_hits: int = 0
    symbolic_port_queries: int = 0
    symbolic_maximum_port_bits: int = 0
    bounded_limb_operations: int = 0
    maximum_arithmetic_bits: int = 0
    unbounded_arithmetic_observations: int = 0
    endpoint_lowering_requests: int = 0
    explicitly_lowered_digits: int = 0
    explicitly_materialized_endpoints: int = 0


@dataclass(frozen=True, slots=True)
class HashLifeProjectionMetrics(LedgerMetrics):
    """Schema-seven totals and compatibility views of actual diamond work.

    ``spacetime_macro_*`` counts complete substitution observations;
    ``spacetime_tile_advance_*`` counts spatial transfer observations; and
    ``spacetime_boundary_advance_*`` counts continuation application. Their
    entry fields count the corresponding actual memo slots. On the canonical
    tile route, macrocell roots count explicitly leased completed application
    roots; demanded child results do not count as application roots. The legacy
    ``temporal_leaf_applications`` view counts primitive finite output
    evaluations, including construction of parametric finite functions.
    ``finite_action_alias_hits`` sums existing-key discoveries at decision-node
    and finite-expression interning. It counts late alias discoveries, not
    early query memo hits, identity reductions, or distinct alias classes.
    ``tile_observations`` includes original-source leaf reads and canonical-tile
    observation descents. ``canonical_tile_arena_nodes`` includes source and
    future content on the canonical-tile route. Spatial interface memo hits
    remain separate from late reductions in schema-seven counters.

    ``canonical_tile_arena_nodes_global`` is a retained compatibility name for
    the weak, process-shared immutable DyadicTile source-geometry population.
    It is not part of the index-owned canonical execution-tile inventory.
    ``spacetime_macro_cache_*`` and ``spacetime_tile_output_*`` are two legacy
    views of the same completed-result memo on the tile route and must not be
    summed. ``spacetime_boundary_output_*`` forwards causal-region task work;
    retained region slots remain part of the typed execution-memo inventory.

    ``section_*``, ``leaf_word_*``, plain ``boundary_*`` and exact tile-output
    compatibility fields remain retired. Zero there does not assert absent
    work, storage, or logarithmic complexity. The schema-seven fields give the
    full independently observed node partition and every instrumented counter.
    """

    point_queries: int
    section_requests: int
    section_cache_hits: int
    section_cache_entries: int
    leaf_word_requests: int
    leaf_word_cache_hits: int
    leaf_word_cache_entries: int
    boundary_requests: int
    boundary_cache_hits: int
    boundary_cache_entries: int
    canonical_tile_roots: int
    retained_execution_nodes: int
    canonical_program_word_roots: int
    left_boundary_residuals: int
    right_boundary_residuals: int
    dyadic_forest_chunks: int = 0
    dyadic_max_level: int = 0
    temporal_leaf_applications: int = 0
    high_level_tile_hits: int = 0
    finite_action_unique: int = 0
    finite_action_alias_hits: int = 0
    finite_action_tile_hits: int = 0
    finite_action_retained_entries: int = 0
    finite_action_mirror_alias_hits: int = 0
    finite_action_conjugate_alias_hits: int = 0
    peak_live_tile_roots: int = 0
    tile_observations: int = 0
    direct_powered_point_queries: int = 0
    canonical_spacetime_macrocell_roots: int = 0
    spacetime_tile_output_entries: int = 0
    spacetime_tile_output_max_level: int = 0
    spacetime_temporal_absorption_max: int = 0
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
    spacetime_boundary_advance_cache_publication_requests: int = 0
    spacetime_boundary_advance_cache_publications: int = 0
    spacetime_boundary_advance_cache_late_aliases: int = 0
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
    # Diamond compatibility views: classes count retained canonical records,
    # jump_entries counts completed-result memo slots, nonlinear_branch_evaluations
    # counts primitive finite transitions, exact_spatial_occurrences counts
    # retained canonical source/future tiles (never source visits), and
    # primitive_step/residual_physical
    # steps count the separately instrumented sequential-generation guard.
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


@dataclass(frozen=True, slots=True)
class HashLifeBehaviorMetrics(LedgerMetrics):
    """Observed storage categories and local action classes, not a scaling proof.

    Temporal programs include compiler and application nodes. Local finite
    transfer classes do not establish output-complete temporal successor closure.
    Work counters and workspace peaks must be measured separately from retention.
    """

    effect_exponent: int
    logical_width_bound: int
    seed_payload_tile_nodes: int
    padded_root_tile_nodes: int
    retained_spatial_tile_nodes: int
    application_spatial_tile_nodes: int
    powered_operator_nodes: int

    temporal_quotient_family: str
    temporal_quotient_horizon: int
    # Compatibility: minimum code bits for the local spatial action class,
    # excluding geometry and scoped-ID storage; not an exact temporal cell.
    temporal_cell_payload_bits: int
    temporal_residue_prime: int
    temporal_residue_precision: int
    temporal_residue_classes: int
    temporal_symbolic_exponent_fields: int
    temporal_quotient_state_class_bound: int
    # Zero means no finite bound on the symbolic composed-action closure.
    temporal_quotient_action_class_bound: int
    temporal_local_action_class_bound: int
    temporal_quotient_descriptor_bits_bound: int
    temporal_cocycle_weight_fields: int

    compiler_temporal_state_nodes: int
    compiler_temporal_action_nodes: int
    compiler_recursive_state_action_shared_nodes: int
    temporal_description_nodes: int
    seed_application_temporal_state_nodes: int
    seed_application_temporal_action_nodes: int
    seed_application_temporal_description_nodes: int

    spatial_occurrence_state_nodes: int
    spatial_occurrence_action_nodes: int
    spatial_occurrence_recursive_state_action_shared_nodes: int
    spatial_occurrence_description_nodes: int
    # Compatibility counters for the generic recursive carrier.  Production
    # reverse/add and Collatz bounded applications require all three to remain
    # zero; nonzero values therefore expose a cutover regression directly.
    unquotiented_recursive_application_state_nodes: int
    unquotiented_recursive_application_action_nodes: int
    unquotiented_recursive_application_description_nodes: int
    execution_memo_entries: int
    retained_effect_memo_entries: int
    recursive_spatial_residual_max_extent: int
    recursive_spatial_residual_max_depth: int
    recursive_boundary_wrapper_nodes: int
    spatial_occurrence_accounting_delta: int
    raw_temporal_scalar_length_fields: int
    raw_temporal_span_fields: int
    raw_spatial_occurrence_scalar_extent_fields: int
    eager_spatial_observer_fields: int
    carry_port_function_class_bound: int = 0
    spatial_interval_action_classes: int = 0
    spatial_interval_action_class_bound: int = 0
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


__all__ = ["HashLifeBehaviorMetrics", "HashLifeProjectionMetrics"]

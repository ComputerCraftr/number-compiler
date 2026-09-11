"""Units and ownership roles for independently observed execution resources.

Categories partition node records. Interner and memo slots remain a separate
dimension, including when several slots refer to the same canonical node.
"""

from __future__ import annotations

from collections.abc import Iterable, Mapping, Sequence
from types import MappingProxyType

from number_compiler.resources.ledger import ResourceInventory
from number_compiler.resources.semantic_metric_registry import (
    SEMANTIC_ADAPTER_WORK_COUNTERS as SEMANTIC_ADAPTER_WORK_COUNTERS,
)

NODE_ROLE_GROUPS: tuple[tuple[str, tuple[str, ...]], ...] = (
    ("canonical_tile_nodes", ("canonical_tile",)),
    ("tile_alphabet_nodes", ("tile_alphabet",)),
    ("source_payload_nodes", ("exact_source", "source_cell", "source_forest")),
    ("source_summary_nodes", ("source_summary",)),
    (
        "temporal_program_nodes",
        (
            "action_program",
            "symbolic_offset_program",
            "compiled_action_program",
            "temporal_action",
        ),
    ),
    ("image_action_nodes", ("image_action", "field_image")),
    ("diamond_cell_nodes", ("diamond_cell",)),
    (
        "canonical_transfer_nodes",
        (
            "canonical_transfer",
            "finite_kernel_template",
            "field_transfer",
        ),
    ),
    (
        "semantic_function_nodes",
        (
            "semantic_function",
            "semantic_factored_function",
            "semantic_structure",
            "radix_fused_action",
            "higher_semantic_expression",
            "higher_semantic_function",
        ),
    ),
    ("diamond_quotient_nodes", ("diamond_quotient", "higher_local_interface")),
    (
        "field_action_nodes",
        (
            "field_action",
            "field_cell_action",
            "reverse_field_action",
            "collatz_field_action",
        ),
    ),
    ("field_geometry_nodes", ("field_geometry",)),
    (
        "algebraic_component_nodes",
        (
            "radial_action",
            "carry_action",
            "character_action",
            "affine_action",
            "innovation_action",
            "output_morphism",
            "reverse_output_morphism",
            "reverse_local_action",
            "collatz_local_action",
            "provider_action",
        ),
    ),
    ("primitive_behavioral_quotient_nodes", ("primitive_behavioral_quotient",)),
    ("future_behavior_profile_nodes", ("future_behavior_profile",)),
    ("future_behavior_class_nodes", ("future_behavior_class",)),
    (
        "production_residual_state_nodes",
        (
            "residual_behavior_class",
            "reverse_defect_class",
            "collatz_defect_class",
            "reverse_residual_node",
        ),
    ),
    (
        "semantic_signature_nodes",
        (
            "semantic_port_signature",
            "higher_port_signature",
            "semantic_state_codec",
            "semantic_reachable_profile",
            "semantic_reachable_codec",
        ),
    ),
    ("exact_microblock_nodes", ("exact_microblock",)),
    (
        "spatial_action_program_nodes",
        ("context_program", "macro_transfer_program", "boundary_expression_program"),
    ),
    (
        "spatial_binding_nodes",
        (
            "spatial_binding",
            "field_transfer_binding",
            "lazy_field",
            "spatial_parent_memo",
            "diamond_memo",
            "macro_transfer_memo",
            "primitive_spatial_memo",
        ),
    ),
    ("finite_port_state_nodes", ("finite_port", "finite_kernel", "reverse_port_state")),
    ("exact_endpoint_nodes", ("exact_endpoint",)),
)

TILE_WORK_COUNTERS = (
    "future_behavior_requests",
    "future_behavior_early_hits",
    "future_behavior_binding_requests",
    "future_behavior_binding_early_hits",
    "future_behavior_publication_requests",
    "future_behavior_binding_publications",
    "future_behavior_aliases",
    "future_behavior_publication_failures",
    "future_behavior_new_classes",
    "future_behavior_profile_early_hits",
    "future_behavior_classification_evaluations",
    "future_behavior_classification_work",
    "future_behavior_refinement_observation_checks",
    "future_behavior_refinement_successor_checks",
    "behavior_classification_summary_checks",
    "behavior_classification_port_checks",
    "behavior_point_observations",
    "behavior_width_observations",
    "exact_causal_fallback_requests",
    "causal_extent_discharged_by_behavior",
    "tile_causal_quiescent_boundary_reuses",
    "reverse_bound_output_requests",
    "reverse_bound_output_early_hits",
    "reverse_bound_output_evaluations",
    "reverse_bound_output_failures",
    "reverse_bound_output_publication_requests",
    "reverse_bound_output_publications",
    "reverse_bound_output_late_duplicates",
    "reverse_bound_output_leaf_evaluations",
    "reverse_bound_output_parent_compositions",
    "reverse_bound_output_evictions",
    "reverse_bound_output_post_eviction_misses_attribution_unknown",
    "tile_region_normalization_requests",
    "tile_region_normalization_misses",
    "tile_region_normalization_early_hits",
    "tile_region_normalization_publication_requests",
    "tile_region_normalization_publications",
    "tile_region_normalization_late_duplicates",
    "tile_region_application_validation_visits",
    "tile_boundary_concat_cache_requests",
    "tile_boundary_concat_cache_misses",
    "tile_boundary_concat_cache_early_hits",
    "tile_boundary_concat_cache_evaluations",
    "tile_boundary_concat_cache_failures",
    "tile_boundary_concat_cache_publication_requests",
    "tile_boundary_concat_cache_publications",
    "tile_boundary_concat_cache_late_duplicates",
    "tile_boundary_concat_application_validation_visits",
    "powered_absorption_requests",
    "powered_absorption_early_hits",
    "powered_absorption_evaluations",
    "powered_absorption_successes",
    "powered_absorption_max_span",
    "proof_artifact_builds",
    "proof_artifact_hits",
    "proof_artifact_loading_work",
    "proof_artifact_build_failures",
    "proof_artifact_loading_failures",
    "fused_interface_requests",
    "fused_interface_early_hits",
    "fused_interface_publications",
    "fused_interface_late_aliases",
    "fused_interface_publication_requests",
    "tile_fused_frames",
    "tile_fused_leaf_evaluations",
    "tile_fused_observation_descents",
    "tile_fused_workspace_peak",
    "tile_fused_observation_requests",
    "spatial_interface_composition_requests",
    "spatial_interface_composition_early_hits",
    "spatial_interface_composition_late_aliases",
    "spatial_interface_composition_publications",
    "spatial_interface_composition_publication_requests",
    "tile_temporal_action_hits",
    "tile_temporal_action_publications",
    "tile_temporal_action_semantic_alias_hits",
    "reverse_frobenius_plan_compositions",
    "reverse_field_action_source_annihilation_derivations",
    "collatz_field_action_source_annihilation_derivations",
    "tile_temporal_complete_compositions",
    "tile_temporal_complete_frames",
    "completed_result_publication_requests",
    "completed_result_evaluations",
    "completed_result_late_duplicate_reductions",
    "tile_scheduler_demand_parent_hits",
    "tile_scheduler_demand_parent_misses",
    "completed_result_requests",
    "completed_result_early_hits",
    "completed_result_publications",
    "completed_result_tile_retirements",
    "completed_result_evictions",
    "completed_result_evicted_entries",
    "completed_result_retirement_memo_removals",
    "completed_result_reverse_index_removals",
    "completed_result_retirement_traversal_steps",
    "completed_result_eviction_reverse_index_entries",
    "completed_result_recomputation_attribution_unknown",
    "result_cache_kind_classification_visits",
    "result_cache_result_evicted_entries",
    "result_cache_interface_evicted_entries",
    "result_cache_behavior_evicted_entries",
    "result_cache_region_evicted_entries",
    "result_cache_spatial_evicted_entries",
    "result_cache_result_retirement_removals",
    "result_cache_interface_retirement_removals",
    "result_cache_behavior_retirement_removals",
    "result_cache_region_retirement_removals",
    "result_cache_spatial_retirement_removals",
    "result_cache_result_post_eviction_misses_attribution_unknown",
    "result_cache_interface_post_eviction_misses_attribution_unknown",
    "result_cache_behavior_post_eviction_misses_attribution_unknown",
    "result_cache_region_post_eviction_misses_attribution_unknown",
    "result_cache_spatial_post_eviction_misses_attribution_unknown",
    "tile_intern_requests",
    "tile_intern_early_hits",
    "tile_publications",
    "tile_mirror_requests",
    "tile_mirror_early_hits",
    "tile_mirror_evaluations",
    "tile_mirror_publications",
    "tile_retirements",
    "tile_lease_acquisitions",
    "tile_lease_releases",
    "tile_retirement_work_ns",
    "python_gc_collections_during_tile_retirement",
    "python_gc_collected_during_tile_retirement",
    "python_gc_uncollectable_during_tile_retirement",
    "tile_recreation_attribution_unknown",
    "cache_event_histogram_dropped",
    "tile_observation_descents",
    "tile_scheduler_frames",
    "tile_scheduler_demand_descents",
    "tile_scheduler_width_descents",
    "tile_scheduler_parent_early_hits",
    "tile_scheduler_midpoint_hits",
    "tile_scheduler_fused_requests",
    "tile_scheduler_leaf_function_applications",
    "tile_scheduler_temporal_complete_requests",
    "tile_scheduler_spatial_compositions",
    "tile_scheduler_workspace_peak",
    "canonical_tile_peak",
    "tile_root_lease_peak",
    "powered_interface_requests",
    "powered_interface_early_hits",
    "powered_interface_publications",
    "tile_width_descents",
    "completed_result_port_variants_peak",
    "completed_result_port_validation_requests",
    "completed_result_port_validation_visits",
    "boundary_tile_lease_peak",
    "tile_boundary_transfer_requests",
    "tile_boundary_transfer_frames",
    "tile_boundary_transfer_parent_observations",
    "tile_boundary_transfer_descents",
    "tile_boundary_transfer_workspace_peak",
    "tile_source_imports",
    "tile_endpoint_projection_descents",
    "tile_endpoint_emissions",
    "tile_projection_width_observations",
    "tile_radix_stage_publications",
    "tile_radix_digit_observations",
    "tile_scheduler_direct_requests",
    "tile_scheduler_sibling_transfer_requests",
    "tile_scheduler_sibling_transfer_evaluations",
    "tile_scheduler_demanded_result_pins",
    "primitive_tile_interface_publications",
    "tile_causal_interface_midpoint_reuse",
    "tile_causal_interface_midpoint_publications",
    "tile_leaf_product_requests",
    "tile_leaf_product_early_hits",
    "tile_leaf_product_evaluations",
    "tile_leaf_product_publications",
    "tile_leaf_product_late_aliases",
)

# Counts are forwarded only from runtime instrumentation. Presence is reported
# separately, so a missing instrument cannot masquerade as a measured zero.
DIAMOND_WORK_COUNTERS = (
    "diamond_requests",
    "diamond_cache_hits",
    "diamond_evaluations",
    "macro_transfer_requests",
    "macro_transfer_cache_hits",
    "macro_transfer_evaluations",
    "image_program_requests",
    "image_program_cache_hits",
    "image_program_evaluations",
    "output_function_requests",
    "output_function_cache_hits",
    "output_function_evaluations",
    "context_observation_requests",
    "context_observation_cache_hits",
    "context_observation_evaluations",
    "unary_function_composition_requests",
    "unary_function_composition_hits",
    "unary_function_composition_evaluations",
    "unary_kernel_application_requests",
    "unary_kernel_application_hits",
    "unary_kernel_application_evaluations",
    "boundary_substitution_requests",
    "boundary_substitution_cache_hits",
    "boundary_substitution_evaluations",
    "spatial_parent_requests",
    "spatial_parent_cache_hits",
    "spatial_parent_evaluations",
    "primitive_spatial_requests",
    "primitive_spatial_cache_hits",
    "primitive_spatial_evaluations",
    "primitive_spatial_observations",
    "primitive_transition_evaluations",
    "primitive_output_evaluations",
    "scalar_observation_requests",
    "sequential_generation_advances",
    "scheduler_transitions",
    "scheduler_workspace_peak",
)

DIAMOND_MEMO_ROLES = (
    ("diamond_cache_entries", "diamond_memo"),
    ("macro_transfer_cache_entries", "macro_transfer_memo"),
    ("image_program_cache_entries", "image_program_memo"),
    ("output_function_cache_entries", "output_function_memo"),
    ("boundary_substitution_cache_entries", "boundary_substitution_memo"),
    ("spatial_parent_cache_entries", "spatial_parent_memo"),
    ("primitive_spatial_cache_entries", "primitive_spatial_memo"),
)

# These are optional instruments: an index without a semantic executor has no
# quotient work. They are never substituted for its existing primitive work.
QUOTIENT_WORK_COUNTERS = (
    "primitive_occurrence_observation_evaluations",
    "primitive_behavior_refinement_observation_checks",
    "primitive_behavior_refinement_successor_checks",
    "semantic_expression_finite_lift_requests",
    "semantic_expression_finite_lift_hits",
    "semantic_expression_finite_lift_evaluations",
    "semantic_expression_finite_lift_frames",
    "semantic_structure_declaration_requests",
    "semantic_structure_declaration_identity_hits",
    "semantic_structure_declaration_early_hits",
    "semantic_structure_declaration_evaluations",
    "primitive_macro_requests",
    "primitive_macro_early_hits",
    "primitive_macro_evaluations",
    "primitive_macro_compilations",
    "primitive_macro_source_frames",
    "primitive_macro_spatial_compositions",
    "primitive_macro_observation_requests",
    "primitive_macro_observation_evaluations",
    "quotient_parent_requests",
    "quotient_parent_early_hits",
    "quotient_parent_publications",
    "quotient_complete_normalizations",
    "quotient_semantic_interner_evaluations",
    "quotient_normal_form_early_hits",
    "quotient_semantic_interner_hits",
    "semantic_function_requests",
    "semantic_function_request_hits",
    "semantic_function_evaluations",
    "semantic_function_decision_visits",
    "semantic_function_ite_frames",
    "semantic_function_rewrite_frames",
    "semantic_function_staged_nodes",
    "semantic_function_published_nodes",
    "semantic_bit_admissibility_requests",
    "semantic_bit_admissibility_early_hits",
    "semantic_bit_admissibility_evaluations",
    "semantic_bit_admissibility_publications",
    "semantic_expression_tasks",
    "semantic_binary_division_compilations",
)

# A field-action executor installs every counter, including observed zeros, when
# it is constructed.  This lets reporting distinguish missing instrumentation
# from measured absence without consulting a second executor snapshot.
ALGEBRAIC_FIELD_WORK_COUNTERS = (
    "temporal_parent_requests",
    "temporal_parent_early_hits",
    "temporal_parent_compositions",
    "temporal_parent_late_duplicate_reductions",
    "radial_action_operations",
    "carry_action_operations",
    "character_action_operations",
    "affine_action_operations",
    "innovation_action_operations",
    "output_morphism_operations",
    "residual_refinement_operations",
    "source_annihilations",
    "root_germ_skips",
    "whole_word_sweeps",
    "whole_word_symbol_visits",
    "proof_machine_applications",
    "production_residual_state_classes",
    "sequential_generation_advances",
    "spatial_descents",
    "canonical_expression_node_visits",
    "post_publish_equivalence_merges",
    "point_observations",
    "width_observations",
    "radix_fixed_cycle_observations",
    "radix_provider_digit_requests",
    "radix_provider_digit_early_hits",
    "radix_provider_digit_evaluations",
    "radix_temporal_action_requests",
    "radix_temporal_action_early_hits",
    "radix_temporal_action_evaluations",
    "radix_recursive_transfer_requests",
    "radix_recursive_transfer_early_hits",
    "radix_recursive_transfer_evaluations",
    "radix_recursive_descents",
    "radix_source_bit_visits",
    "radix_limb_operations",
    "higher_point_observations",
    "higher_width_observations",
    "higher_observation_fallback",
    "higher_range_dyadic_cells",
    "higher_concrete_operation_evaluations",
    "higher_concrete_operation_hits",
    "higher_concrete_initial_evaluations",
    "higher_concrete_step_evaluations",
    "higher_concrete_emit_evaluations",
    "higher_concrete_apply_evaluations",
    "higher_concrete_force_evaluations",
    "higher_primitive_step_hits",
    "higher_primitive_step_publications",
    "higher_primitive_output_hits",
    "higher_primitive_output_publications",
    "higher_summary_temporal_compositions",
    "higher_summary_spatial_compositions",
    "higher_context_spatial_compositions",
    "reverse_temporal_leaf_substitutions",
    "reverse_temporal_parent_substitutions",
    "reverse_temporal_prefix_image_observations",
    "collatz_temporal_leaf_substitutions",
    "collatz_temporal_parent_substitutions",
    "collatz_temporal_prefix_image_observations",
    "collatz_complete_leaf_interface_observations",
    "collatz_complete_leaf_interface_early_hits",
    "collatz_source_root_match_requests",
    "collatz_source_root_match_early_hits",
    "collatz_source_root_match_evaluations",
    "collatz_source_root_match_publications",
    "collatz_source_root_match_late_duplicates",
    "reverse_active_transfer_evaluations",
    "reverse_active_transfer_declines",
    "reverse_boundary_transfer_publications",
    "reverse_boundary_transfer_completions",
    "collatz_radix_boundary_validation_requests",
    "collatz_radix_boundary_validation_visits",
    "collatz_radix_boundary_proof_hits",
    "collatz_radix_boundary_proof_publications",
    "opaque_higher_operation_publications",
    "higher_operation_early_hits",
    "radix_observations",
    "endpoint_emissions",
    "field_action_publications",
    "output_morphism_publications",
    "image_publications",
    "microblock_publications",
    "new_field_image_nodes",
    "field_image_binding_requests",
    "field_image_binding_early_hits",
    "microblock_payload_bytes",
    "microblock_payload_high_water_bytes",
    "microblock_entry_high_water",
    "source_leaf_visits",
    "transient_buffer_allocations",
    "proof_machine_artifacts_loaded_by_runtime",
    "algebraic_executor_capability_validated",
    "new_field_transfer_nodes",
    "field_transfer_binding_requests",
    "field_transfer_binding_early_hits",
    "field_transfer_binding_publications",
    "field_transfer_semantic_alias_hits",
    "local_interface_compositions",
    "local_interface_alias_hits",
    "output_morphism_visits",
    "field_image_parent_observation_requests",
    "field_image_parent_observation_early_hits",
    "field_image_parent_observation_evaluations",
    "provider_fused_point_requests",
    "provider_fused_point_early_hits",
    "provider_fused_point_evaluations",
    "provider_fused_width_requests",
    "provider_fused_width_early_hits",
    "provider_fused_width_evaluations",
    "concrete_port_task_frames",
    "concrete_provider_layer_publications",
    "concrete_irrelevant_port_elisions",
    "endpoint_mirror_reuses",
    "endpoint_mirror_buffer_peak_bytes",
    "temporal_leaf_diamond_descents",
    "higher_semantic_evaluations",
    "higher_semantic_task_frames",
    "higher_action_continuation_requests",
    "temporal_leaf_parent_hits",
    "temporal_leaf_parent_publications",
    "higher_identity_transfer_elisions",
    "generic_higher_action_early_hits",
    "generic_higher_action_publications",
    "parametric_width_forest_visits",
    "parametric_width_parent_visits",
    "parametric_width_descent_steps",
    "parametric_width_contexts_peak",
    "higher_boundary_resolution_hits",
    "higher_runtime_composition_requests",
    "higher_runtime_composition_hits",
    "higher_runtime_interchange_compositions",
    "higher_finite_transfer_state_visits",
    "higher_finite_transfer_evaluations",
    "higher_finite_transfer_compositions",
    "concrete_provider_layer_alias_hits",
    "concrete_port_task_requests",
    "concrete_port_task_early_hits",
    "concrete_port_task_evaluations",
    "concrete_virtual_interface_requests",
    "concrete_virtual_interface_early_hits",
    "concrete_virtual_interface_evaluations",
    "concrete_virtual_interface_publications",
    "concrete_virtual_interface_alias_hits",
    "recursive_field_image_requests",
    "recursive_field_image_early_hits",
    "recursive_field_image_temporal_compositions",
    "recursive_field_image_spatial_compositions",
    "recursive_field_image_primitive_evaluations",
    "recursive_field_forest_requests",
    "recursive_field_forest_early_hits",
    "recursive_field_forest_spatial_compositions",
    "recursive_field_forest_primitive_evaluations",
)

CANONICAL_EXPRESSION_VISIT_COUNTERS = (
    "diamond_temporal_import_visits",
    "diamond_slice_normalization_visits",
    "finite_expression_component_checks",
    "finite_port_substitution_support_frame_pops",
    "finite_port_substitution_publication_visits",
    "semantic_function_decision_visits",
    "semantic_function_ite_frames",
    "semantic_function_rewrite_frames",
    "unary_function_admission_visits",
    "unary_function_admission_frame_visits",
    "decimal_t2_output_reduction_evaluations",
    "decimal_t2_output_reduction_early_hits",
    "decimal_t2_output_identity_reductions",
    "decimal_t2_cofactor_visits",
    "semantic_expression_finite_lift_frames",
    "unary_correlated_cofactor_visits",
    "higher_context_admission_visits",
    "context_variable_support_visits",
    "context_variable_support_frame_visits",
    "diamond_finite_bridge_visits",
    "diamond_finite_bridge_admission_visits",
    "boundary_decision_visits",
    "image_program_admission_visits",
    "causal_halo_dag_visits",
    "causal_halo_kernel_checks",
)


def schema6_work_values(counters: Mapping[str, int]) -> dict[str, int]:
    """Map actual executor instruments into the stable schema-six vocabulary."""
    values = {name: counters.get(name, 0) for name in ALGEBRAIC_FIELD_WORK_COUNTERS}
    values.update((name, counters.get(name, 0)) for name in TILE_WORK_COUNTERS)
    # The concrete scheduler records misses as ``*_requests`` because its
    # early probe precedes the compilation path.  Public request fields count
    # every probe, while the raw snapshot preserves the independently observed
    # miss and early-hit instruments.
    values["concrete_port_task_requests"] = counters.get(
        "concrete_port_task_requests", 0
    ) + counters.get("concrete_port_task_early_hits", 0)
    values["concrete_virtual_interface_requests"] = counters.get(
        "concrete_virtual_interface_requests", 0
    ) + counters.get("concrete_virtual_interface_early_hits", 0)
    aliases = {
        "temporal_parent_requests": "diamond_temporal_composition_requests",
        "temporal_parent_early_hits": "diamond_temporal_composition_hits",
        "temporal_parent_compositions": "diamond_temporal_composition_evaluations",
        "spatial_descents": "width_descent_steps",
        "width_observations": "width_queries",
        "endpoint_emissions": "explicitly_lowered_digits",
        "image_publications": "diamond_cell_interner_evaluations",
        "microblock_publications": "microblock_publications",
        "source_leaf_visits": "source_leaf_reads",
        "proof_machine_artifacts_loaded_by_runtime": "proof_machine_artifacts_loaded_by_runtime",
    }
    for public, instrument in aliases.items():
        if public not in counters:
            values[public] = counters.get(instrument, 0)
    if "point_observations" not in counters:
        values["point_observations"] = counters.get("diamond_point_queries", 0)
    if "radix_observations" not in counters:
        values["radix_observations"] = sum(
            counters.get(name, 0)
            for name in (
                "radix_fused_digit_queries",
                "original_radix_point_queries",
                "radix_original_affine_digit_queries",
                "radix_native_source_queries",
                "radix_native_odd_shift_queries",
                "radix_native_odd_constant_queries",
                "radix_native_odd_low_limb_queries",
            )
        )
    if "canonical_expression_node_visits" not in counters:
        values["canonical_expression_node_visits"] = sum(
            counters.get(name, 0) for name in CANONICAL_EXPRESSION_VISIT_COUNTERS
        )
    values["field_action_component_operations"] = sum(
        values[name]
        for name in (
            "radial_action_operations",
            "carry_action_operations",
            "character_action_operations",
            "affine_action_operations",
            "innovation_action_operations",
            "output_morphism_operations",
            "residual_refinement_operations",
        )
    )
    values["spatial_parent_cache_hits"] = counters.get(
        "spatial_parent_cache_hits",
        0,
    ) + counters.get("spatial_parent_early_hits", 0)
    values["nonlinear_branch_evaluations"] = counters.get(
        "nonlinear_branch_evaluations",
        counters.get("reverse_nonlinear_branch_evaluations", 0),
    )
    values["whole_word_sweeps"] = counters.get("whole_word_sweeps", 0)
    values["whole_word_symbol_visits"] = counters.get("whole_word_symbol_visits", 0)
    values["proof_machine_applications"] = counters.get("proof_machine_applications", 0)
    if "proof_machine_artifacts_loaded_by_runtime" not in counters:
        values["proof_machine_artifacts_loaded_by_runtime"] = 0
    values["extensional_family_executor_instances"] = counters.get(
        "extensional_family_executor_instances",
        0,
    )
    values["transient_buffer_allocations"] = counters.get(
        "transient_buffer_allocations",
        0,
    )
    values["transient_buffer_bytes_peak"] = counters.get(
        "transient_buffer_bytes_peak", 0
    )
    if "field_action_publications" not in counters:
        values["field_action_publications"] = sum(
            counters.get(name, 0)
            for name in (
                "reverse_field_action_publications",
                "collatz_field_action_publications",
                "tile_temporal_action_publications",
            )
        )
    image_publications = counters.get("new_field_image_nodes", 0)
    values["new_field_image_nodes"] = image_publications
    values["field_image_binding_requests"] = counters.get(
        "field_image_binding_requests",
        0,
    )
    values["field_image_binding_early_hits"] = counters.get(
        "field_image_binding_early_hits",
        0,
    )
    if (
        "image_publications" not in counters
        and "algebraic_executor_capability_validated" in counters
    ):
        values["image_publications"] = image_publications
    values["new_canonical_field_images_published"] = image_publications
    values["field_image_publication_requests"] = counters.get(
        "field_image_publication_requests",
        counters.get(
            "field_image_binding_requests",
            counters.get("image_program_requests", 0),
        ),
    )
    values["field_image_early_hits"] = counters.get(
        "field_image_early_hits",
        counters.get(
            "field_image_binding_early_hits",
            counters.get("image_program_cache_hits", 0),
        ),
    )
    values["field_interface_publications"] = counters.get(
        "field_interface_publications",
        counters.get("higher_interface_publications", 0)
        + counters.get("quotient_semantic_interner_evaluations", 0),
    )
    values["field_interface_early_hits"] = counters.get(
        "field_interface_early_hits",
        counters.get("higher_interface_normal_form_hits", 0)
        + counters.get("quotient_normal_form_early_hits", 0),
    )
    # Frames refine semantic-call counts. Preserve the legacy coarse count
    # when only it was instrumented, without counting a call twice alongside
    # the frames that execute it.
    higher_work = max(
        counters.get("higher_semantic_task_frames", 0),
        counters.get("higher_semantic_evaluations", 0),
    )
    values["total_internal_action_work"] = (
        higher_work
        + sum(
            values[name]
            for name in (
                "temporal_parent_compositions",
                "canonical_expression_node_visits",
                "field_action_component_operations",
                "nonlinear_branch_evaluations",
            )
        )
        + sum(
            counters.get(name, 0)
            for name in (
                "spatial_parent_evaluations",
                "boundary_substitution_evaluations",
                "primitive_transition_evaluations",
                "primitive_output_evaluations",
                "field_transfer_parent_evaluations",
                "field_image_parent_evaluations",
                "higher_operation_publications",
                "higher_action_continuation_requests",
                "higher_concrete_operation_evaluations",
                "higher_concrete_operation_hits",
                "higher_runtime_composition_requests",
                "higher_finite_transfer_state_visits",
                "higher_primitive_step_hits",
                "higher_primitive_step_publications",
                "higher_primitive_output_hits",
                "higher_primitive_output_publications",
                "opaque_higher_operation_publications",
                "higher_operation_early_hits",
                "higher_spatial_transfer_publications",
                "higher_range_dyadic_cells",
                "spatial_observation_descents",
                "generic_higher_action_early_hits",
                "generic_higher_action_publications",
                "parametric_width_forest_visits",
                "parametric_width_parent_visits",
                "parametric_width_descent_steps",
                "provider_fused_point_evaluations",
                "provider_fused_width_evaluations",
                "concrete_port_task_evaluations",
                "concrete_port_task_frames",
                "concrete_virtual_interface_evaluations",
                "recursive_field_image_temporal_compositions",
                "recursive_field_image_spatial_compositions",
                "recursive_field_image_primitive_evaluations",
                "recursive_field_forest_spatial_compositions",
                "reverse_temporal_prefix_image_observations",
                "collatz_temporal_prefix_image_observations",
                "recursive_field_forest_primitive_evaluations",
                "radix_recursive_transfer_evaluations",
                "radix_temporal_action_evaluations",
                "radix_recursive_descents",
                "radix_source_bit_visits",
                "radix_limb_operations",
                "temporal_leaf_diamond_descents",
                "temporal_leaf_parent_hits",
                "temporal_leaf_parent_publications",
                "collatz_radix_boundary_validation_visits",
                "collatz_radix_boundary_proof_hits",
                "completed_result_requests",
                "completed_result_publication_requests",
                "tile_intern_requests",
                "spatial_interface_composition_requests",
                "spatial_interface_composition_publication_requests",
                "fused_interface_publication_requests",
                "fused_interface_requests",
                "tile_fused_frames",
                "powered_absorption_requests",
                "proof_artifact_loading_work",
                "tile_fused_leaf_evaluations",
                "tile_fused_observation_descents",
                "tile_fused_observation_requests",
                "tile_lease_acquisitions",
                "tile_lease_releases",
                "tile_retirements",
                "tile_observation_descents",
                "tile_scheduler_frames",
                "tile_scheduler_demand_descents",
                "tile_scheduler_width_descents",
                "tile_scheduler_leaf_function_applications",
                "powered_interface_requests",
                "tile_width_descents",
                "tile_endpoint_projection_descents",
                "tile_endpoint_emissions",
                "tile_scheduler_sibling_transfer_requests",
                "primitive_tile_interface_publications",
                "tile_leaf_product_requests",
                "tile_radix_stage_publications",
                "tile_radix_digit_observations",
                "tile_temporal_complete_frames",
                "tile_temporal_action_publications",
            )
        )
    )
    return values


def schema6_inventory_values(inventory: Iterable[ResourceInventory]) -> dict[str, int]:
    """Field-runtime populations from the same immutable ledger snapshot."""
    rows = tuple(inventory)

    def nodes(*roles: str) -> int:
        return sum(
            item.observed_nodes or 0
            for item in rows
            if normalized_role(item.role) in roles
        )

    def entries(*roles: str) -> int:
        return sum(
            item.observed_entries or 0
            for item in rows
            if normalized_role(item.role) in roles
        )

    return {
        "canonical_tile_nodes": nodes("canonical_tile"),
        "tile_alphabet_nodes": nodes("tile_alphabet"),
        "tile_root_leases": entries("tile_root_lease"),
        "tile_child_reverse_index_entries": entries("tile_child_reverse_index"),
        "tile_execution_memo_entries": entries("completed_result_memo"),
        "completed_result_reverse_index_entries": entries(
            "completed_result_reverse_index"
        ),
        "completed_result_variant_entries": entries("completed_result_port_variants"),
        "tile_application_result_pins": entries("tile_application_result_pin"),
        "source_cell_nodes": nodes("source_cell", "source_forest"),
        "image_input_reference_nodes": nodes("image_input_reference"),
        "runtime_query_state_nodes": nodes("runtime_query_state_memo"),
        "runtime_query_environment_nodes": nodes("runtime_query_environment_memo"),
        "runtime_operation_memo_entries": entries("runtime_operation_memo"),
        "field_transfer_nodes": nodes("field_transfer"),
        "field_transfer_binding_entries": entries("field_transfer_binding"),
        "recursive_field_image_nodes": nodes("field_image"),
        "field_geometry_nodes": nodes("field_geometry"),
        "local_interface_nodes": nodes("diamond_quotient", "higher_local_interface"),
        "output_morphism_nodes": nodes(
            "output_morphism",
            "reverse_output_morphism",
            "coordinate_output_morphism",
        ),
    }


PROOF_CERTIFICATE_POPULATIONS: Mapping[str, int] = MappingProxyType(
    {
        "reverse_t2_left": 757,
        "reverse_t2_right": 179,
        "collatz_c4_left": 50,
        "collatz_c4_right": 90,
    }
)


def normalized_role(role: str) -> str:
    return role.lower().replace("-", "_")


def observed_node_partition(
    inventory: Iterable[ResourceInventory],
    containers: Mapping[int, object] | None = None,
) -> dict[str, int]:
    """Count every category from container observations, never ledger claims."""
    categories = {
        role: category for category, roles in NODE_ROLE_GROUPS for role in roles
    }
    counts = dict.fromkeys((category for category, _ in NODE_ROLE_GROUPS), 0)
    counts["other_retained_nodes"] = 0
    for item in inventory:
        category = categories.get(normalized_role(item.role), "other_retained_nodes")
        nodes = item.observed_nodes or 0
        if category == "diamond_cell_nodes" and containers is not None:
            from number_compiler.hashlife.actions.diamond_actions import CellNode

            container = containers.get(item.owner)
            if isinstance(container, Sequence) and len(container) == nodes:
                images = sum(
                    type(value) is CellNode and value.kind == "image"
                    for value in container
                )
                counts["image_action_nodes"] += images
                nodes -= images
        counts[category] += nodes
    return counts

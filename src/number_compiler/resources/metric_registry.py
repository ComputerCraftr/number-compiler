"""Units and ownership roles for independently observed execution resources.

Categories partition node records. Interner and memo slots remain a separate
dimension, including when several slots refer to the same canonical node.
"""

from __future__ import annotations

from collections.abc import Iterable, Mapping, Sequence
from typing import cast

from number_compiler.resources import semantic_metric_registry
from number_compiler.resources.ledger import ResourceInventory
from number_compiler.resources.metric_keys import (
    arithmetic_contracts as _contracts_keys,
)
from number_compiler.resources.metric_keys import (
    arithmetic_functions as _functions_keys,
)
from number_compiler.resources.metric_keys import (
    arithmetic_radix_transfer as _radix_transfer_keys,
)
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.resources.metric_keys import (
    hashlife_actions as _actions_keys,
)
from number_compiler.resources.metric_keys import (
    hashlife_behavior as _behavior_keys,
)
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)
from number_compiler.resources.metric_keys import (
    hashlife_interfaces as _interfaces_keys,
)
from number_compiler.resources.metric_keys import (
    hashlife_observation as _observation_keys,
)
from number_compiler.resources.metric_keys import (
    hashlife_tiles as _tiles_keys,
)
from number_compiler.resources.metric_keys import projection as _projection_keys
from number_compiler.resources.metric_keys import resources as _resources_keys
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys
from number_compiler.resources.metric_keys import shared as _shared_keys

SEMANTIC_ADAPTER_WORK_COUNTERS = semantic_metric_registry.SEMANTIC_ADAPTER_WORK_COUNTERS

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
    _tiles_keys.FUTURE_BEHAVIOR_REQUESTS,
    _tiles_keys.FUTURE_BEHAVIOR_EARLY_HITS,
    _tiles_keys.FUTURE_BEHAVIOR_BINDING_REQUESTS,
    _tiles_keys.FUTURE_BEHAVIOR_BINDING_EARLY_HITS,
    _tiles_keys.FUTURE_BEHAVIOR_PUBLICATION_REQUESTS,
    _tiles_keys.FUTURE_BEHAVIOR_BINDING_PUBLICATIONS,
    _tiles_keys.FUTURE_BEHAVIOR_ALIASES,
    _tiles_keys.FUTURE_BEHAVIOR_PUBLICATION_FAILURES,
    _behavior_keys.FUTURE_BEHAVIOR_NEW_CLASSES,
    _behavior_keys.FUTURE_BEHAVIOR_PROFILE_EARLY_HITS,
    _tiles_keys.FUTURE_BEHAVIOR_CLASSIFICATION_EVALUATIONS,
    _behavior_keys.FUTURE_BEHAVIOR_CLASSIFICATION_WORK,
    _behavior_keys.FUTURE_BEHAVIOR_REFINEMENT_OBSERVATION_CHECKS,
    _behavior_keys.FUTURE_BEHAVIOR_REFINEMENT_SUCCESSOR_CHECKS,
    _execution_keys.BEHAVIOR_CLASSIFICATION_SUMMARY_CHECKS,
    _tiles_keys.BEHAVIOR_CLASSIFICATION_PORT_CHECKS,
    _execution_keys.BEHAVIOR_POINT_OBSERVATIONS,
    _execution_keys.BEHAVIOR_WIDTH_OBSERVATIONS,
    _execution_keys.EXACT_CAUSAL_FALLBACK_REQUESTS,
    _shared_keys.CAUSAL_EXTENT_DISCHARGED_BY_BEHAVIOR,
    _execution_keys.TILE_CAUSAL_QUIESCENT_BOUNDARY_REUSES,
    _tiles_keys.REVERSE_BOUND_OUTPUT_REQUESTS,
    _tiles_keys.REVERSE_BOUND_OUTPUT_EARLY_HITS,
    _tiles_keys.REVERSE_BOUND_OUTPUT_EVALUATIONS,
    _tiles_keys.REVERSE_BOUND_OUTPUT_FAILURES,
    _tiles_keys.REVERSE_BOUND_OUTPUT_PUBLICATION_REQUESTS,
    _tiles_keys.REVERSE_BOUND_OUTPUT_PUBLICATIONS,
    _tiles_keys.REVERSE_BOUND_OUTPUT_LATE_DUPLICATES,
    _tiles_keys.REVERSE_BOUND_OUTPUT_LEAF_EVALUATIONS,
    _tiles_keys.REVERSE_BOUND_OUTPUT_PARENT_COMPOSITIONS,
    _resources_keys.REVERSE_BOUND_OUTPUT_EVICTIONS,
    _tiles_keys.REVERSE_BOUND_OUTPUT_POST_EVICTION_MISSES_ATTRIBUTION_UNKNOWN,
    _tiles_keys.TILE_REGION_NORMALIZATION_REQUESTS,
    _tiles_keys.TILE_REGION_NORMALIZATION_MISSES,
    _tiles_keys.TILE_REGION_NORMALIZATION_EARLY_HITS,
    _tiles_keys.TILE_REGION_NORMALIZATION_PUBLICATION_REQUESTS,
    _tiles_keys.TILE_REGION_NORMALIZATION_PUBLICATIONS,
    _tiles_keys.TILE_REGION_NORMALIZATION_LATE_DUPLICATES,
    _tiles_keys.TILE_REGION_APPLICATION_VALIDATION_VISITS,
    _tiles_keys.TILE_BOUNDARY_CONCAT_CACHE_REQUESTS,
    _tiles_keys.TILE_BOUNDARY_CONCAT_CACHE_MISSES,
    _tiles_keys.TILE_BOUNDARY_CONCAT_CACHE_EARLY_HITS,
    _tiles_keys.TILE_BOUNDARY_CONCAT_CACHE_EVALUATIONS,
    _tiles_keys.TILE_BOUNDARY_CONCAT_CACHE_FAILURES,
    _tiles_keys.TILE_BOUNDARY_CONCAT_CACHE_PUBLICATION_REQUESTS,
    _tiles_keys.TILE_BOUNDARY_CONCAT_CACHE_PUBLICATIONS,
    _tiles_keys.TILE_BOUNDARY_CONCAT_CACHE_LATE_DUPLICATES,
    _tiles_keys.TILE_BOUNDARY_CONCAT_APPLICATION_VALIDATION_VISITS,
    _execution_keys.POWERED_ABSORPTION_REQUESTS,
    "powered_absorption_early_hits",
    _execution_keys.POWERED_ABSORPTION_EVALUATIONS,
    _execution_keys.POWERED_ABSORPTION_SUCCESSES,
    _execution_keys.POWERED_ABSORPTION_MAX_SPAN,
    "proof_artifact_builds",
    "proof_artifact_hits",
    "proof_artifact_loading_work",
    "proof_artifact_build_failures",
    "proof_artifact_loading_failures",
    _tiles_keys.FUSED_INTERFACE_REQUESTS,
    _tiles_keys.FUSED_INTERFACE_EARLY_HITS,
    _tiles_keys.FUSED_INTERFACE_PUBLICATIONS,
    _tiles_keys.FUSED_INTERFACE_LATE_ALIASES,
    _tiles_keys.FUSED_INTERFACE_PUBLICATION_REQUESTS,
    _execution_keys.TILE_FUSED_FRAMES,
    _execution_keys.TILE_FUSED_LEAF_EVALUATIONS,
    _execution_keys.TILE_FUSED_OBSERVATION_DESCENTS,
    _shared_keys.TILE_FUSED_WORKSPACE_PEAK,
    _execution_keys.TILE_FUSED_OBSERVATION_REQUESTS,
    _tiles_keys.SPATIAL_INTERFACE_COMPOSITION_REQUESTS,
    _tiles_keys.SPATIAL_INTERFACE_COMPOSITION_EARLY_HITS,
    _shared_keys.SPATIAL_INTERFACE_COMPOSITION_LATE_ALIASES,
    _shared_keys.SPATIAL_INTERFACE_COMPOSITION_PUBLICATIONS,
    _tiles_keys.SPATIAL_INTERFACE_COMPOSITION_PUBLICATION_REQUESTS,
    _actions_keys.TILE_TEMPORAL_ACTION_HITS,
    _shared_keys.TILE_TEMPORAL_ACTION_PUBLICATIONS,
    _actions_keys.TILE_TEMPORAL_ACTION_SEMANTIC_ALIAS_HITS,
    _actions_keys.REVERSE_FROBENIUS_PLAN_COMPOSITIONS,
    _reverse_add_keys.REVERSE_FIELD_ACTION_SOURCE_ANNIHILATION_DERIVATIONS,
    _collatz_keys.COLLATZ_FIELD_ACTION_SOURCE_ANNIHILATION_DERIVATIONS,
    _execution_keys.TILE_TEMPORAL_COMPLETE_COMPOSITIONS,
    _execution_keys.TILE_TEMPORAL_COMPLETE_FRAMES,
    _tiles_keys.COMPLETED_RESULT_PUBLICATION_REQUESTS,
    _execution_keys.COMPLETED_RESULT_EVALUATIONS,
    _tiles_keys.COMPLETED_RESULT_LATE_DUPLICATE_REDUCTIONS,
    _shared_keys.TILE_SCHEDULER_DEMAND_PARENT_HITS,
    _observation_keys.TILE_SCHEDULER_DEMAND_PARENT_MISSES,
    _tiles_keys.COMPLETED_RESULT_REQUESTS,
    _tiles_keys.COMPLETED_RESULT_EARLY_HITS,
    _tiles_keys.COMPLETED_RESULT_PUBLICATIONS,
    _tiles_keys.COMPLETED_RESULT_TILE_RETIREMENTS,
    _tiles_keys.COMPLETED_RESULT_EVICTIONS,
    _tiles_keys.COMPLETED_RESULT_EVICTED_ENTRIES,
    _tiles_keys.COMPLETED_RESULT_RETIREMENT_MEMO_REMOVALS,
    _tiles_keys.COMPLETED_RESULT_REVERSE_INDEX_REMOVALS,
    _tiles_keys.COMPLETED_RESULT_PRESENCE_INDEX_VISITS,
    _tiles_keys.COMPLETED_RESULT_RETIREMENT_TRAVERSAL_STEPS,
    _tiles_keys.COMPLETED_RESULT_EVICTION_REVERSE_INDEX_ENTRIES,
    _resources_keys.COMPLETED_RESULT_RECOMPUTATION_ATTRIBUTION_UNKNOWN,
    _resources_keys.RESULT_CACHE_KIND_CLASSIFICATION_VISITS,
    "result_cache_result_evicted_entries",
    _tiles_keys.RESULT_CACHE_INTERFACE_EVICTED_ENTRIES,
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
    _tiles_keys.TILE_INTERN_REQUESTS,
    _tiles_keys.TILE_INTERN_EARLY_HITS,
    _tiles_keys.TILE_PUBLICATIONS,
    _tiles_keys.TILE_MIRROR_REQUESTS,
    _tiles_keys.TILE_MIRROR_EARLY_HITS,
    _tiles_keys.TILE_MIRROR_EVALUATIONS,
    _tiles_keys.TILE_MIRROR_PUBLICATIONS,
    _tiles_keys.TILE_RETIREMENTS,
    _tiles_keys.TILE_LEASE_ACQUISITIONS,
    _tiles_keys.TILE_LEASE_RELEASES,
    _tiles_keys.TILE_RETIREMENT_WORK_NS,
    "python_gc_collections_during_tile_retirement",
    "python_gc_collected_during_tile_retirement",
    "python_gc_uncollectable_during_tile_retirement",
    _tiles_keys.TILE_RECREATION_ATTRIBUTION_UNKNOWN,
    _resources_keys.CACHE_EVENT_HISTOGRAM_DROPPED,
    _tiles_keys.TILE_OBSERVATION_DESCENTS,
    _execution_keys.TILE_SCHEDULER_FRAMES,
    "tile_scheduler_demand_descents",
    "tile_scheduler_width_descents",
    _execution_keys.TILE_SCHEDULER_PARENT_EARLY_HITS,
    _shared_keys.TILE_SCHEDULER_MIDPOINT_HITS,
    "tile_scheduler_fused_requests",
    _execution_keys.TILE_SCHEDULER_LEAF_FUNCTION_APPLICATIONS,
    _execution_keys.TILE_SCHEDULER_TEMPORAL_COMPLETE_REQUESTS,
    _execution_keys.TILE_SCHEDULER_SPATIAL_COMPOSITIONS,
    _execution_keys.TILE_SCHEDULER_WORKSPACE_PEAK,
    "canonical_tile_peak",
    _tiles_keys.TILE_ROOT_LEASE_PEAK,
    _tiles_keys.POWERED_INTERFACE_REQUESTS,
    _tiles_keys.POWERED_INTERFACE_EARLY_HITS,
    _tiles_keys.POWERED_INTERFACE_PUBLICATIONS,
    _tiles_keys.POWERED_INTERFACE_PUBLICATION_REQUESTS,
    _tiles_keys.POWERED_INTERFACE_LATE_ALIASES,
    _tiles_keys.TILE_WIDTH_DESCENTS,
    _tiles_keys.COMPLETED_RESULT_PORT_VARIANTS_PEAK,
    _tiles_keys.COMPLETED_RESULT_PORT_VALIDATION_REQUESTS,
    _tiles_keys.COMPLETED_RESULT_PORT_VALIDATION_VISITS,
    _shared_keys.BOUNDARY_TILE_LEASE_PEAK,
    _execution_keys.TILE_BOUNDARY_TRANSFER_REQUESTS,
    _execution_keys.TILE_BOUNDARY_TRANSFER_FRAMES,
    _execution_keys.TILE_BOUNDARY_TRANSFER_PARENT_OBSERVATIONS,
    _execution_keys.TILE_BOUNDARY_TRANSFER_DESCENTS,
    _execution_keys.TILE_BOUNDARY_TRANSFER_WORKSPACE_PEAK,
    _observation_keys.TILE_SOURCE_IMPORTS,
    _observation_keys.TILE_ENDPOINT_PROJECTION_DESCENTS,
    _observation_keys.TILE_ENDPOINT_EMISSIONS,
    _observation_keys.TILE_PROJECTION_WIDTH_OBSERVATIONS,
    _projection_keys.TILE_RADIX_STAGE_PUBLICATIONS,
    _projection_keys.TILE_RADIX_DIGIT_OBSERVATIONS,
    _execution_keys.TILE_SCHEDULER_DIRECT_REQUESTS,
    _execution_keys.TILE_SCHEDULER_SIBLING_TRANSFER_REQUESTS,
    _execution_keys.TILE_SCHEDULER_SIBLING_TRANSFER_EVALUATIONS,
    _execution_keys.TILE_SCHEDULER_DEMANDED_RESULT_PINS,
    _interfaces_keys.PRIMITIVE_TILE_INTERFACE_PUBLICATIONS,
    _execution_keys.TILE_CAUSAL_INTERFACE_MIDPOINT_REUSE,
    _execution_keys.TILE_CAUSAL_INTERFACE_MIDPOINT_PUBLICATIONS,
    _execution_keys.TILE_LEAF_PRODUCT_REQUESTS,
    _execution_keys.TILE_LEAF_PRODUCT_EARLY_HITS,
    _execution_keys.TILE_LEAF_PRODUCT_EVALUATIONS,
    _execution_keys.TILE_LEAF_PRODUCT_PUBLICATIONS,
    _execution_keys.TILE_LEAF_PRODUCT_LATE_ALIASES,
)

# Counts are forwarded only from runtime instrumentation. Presence is reported
# separately, so a missing instrument cannot masquerade as a measured zero.
DIAMOND_WORK_COUNTERS = (
    _execution_keys.MACRO_TRANSFER_REQUESTS,
    _execution_keys.MACRO_TRANSFER_CACHE_HITS,
    _execution_keys.MACRO_TRANSFER_EVALUATIONS,
    _execution_keys.IMAGE_PROGRAM_REQUESTS,
    _execution_keys.IMAGE_PROGRAM_CACHE_HITS,
    _execution_keys.IMAGE_PROGRAM_EVALUATIONS,
    _execution_keys.OUTPUT_FUNCTION_REQUESTS,
    "output_function_cache_hits",
    "output_function_evaluations",
    _execution_keys.CONTEXT_OBSERVATION_REQUESTS,
    _execution_keys.CONTEXT_OBSERVATION_CACHE_HITS,
    _execution_keys.CONTEXT_OBSERVATION_EVALUATIONS,
    _interfaces_keys.UNARY_FUNCTION_COMPOSITION_REQUESTS,
    _interfaces_keys.UNARY_FUNCTION_COMPOSITION_HITS,
    _interfaces_keys.UNARY_FUNCTION_COMPOSITION_EVALUATIONS,
    _interfaces_keys.UNARY_KERNEL_APPLICATION_REQUESTS,
    _interfaces_keys.UNARY_KERNEL_APPLICATION_HITS,
    _interfaces_keys.UNARY_KERNEL_APPLICATION_EVALUATIONS,
    "boundary_substitution_requests",
    "boundary_substitution_cache_hits",
    "boundary_substitution_evaluations",
    _execution_keys.SPATIAL_PARENT_REQUESTS,
    _execution_keys.SPATIAL_PARENT_CACHE_HITS,
    _execution_keys.SPATIAL_PARENT_EVALUATIONS,
    _execution_keys.PRIMITIVE_SPATIAL_REQUESTS,
    _execution_keys.PRIMITIVE_SPATIAL_CACHE_HITS,
    _execution_keys.PRIMITIVE_SPATIAL_EVALUATIONS,
    _execution_keys.PRIMITIVE_SPATIAL_OBSERVATIONS,
    _shared_keys.PRIMITIVE_TRANSITION_EVALUATIONS,
    _shared_keys.PRIMITIVE_OUTPUT_EVALUATIONS,
    _execution_keys.SCALAR_OBSERVATION_REQUESTS,
    "sequential_generation_advances",
    _execution_keys.SCHEDULER_TRANSITIONS,
    _execution_keys.SCHEDULER_WORKSPACE_PEAK,
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
    _interfaces_keys.PRIMITIVE_OCCURRENCE_OBSERVATION_EVALUATIONS,
    _interfaces_keys.PRIMITIVE_BEHAVIOR_REFINEMENT_OBSERVATION_CHECKS,
    _interfaces_keys.PRIMITIVE_BEHAVIOR_REFINEMENT_SUCCESSOR_CHECKS,
    _interfaces_keys.SEMANTIC_EXPRESSION_FINITE_LIFT_REQUESTS,
    _interfaces_keys.SEMANTIC_EXPRESSION_FINITE_LIFT_HITS,
    _interfaces_keys.SEMANTIC_EXPRESSION_FINITE_LIFT_EVALUATIONS,
    _interfaces_keys.SEMANTIC_EXPRESSION_FINITE_LIFT_FRAMES,
    _interfaces_keys.SEMANTIC_STRUCTURE_DECLARATION_REQUESTS,
    _interfaces_keys.SEMANTIC_STRUCTURE_DECLARATION_IDENTITY_HITS,
    _interfaces_keys.SEMANTIC_STRUCTURE_DECLARATION_EARLY_HITS,
    _interfaces_keys.SEMANTIC_STRUCTURE_DECLARATION_EVALUATIONS,
    _shared_keys.PRIMITIVE_MACRO_REQUESTS,
    _interfaces_keys.PRIMITIVE_MACRO_EARLY_HITS,
    _interfaces_keys.PRIMITIVE_MACRO_EVALUATIONS,
    _interfaces_keys.PRIMITIVE_MACRO_COMPILATIONS,
    _interfaces_keys.PRIMITIVE_MACRO_SOURCE_FRAMES,
    _interfaces_keys.PRIMITIVE_MACRO_SPATIAL_COMPOSITIONS,
    _interfaces_keys.PRIMITIVE_MACRO_OBSERVATION_REQUESTS,
    _interfaces_keys.PRIMITIVE_MACRO_OBSERVATION_EVALUATIONS,
    _interfaces_keys.QUOTIENT_PARENT_REQUESTS,
    _interfaces_keys.QUOTIENT_PARENT_EARLY_HITS,
    _interfaces_keys.QUOTIENT_PARENT_PUBLICATIONS,
    _interfaces_keys.QUOTIENT_COMPLETE_NORMALIZATIONS,
    _interfaces_keys.QUOTIENT_SEMANTIC_INTERNER_EVALUATIONS,
    _interfaces_keys.QUOTIENT_NORMAL_FORM_EARLY_HITS,
    _interfaces_keys.QUOTIENT_SEMANTIC_INTERNER_HITS,
    _functions_keys.SEMANTIC_FUNCTION_REQUESTS,
    _functions_keys.SEMANTIC_FUNCTION_REQUEST_HITS,
    _functions_keys.SEMANTIC_FUNCTION_EVALUATIONS,
    _functions_keys.SEMANTIC_FUNCTION_DECISION_VISITS,
    _functions_keys.SEMANTIC_FUNCTION_ITE_FRAMES,
    _functions_keys.SEMANTIC_FUNCTION_REWRITE_FRAMES,
    _functions_keys.SEMANTIC_FUNCTION_STAGED_NODES,
    _interfaces_keys.SEMANTIC_FUNCTION_PUBLISHED_NODES,
    _interfaces_keys.SEMANTIC_BIT_ADMISSIBILITY_REQUESTS,
    _interfaces_keys.SEMANTIC_BIT_ADMISSIBILITY_EARLY_HITS,
    _interfaces_keys.SEMANTIC_BIT_ADMISSIBILITY_EVALUATIONS,
    _interfaces_keys.SEMANTIC_BIT_ADMISSIBILITY_PUBLICATIONS,
    _interfaces_keys.SEMANTIC_EXPRESSION_TASKS,
    _interfaces_keys.SEMANTIC_BINARY_DIVISION_COMPILATIONS,
)

# A field-action executor installs every counter, including observed zeros, when
# it is constructed.  This lets reporting distinguish missing instrumentation
# from measured absence without consulting a second executor snapshot.
ALGEBRAIC_FIELD_WORK_COUNTERS = (
    _shared_keys.TEMPORAL_PARENT_REQUESTS,
    _shared_keys.TEMPORAL_PARENT_EARLY_HITS,
    _shared_keys.TEMPORAL_PARENT_COMPOSITIONS,
    _collatz_keys.TEMPORAL_PARENT_LATE_DUPLICATE_REDUCTIONS,
    _reverse_add_keys.RADIAL_ACTION_OPERATIONS,
    _reverse_add_keys.CARRY_ACTION_OPERATIONS,
    "character_action_operations",
    "affine_action_operations",
    _reverse_add_keys.INNOVATION_ACTION_OPERATIONS,
    _reverse_add_keys.OUTPUT_MORPHISM_OPERATIONS,
    _reverse_add_keys.RESIDUAL_REFINEMENT_OPERATIONS,
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
    _execution_keys.POINT_OBSERVATIONS,
    _execution_keys.WIDTH_OBSERVATIONS,
    _projection_keys.RADIX_FIXED_CYCLE_OBSERVATIONS,
    _projection_keys.RADIX_PROVIDER_DIGIT_REQUESTS,
    _projection_keys.RADIX_PROVIDER_DIGIT_EARLY_HITS,
    _projection_keys.RADIX_PROVIDER_DIGIT_EVALUATIONS,
    _execution_keys.RADIX_TEMPORAL_ACTION_REQUESTS,
    _execution_keys.RADIX_TEMPORAL_ACTION_EARLY_HITS,
    _execution_keys.RADIX_TEMPORAL_ACTION_EVALUATIONS,
    "radix_recursive_transfer_requests",
    "radix_recursive_transfer_early_hits",
    _radix_transfer_keys.RADIX_RECURSIVE_TRANSFER_EVALUATIONS,
    "radix_recursive_descents",
    "radix_source_bit_visits",
    _shared_keys.RADIX_LIMB_OPERATIONS,
    _execution_keys.HIGHER_POINT_OBSERVATIONS,
    _execution_keys.HIGHER_WIDTH_OBSERVATIONS,
    _execution_keys.HIGHER_OBSERVATION_FALLBACK,
    _execution_keys.HIGHER_RANGE_DYADIC_CELLS,
    _execution_keys.HIGHER_CONCRETE_OPERATION_EVALUATIONS,
    _execution_keys.HIGHER_CONCRETE_OPERATION_HITS,
    "higher_concrete_initial_evaluations",
    "higher_concrete_step_evaluations",
    "higher_concrete_emit_evaluations",
    "higher_concrete_apply_evaluations",
    "higher_concrete_force_evaluations",
    _execution_keys.HIGHER_PRIMITIVE_STEP_HITS,
    _execution_keys.HIGHER_PRIMITIVE_STEP_PUBLICATIONS,
    _execution_keys.HIGHER_PRIMITIVE_OUTPUT_HITS,
    _execution_keys.HIGHER_PRIMITIVE_OUTPUT_PUBLICATIONS,
    _execution_keys.HIGHER_SUMMARY_TEMPORAL_COMPOSITIONS,
    _execution_keys.HIGHER_SUMMARY_SPATIAL_COMPOSITIONS,
    _execution_keys.HIGHER_CONTEXT_SPATIAL_COMPOSITIONS,
    "reverse_temporal_leaf_substitutions",
    "reverse_temporal_parent_substitutions",
    "reverse_temporal_prefix_image_observations",
    "collatz_temporal_leaf_substitutions",
    "collatz_temporal_parent_substitutions",
    "collatz_temporal_prefix_image_observations",
    "collatz_complete_leaf_interface_observations",
    "collatz_complete_leaf_interface_early_hits",
    _tiles_keys.COLLATZ_SOURCE_ROOT_MATCH_REQUESTS,
    _tiles_keys.COLLATZ_SOURCE_ROOT_MATCH_EARLY_HITS,
    _tiles_keys.COLLATZ_SOURCE_ROOT_MATCH_EVALUATIONS,
    _tiles_keys.COLLATZ_SOURCE_ROOT_MATCH_PUBLICATIONS,
    _tiles_keys.COLLATZ_SOURCE_ROOT_MATCH_LATE_DUPLICATES,
    _execution_keys.REVERSE_ACTIVE_TRANSFER_EVALUATIONS,
    _execution_keys.REVERSE_ACTIVE_TRANSFER_DECLINES,
    "reverse_boundary_transfer_publications",
    _execution_keys.REVERSE_BOUNDARY_TRANSFER_COMPLETIONS,
    "collatz_radix_boundary_validation_requests",
    "collatz_radix_boundary_validation_visits",
    "collatz_radix_boundary_proof_hits",
    "collatz_radix_boundary_proof_publications",
    _execution_keys.OPAQUE_HIGHER_OPERATION_PUBLICATIONS,
    _execution_keys.HIGHER_OPERATION_EARLY_HITS,
    _projection_keys.RADIX_OBSERVATIONS,
    "endpoint_emissions",
    _shared_keys.FIELD_ACTION_PUBLICATIONS,
    _execution_keys.OUTPUT_MORPHISM_PUBLICATIONS,
    "image_publications",
    _projection_keys.MICROBLOCK_PUBLICATIONS,
    _execution_keys.NEW_FIELD_IMAGE_NODES,
    _execution_keys.FIELD_IMAGE_BINDING_REQUESTS,
    _execution_keys.FIELD_IMAGE_BINDING_EARLY_HITS,
    _projection_keys.MICROBLOCK_PAYLOAD_BYTES,
    _projection_keys.MICROBLOCK_PAYLOAD_HIGH_WATER_BYTES,
    _projection_keys.MICROBLOCK_ENTRY_HIGH_WATER,
    _execution_keys.SOURCE_LEAF_VISITS,
    "transient_buffer_allocations",
    "proof_machine_artifacts_loaded_by_runtime",
    _execution_keys.ALGEBRAIC_EXECUTOR_CAPABILITY_VALIDATED,
    _execution_keys.NEW_FIELD_TRANSFER_NODES,
    _execution_keys.FIELD_TRANSFER_BINDING_REQUESTS,
    _execution_keys.FIELD_TRANSFER_BINDING_EARLY_HITS,
    _execution_keys.FIELD_TRANSFER_BINDING_PUBLICATIONS,
    _execution_keys.FIELD_TRANSFER_SEMANTIC_ALIAS_HITS,
    "local_interface_compositions",
    "local_interface_alias_hits",
    _shared_keys.OUTPUT_MORPHISM_VISITS,
    _execution_keys.FIELD_IMAGE_PARENT_OBSERVATION_REQUESTS,
    "field_image_parent_observation_early_hits",
    "field_image_parent_observation_evaluations",
    _execution_keys.PROVIDER_FUSED_POINT_REQUESTS,
    _execution_keys.PROVIDER_FUSED_POINT_EARLY_HITS,
    _execution_keys.PROVIDER_FUSED_POINT_EVALUATIONS,
    _execution_keys.PROVIDER_FUSED_WIDTH_REQUESTS,
    _execution_keys.PROVIDER_FUSED_WIDTH_EARLY_HITS,
    _execution_keys.PROVIDER_FUSED_WIDTH_EVALUATIONS,
    _execution_keys.CONCRETE_PORT_TASK_FRAMES,
    _execution_keys.CONCRETE_PROVIDER_LAYER_PUBLICATIONS,
    _execution_keys.CONCRETE_IRRELEVANT_PORT_ELISIONS,
    _projection_keys.ENDPOINT_MIRROR_REUSES,
    _projection_keys.ENDPOINT_MIRROR_BUFFER_PEAK_BYTES,
    "temporal_leaf_diamond_descents",
    _execution_keys.HIGHER_SEMANTIC_EVALUATIONS,
    _execution_keys.HIGHER_SEMANTIC_TASK_FRAMES,
    _execution_keys.HIGHER_ACTION_CONTINUATION_REQUESTS,
    "temporal_leaf_parent_hits",
    "temporal_leaf_parent_publications",
    _execution_keys.HIGHER_IDENTITY_TRANSFER_ELISIONS,
    _execution_keys.GENERIC_HIGHER_ACTION_EARLY_HITS,
    _execution_keys.GENERIC_HIGHER_ACTION_PUBLICATIONS,
    _execution_keys.PARAMETRIC_WIDTH_FOREST_VISITS,
    _execution_keys.PARAMETRIC_WIDTH_PARENT_VISITS,
    _execution_keys.PARAMETRIC_WIDTH_DESCENT_STEPS,
    "parametric_width_contexts_peak",
    _execution_keys.HIGHER_BOUNDARY_RESOLUTION_HITS,
    _execution_keys.HIGHER_RUNTIME_COMPOSITION_REQUESTS,
    _execution_keys.HIGHER_RUNTIME_COMPOSITION_HITS,
    _execution_keys.HIGHER_RUNTIME_INTERCHANGE_COMPOSITIONS,
    _execution_keys.HIGHER_FINITE_TRANSFER_STATE_VISITS,
    _execution_keys.HIGHER_FINITE_TRANSFER_EVALUATIONS,
    _execution_keys.HIGHER_FINITE_TRANSFER_COMPOSITIONS,
    _execution_keys.CONCRETE_PROVIDER_LAYER_ALIAS_HITS,
    _execution_keys.CONCRETE_PORT_TASK_REQUESTS,
    _execution_keys.CONCRETE_PORT_TASK_EARLY_HITS,
    _execution_keys.CONCRETE_PORT_TASK_EVALUATIONS,
    _execution_keys.CONCRETE_VIRTUAL_INTERFACE_REQUESTS,
    _execution_keys.CONCRETE_VIRTUAL_INTERFACE_EARLY_HITS,
    _execution_keys.CONCRETE_VIRTUAL_INTERFACE_EVALUATIONS,
    _execution_keys.CONCRETE_VIRTUAL_INTERFACE_PUBLICATIONS,
    _execution_keys.CONCRETE_VIRTUAL_INTERFACE_ALIAS_HITS,
    _execution_keys.RECURSIVE_FIELD_IMAGE_REQUESTS,
    _execution_keys.RECURSIVE_FIELD_IMAGE_EARLY_HITS,
    _execution_keys.RECURSIVE_FIELD_IMAGE_TEMPORAL_COMPOSITIONS,
    _execution_keys.RECURSIVE_FIELD_IMAGE_SPATIAL_COMPOSITIONS,
    _execution_keys.RECURSIVE_FIELD_IMAGE_PRIMITIVE_EVALUATIONS,
    _execution_keys.RECURSIVE_FIELD_FOREST_REQUESTS,
    _execution_keys.RECURSIVE_FIELD_FOREST_EARLY_HITS,
    _execution_keys.RECURSIVE_FIELD_FOREST_SPATIAL_COMPOSITIONS,
    _execution_keys.RECURSIVE_FIELD_FOREST_PRIMITIVE_EVALUATIONS,
)

CANONICAL_EXPRESSION_VISIT_COUNTERS = (
    _actions_keys.DIAMOND_TEMPORAL_IMPORT_VISITS,
    _actions_keys.DIAMOND_SLICE_NORMALIZATION_VISITS,
    _interfaces_keys.FINITE_EXPRESSION_COMPONENT_CHECKS,
    _functions_keys.FINITE_PORT_SUBSTITUTION_SUPPORT_FRAME_POPS,
    _functions_keys.FINITE_PORT_SUBSTITUTION_PUBLICATION_VISITS,
    _functions_keys.SEMANTIC_FUNCTION_DECISION_VISITS,
    _functions_keys.SEMANTIC_FUNCTION_ITE_FRAMES,
    _functions_keys.SEMANTIC_FUNCTION_REWRITE_FRAMES,
    "unary_function_admission_visits",
    "unary_function_admission_frame_visits",
    _interfaces_keys.SEMANTIC_EXPRESSION_FINITE_LIFT_FRAMES,
    _interfaces_keys.UNARY_CORRELATED_COFACTOR_VISITS,
    _execution_keys.HIGHER_CONTEXT_ADMISSION_VISITS,
    "context_variable_support_visits",
    "context_variable_support_frame_visits",
    _interfaces_keys.DIAMOND_FINITE_BRIDGE_VISITS,
    _interfaces_keys.DIAMOND_FINITE_BRIDGE_ADMISSION_VISITS,
    _interfaces_keys.BOUNDARY_DECISION_VISITS,
    _execution_keys.IMAGE_PROGRAM_ADMISSION_VISITS,
    _interfaces_keys.CAUSAL_HALO_DAG_VISITS,
    _interfaces_keys.CAUSAL_HALO_KERNEL_CHECKS,
)


def schema7_work_values(counters: Mapping[str, int]) -> dict[str, int]:
    """Map actual executor instruments into the stable schema-seven vocabulary."""
    values = {name: counters.get(name, 0) for name in ALGEBRAIC_FIELD_WORK_COUNTERS}
    values.update((name, counters.get(name, 0)) for name in TILE_WORK_COUNTERS)
    # The concrete scheduler records misses as ``*_requests`` because its
    # early probe precedes the compilation path.  Public request fields count
    # every probe, while the raw snapshot preserves the independently observed
    # miss and early-hit instruments.
    values[_execution_keys.CONCRETE_PORT_TASK_REQUESTS] = counters.get(
        _execution_keys.CONCRETE_PORT_TASK_REQUESTS, 0
    ) + counters.get(_execution_keys.CONCRETE_PORT_TASK_EARLY_HITS, 0)
    values[_execution_keys.CONCRETE_VIRTUAL_INTERFACE_REQUESTS] = counters.get(
        _execution_keys.CONCRETE_VIRTUAL_INTERFACE_REQUESTS, 0
    ) + counters.get(_execution_keys.CONCRETE_VIRTUAL_INTERFACE_EARLY_HITS, 0)
    aliases = {
        _shared_keys.TEMPORAL_PARENT_REQUESTS: _shared_keys.DIAMOND_TEMPORAL_COMPOSITION_REQUESTS,
        _shared_keys.TEMPORAL_PARENT_EARLY_HITS: _shared_keys.DIAMOND_TEMPORAL_COMPOSITION_HITS,
        _shared_keys.TEMPORAL_PARENT_COMPOSITIONS: _shared_keys.DIAMOND_TEMPORAL_COMPOSITION_EVALUATIONS,
        "spatial_descents": _observation_keys.WIDTH_DESCENT_STEPS,
        _execution_keys.WIDTH_OBSERVATIONS: _observation_keys.WIDTH_QUERIES,
        "endpoint_emissions": _projection_keys.EXPLICITLY_LOWERED_DIGITS,
        "image_publications": _actions_keys.DIAMOND_CELL_INTERNER_EVALUATIONS,
        _projection_keys.MICROBLOCK_PUBLICATIONS: _projection_keys.MICROBLOCK_PUBLICATIONS,
        _execution_keys.SOURCE_LEAF_VISITS: _contracts_keys.SOURCE_LEAF_READS,
        "proof_machine_artifacts_loaded_by_runtime": "proof_machine_artifacts_loaded_by_runtime",
    }
    for public, instrument in aliases.items():
        if public not in counters:
            values[public] = counters.get(instrument, 0)
    if _execution_keys.POINT_OBSERVATIONS not in counters:
        values[_execution_keys.POINT_OBSERVATIONS] = counters.get(
            _observation_keys.DIAMOND_POINT_QUERIES, 0
        )
    if _projection_keys.RADIX_OBSERVATIONS not in counters:
        values[_projection_keys.RADIX_OBSERVATIONS] = sum(
            counters.get(name, 0)
            for name in (
                _projection_keys.RADIX_FUSED_DIGIT_QUERIES,
                _projection_keys.ORIGINAL_RADIX_POINT_QUERIES,
                _projection_keys.RADIX_ORIGINAL_AFFINE_DIGIT_QUERIES,
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
            _reverse_add_keys.RADIAL_ACTION_OPERATIONS,
            _reverse_add_keys.CARRY_ACTION_OPERATIONS,
            "character_action_operations",
            "affine_action_operations",
            _reverse_add_keys.INNOVATION_ACTION_OPERATIONS,
            _reverse_add_keys.OUTPUT_MORPHISM_OPERATIONS,
            _reverse_add_keys.RESIDUAL_REFINEMENT_OPERATIONS,
        )
    )
    values[_execution_keys.SPATIAL_PARENT_CACHE_HITS] = counters.get(
        _execution_keys.SPATIAL_PARENT_CACHE_HITS,
        0,
    ) + counters.get("spatial_parent_early_hits", 0)
    values[_reverse_add_keys.NONLINEAR_BRANCH_EVALUATIONS] = counters.get(
        _reverse_add_keys.NONLINEAR_BRANCH_EVALUATIONS,
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
    if _shared_keys.FIELD_ACTION_PUBLICATIONS not in counters:
        values[_shared_keys.FIELD_ACTION_PUBLICATIONS] = sum(
            counters.get(name, 0)
            for name in (
                "reverse_field_action_publications",
                _collatz_keys.COLLATZ_FIELD_ACTION_PUBLICATIONS,
                _shared_keys.TILE_TEMPORAL_ACTION_PUBLICATIONS,
            )
        )
    image_publications = counters.get(_execution_keys.NEW_FIELD_IMAGE_NODES, 0)
    values[_execution_keys.NEW_FIELD_IMAGE_NODES] = image_publications
    values[_execution_keys.FIELD_IMAGE_BINDING_REQUESTS] = counters.get(
        _execution_keys.FIELD_IMAGE_BINDING_REQUESTS,
        0,
    )
    values[_execution_keys.FIELD_IMAGE_BINDING_EARLY_HITS] = counters.get(
        _execution_keys.FIELD_IMAGE_BINDING_EARLY_HITS,
        0,
    )
    if (
        "image_publications" not in counters
        and _execution_keys.ALGEBRAIC_EXECUTOR_CAPABILITY_VALIDATED in counters
    ):
        values["image_publications"] = image_publications
    values["new_canonical_field_images_published"] = image_publications
    values["field_image_publication_requests"] = counters.get(
        "field_image_publication_requests",
        counters.get(
            _execution_keys.FIELD_IMAGE_BINDING_REQUESTS,
            counters.get(_execution_keys.IMAGE_PROGRAM_REQUESTS, 0),
        ),
    )
    values["field_image_early_hits"] = counters.get(
        "field_image_early_hits",
        counters.get(
            _execution_keys.FIELD_IMAGE_BINDING_EARLY_HITS,
            counters.get(_execution_keys.IMAGE_PROGRAM_CACHE_HITS, 0),
        ),
    )
    values["field_interface_publications"] = counters.get(
        "field_interface_publications",
        counters.get(_execution_keys.HIGHER_INTERFACE_PUBLICATIONS, 0)
        + counters.get(_interfaces_keys.QUOTIENT_SEMANTIC_INTERNER_EVALUATIONS, 0),
    )
    values["field_interface_early_hits"] = counters.get(
        "field_interface_early_hits",
        counters.get(_execution_keys.HIGHER_INTERFACE_NORMAL_FORM_HITS, 0)
        + counters.get(_interfaces_keys.QUOTIENT_NORMAL_FORM_EARLY_HITS, 0),
    )
    # Frames refine semantic-call counts. Preserve the legacy coarse count
    # when only it was instrumented, without counting a call twice alongside
    # the frames that execute it.
    higher_work = max(
        counters.get(_execution_keys.HIGHER_SEMANTIC_TASK_FRAMES, 0),
        counters.get(_execution_keys.HIGHER_SEMANTIC_EVALUATIONS, 0),
    )
    values["total_internal_action_work"] = (
        higher_work
        + sum(
            values[name]
            for name in (
                _shared_keys.TEMPORAL_PARENT_COMPOSITIONS,
                "canonical_expression_node_visits",
                "field_action_component_operations",
                _reverse_add_keys.NONLINEAR_BRANCH_EVALUATIONS,
            )
        )
        + sum(
            counters.get(name, 0)
            for name in (
                _execution_keys.SPATIAL_PARENT_EVALUATIONS,
                "boundary_substitution_evaluations",
                _shared_keys.PRIMITIVE_TRANSITION_EVALUATIONS,
                _shared_keys.PRIMITIVE_OUTPUT_EVALUATIONS,
                _execution_keys.FIELD_TRANSFER_PARENT_EVALUATIONS,
                _execution_keys.FIELD_IMAGE_PARENT_EVALUATIONS,
                "higher_operation_publications",
                _execution_keys.HIGHER_ACTION_CONTINUATION_REQUESTS,
                _execution_keys.HIGHER_CONCRETE_OPERATION_EVALUATIONS,
                _execution_keys.HIGHER_CONCRETE_OPERATION_HITS,
                _execution_keys.HIGHER_RUNTIME_COMPOSITION_REQUESTS,
                _execution_keys.HIGHER_FINITE_TRANSFER_STATE_VISITS,
                _execution_keys.HIGHER_PRIMITIVE_STEP_HITS,
                _execution_keys.HIGHER_PRIMITIVE_STEP_PUBLICATIONS,
                _execution_keys.HIGHER_PRIMITIVE_OUTPUT_HITS,
                _execution_keys.HIGHER_PRIMITIVE_OUTPUT_PUBLICATIONS,
                _execution_keys.OPAQUE_HIGHER_OPERATION_PUBLICATIONS,
                _execution_keys.HIGHER_OPERATION_EARLY_HITS,
                _execution_keys.HIGHER_SPATIAL_TRANSFER_PUBLICATIONS,
                _execution_keys.HIGHER_RANGE_DYADIC_CELLS,
                _execution_keys.SPATIAL_OBSERVATION_DESCENTS,
                _execution_keys.GENERIC_HIGHER_ACTION_EARLY_HITS,
                _execution_keys.GENERIC_HIGHER_ACTION_PUBLICATIONS,
                _execution_keys.PARAMETRIC_WIDTH_FOREST_VISITS,
                _execution_keys.PARAMETRIC_WIDTH_PARENT_VISITS,
                _execution_keys.PARAMETRIC_WIDTH_DESCENT_STEPS,
                _execution_keys.PROVIDER_FUSED_POINT_EVALUATIONS,
                _execution_keys.PROVIDER_FUSED_WIDTH_EVALUATIONS,
                _execution_keys.CONCRETE_PORT_TASK_EVALUATIONS,
                _execution_keys.CONCRETE_PORT_TASK_FRAMES,
                _execution_keys.CONCRETE_VIRTUAL_INTERFACE_EVALUATIONS,
                _execution_keys.RECURSIVE_FIELD_IMAGE_TEMPORAL_COMPOSITIONS,
                _execution_keys.RECURSIVE_FIELD_IMAGE_SPATIAL_COMPOSITIONS,
                _execution_keys.RECURSIVE_FIELD_IMAGE_PRIMITIVE_EVALUATIONS,
                _execution_keys.RECURSIVE_FIELD_FOREST_SPATIAL_COMPOSITIONS,
                "reverse_temporal_prefix_image_observations",
                "collatz_temporal_prefix_image_observations",
                _execution_keys.RECURSIVE_FIELD_FOREST_PRIMITIVE_EVALUATIONS,
                _radix_transfer_keys.RADIX_RECURSIVE_TRANSFER_EVALUATIONS,
                _execution_keys.RADIX_TEMPORAL_ACTION_EVALUATIONS,
                "radix_recursive_descents",
                "radix_source_bit_visits",
                _shared_keys.RADIX_LIMB_OPERATIONS,
                "temporal_leaf_diamond_descents",
                "temporal_leaf_parent_hits",
                "temporal_leaf_parent_publications",
                "collatz_radix_boundary_validation_visits",
                "collatz_radix_boundary_proof_hits",
                _tiles_keys.COMPLETED_RESULT_REQUESTS,
                _tiles_keys.COMPLETED_RESULT_PUBLICATION_REQUESTS,
                _tiles_keys.TILE_INTERN_REQUESTS,
                _tiles_keys.SPATIAL_INTERFACE_COMPOSITION_REQUESTS,
                _tiles_keys.SPATIAL_INTERFACE_COMPOSITION_PUBLICATION_REQUESTS,
                _tiles_keys.FUSED_INTERFACE_PUBLICATION_REQUESTS,
                _tiles_keys.FUSED_INTERFACE_REQUESTS,
                _execution_keys.TILE_FUSED_FRAMES,
                _execution_keys.POWERED_ABSORPTION_REQUESTS,
                "proof_artifact_loading_work",
                _execution_keys.TILE_FUSED_LEAF_EVALUATIONS,
                _execution_keys.TILE_FUSED_OBSERVATION_DESCENTS,
                _execution_keys.TILE_FUSED_OBSERVATION_REQUESTS,
                _tiles_keys.TILE_LEASE_ACQUISITIONS,
                _tiles_keys.TILE_LEASE_RELEASES,
                _tiles_keys.TILE_RETIREMENTS,
                _tiles_keys.TILE_OBSERVATION_DESCENTS,
                _execution_keys.TILE_SCHEDULER_FRAMES,
                "tile_scheduler_demand_descents",
                "tile_scheduler_width_descents",
                _execution_keys.TILE_SCHEDULER_LEAF_FUNCTION_APPLICATIONS,
                _tiles_keys.POWERED_INTERFACE_REQUESTS,
                _tiles_keys.TILE_WIDTH_DESCENTS,
                _observation_keys.TILE_ENDPOINT_PROJECTION_DESCENTS,
                _observation_keys.TILE_ENDPOINT_EMISSIONS,
                _execution_keys.TILE_SCHEDULER_SIBLING_TRANSFER_REQUESTS,
                _interfaces_keys.PRIMITIVE_TILE_INTERFACE_PUBLICATIONS,
                _execution_keys.TILE_LEAF_PRODUCT_REQUESTS,
                _projection_keys.TILE_RADIX_STAGE_PUBLICATIONS,
                _projection_keys.TILE_RADIX_DIGIT_OBSERVATIONS,
                _execution_keys.TILE_TEMPORAL_COMPLETE_FRAMES,
                _shared_keys.TILE_TEMPORAL_ACTION_PUBLICATIONS,
            )
        )
    )
    return values


def schema7_inventory_values(inventory: Iterable[ResourceInventory]) -> dict[str, int]:
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
        _interfaces_keys.OUTPUT_MORPHISM_NODES: nodes(
            "output_morphism",
            "reverse_output_morphism",
            "coordinate_output_morphism",
        ),
    }


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
            if isinstance(container, Sequence):
                values = cast(Sequence[object], container)
                if len(values) == nodes:
                    images = sum(
                        type(value) is CellNode and value.kind == "image"
                        for value in values
                    )
                    counts["image_action_nodes"] += images
                    nodes -= images
        counts[category] += nodes
    return counts

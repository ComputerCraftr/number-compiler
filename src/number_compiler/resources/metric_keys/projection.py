"""Stable counter names for projection execution."""

from typing import Final

ENDPOINT_LOWERING_REQUESTS: Final = "endpoint_lowering_requests"
ENDPOINT_MIRROR_BUFFER_PEAK_BYTES: Final = "endpoint_mirror_buffer_peak_bytes"
ENDPOINT_MIRROR_REUSES: Final = "endpoint_mirror_reuses"
EXPLICITLY_LOWERED_DIGITS: Final = "explicitly_lowered_digits"
EXPLICITLY_MATERIALIZED_ENDPOINTS: Final = "explicitly_materialized_endpoints"
MICROBLOCK_ENTRY_HIGH_WATER: Final = "microblock_entry_high_water"
MICROBLOCK_EVICTIONS: Final = "microblock_evictions"
MICROBLOCK_HITS: Final = "microblock_hits"
MICROBLOCK_PAYLOAD_BYTES: Final = "microblock_payload_bytes"
MICROBLOCK_PAYLOAD_HIGH_WATER_BYTES: Final = "microblock_payload_high_water_bytes"
MICROBLOCK_PUBLICATIONS: Final = "microblock_publications"
MICROBLOCK_REQUESTS: Final = "microblock_requests"
ORIGINAL_AFFINE_PREFIX_SUMMARY_VISITS: Final = "original_affine_prefix_summary_visits"
ORIGINAL_AFFINE_SHIFT_COMPOSITIONS: Final = "original_affine_shift_compositions"
ORIGINAL_AFFINE_SHIFT_SUMMARY_VISITS: Final = "original_affine_shift_summary_visits"
ORIGINAL_AFFINE_SUMMARY_DIVISION_CELLS: Final = "original_affine_summary_division_cells"
ORIGINAL_AFFINE_SUMMARY_FAILURES: Final = "original_affine_summary_failures"
ORIGINAL_AFFINE_SUMMARY_HITS: Final = "original_affine_summary_hits"
ORIGINAL_AFFINE_SUMMARY_LIMB_OPERATIONS: Final = (
    "original_affine_summary_limb_operations"
)
ORIGINAL_AFFINE_SUMMARY_PARENT_CELLS: Final = "original_affine_summary_parent_cells"
ORIGINAL_AFFINE_SUMMARY_PUBLICATIONS: Final = "original_affine_summary_publications"
ORIGINAL_AFFINE_SUMMARY_REQUESTS: Final = "original_affine_summary_requests"
ORIGINAL_AFFINE_SUMMARY_SOURCE_CELLS: Final = "original_affine_summary_source_cells"
ORIGINAL_AFFINE_SUMMARY_TRANSITION_EVALUATIONS: Final = (
    "original_affine_summary_transition_evaluations"
)
ORIGINAL_AFFINE_SUMMARY_WORKSPACE_SLOTS_PEAK: Final = (
    "original_affine_summary_workspace_slots_peak"
)
ORIGINAL_RADIX_BOUNDED_POINT_QUERIES: Final = "original_radix_bounded_point_queries"
ORIGINAL_RADIX_BOUNDED_SOURCE_BIT_READS: Final = (
    "original_radix_bounded_source_bit_reads"
)
ORIGINAL_RADIX_ENCODING_HITS: Final = "original_radix_encoding_hits"
ORIGINAL_RADIX_LIMB_OPERATIONS: Final = "original_radix_limb_operations"
ORIGINAL_RADIX_POINT_QUERIES: Final = "original_radix_point_queries"
ORIGINAL_RADIX_SHIFT_DIVISION_CELLS: Final = "original_radix_shift_division_cells"
ORIGINAL_RADIX_SHIFT_LIMB_OPERATIONS: Final = "original_radix_shift_limb_operations"
ORIGINAL_RADIX_SHIFT_LIVE_BUFFER_LIMBS_PEAK: Final = (
    "original_radix_shift_live_buffer_limbs_peak"
)
ORIGINAL_RADIX_SHIFT_OPERAND_LIMBS_PEAK: Final = (
    "original_radix_shift_operand_limbs_peak"
)
ORIGINAL_RADIX_SHIFT_PRODUCT_BUFFER_LIMBS_PEAK: Final = (
    "original_radix_shift_product_buffer_limbs_peak"
)
ORIGINAL_RADIX_SHIFT_QUOTIENT_BUFFER_LIMBS_PEAK: Final = (
    "original_radix_shift_quotient_buffer_limbs_peak"
)
ORIGINAL_RADIX_SHIFT_SMALL_CELLS: Final = "original_radix_shift_small_cells"
ORIGINAL_RADIX_SHIFT_SOURCE_DIGIT_READS: Final = (
    "original_radix_shift_source_digit_reads"
)
ORIGINAL_RADIX_SHIFT_WIDE_CELLS: Final = "original_radix_shift_wide_cells"
ORIGINAL_RADIX_SHIFT_WORD_MULTIPLICATIONS: Final = (
    "original_radix_shift_word_multiplications"
)
ORIGINAL_RADIX_SOURCE_BIT_READS: Final = "original_radix_source_bit_reads"
ORIGINAL_RADIX_WORKSPACE_LIMBS_PEAK: Final = "original_radix_workspace_limbs_peak"
POINT_RESPONSE_CACHE_HITS: Final = "point_response_cache_hits"
POINT_RESPONSE_EVALUATIONS: Final = "point_response_evaluations"
POINT_RESPONSE_REQUESTS: Final = "point_response_requests"
RADIX_FIXED_CYCLE_OBSERVATIONS: Final = "radix_fixed_cycle_observations"
RADIX_FUSED_ACTIONS_PUBLISHED: Final = "radix_fused_actions_published"
RADIX_FUSED_BINDING_HITS: Final = "radix_fused_binding_hits"
RADIX_FUSED_DIGIT_QUERIES: Final = "radix_fused_digit_queries"
RADIX_FUSED_LEAF_COMPILATIONS: Final = "radix_fused_leaf_compilations"
RADIX_FUSED_ORIGINAL_SOURCE_READS: Final = "radix_fused_original_source_reads"
RADIX_FUSED_PARENT_COMPOSITIONS: Final = "radix_fused_parent_compositions"
RADIX_FUSED_PARENT_CONSTRUCTION_HITS: Final = "radix_fused_parent_construction_hits"
RADIX_FUSED_PARENT_RECORDS_PEAK: Final = "radix_fused_parent_records_peak"
RADIX_FUSED_PARENT_STACK_PEAK: Final = "radix_fused_parent_stack_peak"
RADIX_FUSED_SPATIAL_LEAF_VISITS: Final = "radix_fused_spatial_leaf_visits"
RADIX_FUSED_SUBSTITUTION_FRAMES: Final = "radix_fused_substitution_frames"
RADIX_FUSED_SUBSTITUTION_VISITS: Final = "radix_fused_substitution_visits"
RADIX_FUSED_SUBSTITUTION_WORKSPACE_PEAK: Final = (
    "radix_fused_substitution_workspace_peak"
)
RADIX_NATIVE_BOUNDED_SOURCE_QUERIES: Final = "radix_native_bounded_source_queries"
RADIX_NATIVE_ORIGINAL_BIT_READS: Final = "radix_native_original_bit_reads"
RADIX_OBSERVATIONS: Final = "radix_observations"
RADIX_ORIGINAL_AFFINE_CARRY_CELLS: Final = "radix_original_affine_carry_cells"
RADIX_ORIGINAL_AFFINE_DIGIT_QUERIES: Final = "radix_original_affine_digit_queries"
RADIX_PROVIDER_DIGIT_EARLY_HITS: Final = "radix_provider_digit_early_hits"
RADIX_PROVIDER_DIGIT_EVALUATIONS: Final = "radix_provider_digit_evaluations"
RADIX_PROVIDER_DIGIT_REQUESTS: Final = "radix_provider_digit_requests"
TILE_RADIX_BINARY_POWER_OBSERVATIONS: Final = "tile_radix_binary_power_observations"
TILE_RADIX_COMPLETED_STAGE_REUSE_SPAN: Final = "tile_radix_completed_stage_reuse_span"
TILE_RADIX_COMPLETED_STAGE_REUSES: Final = "tile_radix_completed_stage_reuses"
TILE_RADIX_DIGIT_OBSERVATIONS: Final = "tile_radix_digit_observations"
TILE_RADIX_DIRECT_POWER_STAGES: Final = "tile_radix_direct_power_stages"
TILE_RADIX_INTERFACE_OBSERVATIONS: Final = "tile_radix_interface_observations"
TILE_RADIX_OBSERVATION_EARLY_HITS: Final = "tile_radix_observation_early_hits"
TILE_RADIX_OBSERVATION_PUBLICATIONS: Final = "tile_radix_observation_publications"
TILE_RADIX_STAGE_EARLY_HITS: Final = "tile_radix_stage_early_hits"
TILE_RADIX_STAGE_PEAK: Final = "tile_radix_stage_peak"
TILE_RADIX_STAGE_PUBLICATIONS: Final = "tile_radix_stage_publications"

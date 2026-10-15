"""Immutable schema-eight temporal observation records."""

from __future__ import annotations

from dataclasses import dataclass, field

from number_compiler.resources.cellular_diagnostics import CellularTemporalWork
from number_compiler.resources.reuse_diagnostics import (
    CompleteActionReuse,
    TemporalReuseLane,
)

METRICS_SCHEMA_VERSION = 8


@dataclass(frozen=True, slots=True)
class TemporalConstruction:
    """Scheduler work; composite application is not source-discovery work."""

    postorder_frames: int | None = None
    primitive_applications: int | None = None
    chronological_compositions: int | None = None
    composite_applications: int | None = None
    demanded_composite_applications: int | None = None
    source_image_publications: int | None = None
    source_image_adapter_registrations: int | None = None
    arithmetic_result_publications: int | None = None
    bootstrap_admission_steps: int | None = None
    reverse_pair_steps: int | None = None
    reverse_pair_sections: int | None = None
    reverse_successor_rows: int | None = None
    reverse_successor_bootstrap_rows: int | None = None
    reverse_successor_spatial_bits: int | None = None
    reverse_successor_pair_symbols: int | None = None
    reverse_successor_event_symbols: int | None = None
    reverse_successor_transport_updates: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalStreamDemand:
    """Output emission measurements, kept distinct from jump construction."""

    requests: int | None = None
    node_visits: int | None = None
    emitted: int | None = None
    boundary_evaluations: int | None = None
    frame_peak: int | None = None
    cancellations: int | None = None
    failures: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalRenderingWork:
    """Complete CLI text rendering, separate from internal native digit streams."""

    requests: int | None = None
    emitted_digits: int | None = None
    failures: int | None = None
    integer_conversion_operand_bits: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalDemand:
    """Term query counts; absent exact counters are not inferred from output."""

    point_requests: int | None = None
    length_requests: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalObservations:
    """Family observation and forbidden replay work, in original units."""

    arithmetic_returns: int | None = None
    arithmetic_result_validation_blocks: int | None = None
    arithmetic_result_validation_reconstructions: int | None = None
    arithmetic_result_validation_operand_bits: int | None = None
    mahler_source_composed_image_reads: int | None = None
    mahler_associated_action_demands: int | None = None
    mahler_root_shell_projections: int | None = None
    mahler_root_shell_operand_bits: int | None = None
    physical_roof_evaluations: int | None = None
    query_observer_reuses: int | None = None
    higher_concrete_operation_evaluations: int | None = None
    higher_action_continuation_requests: int | None = None
    reverse_recursive_pair_width_cache_hits: int | None = None
    reverse_recursive_pair_width_cache_misses: int | None = None
    reverse_recursive_pair_width_publications: int | None = None
    reverse_recursive_pair_width_descents: int | None = None
    reverse_recursive_pair_width_failures: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalGrowthReadout:
    """Demanded homogeneous arithmetic, never endpoint-growth work."""

    work: int | None = None
    operand_bits: int | None = None
    precision_bits: int | None = None
    refinements: int | None = None
    exact_rational_cases: int | None = None
    bounded_exact_ratio_cases: int | None = None
    identity_shortcuts: int | None = None
    log_constant_hits: int | None = None
    cf_requests: int | None = None
    cf_budget_refusals: int | None = None
    order_hits: int | None = None
    budget_refusals: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalFamilyWork:
    """One arithmetic owner's finite source-discovery measurements."""

    counter_prefix: str
    action_requests: int | None
    action_hits: int | None
    action_misses: int | None
    action_publications: int
    macro_requests: int | None
    bounded_base_steps: int | None
    macro_compositions: int | None
    operand_bits: tuple[tuple[str, int], ...]
    transient_leaf_steps: int | None = None
    balanced_effect_compositions: int | None = None
    balanced_macro_compositions: int | None = None
    saturated_support_publications: int | None = None
    composite_cutover_chunks: int | None = None
    composite_cutover_publications: int | None = None
    balanced_effect_memo_lookups: int | None = None
    balanced_effect_memo_hits: int | None = None
    balanced_effect_memo_misses: int | None = None
    balanced_effect_memo_publications: int | None = None
    balanced_effect_memo_evictions: int | None = None
    finite_block_lookups: int | None = None
    finite_block_hits: int | None = None
    finite_block_misses: int | None = None
    finite_block_publications: int | None = None
    finite_block_evictions: int | None = None
    finite_block_cold_atoms: int | None = None
    finite_block_cold_steps: int | None = None
    run_actions: int | None = None
    zero_run_pumps: int | None = None
    one_run_pumps: int | None = None
    cycle_pumps: int | None = None
    represented_cycle_repetitions: int | None = None
    run_contraction_publications: int | None = None
    run_routes: int | None = None
    balanced_routes: int | None = None
    punctured_event_actions: int | None = None
    punctured_event_symbols: int | None = None
    guarded_template_lookups: int | None = None
    guarded_template_hits: int | None = None
    guarded_template_misses: int | None = None
    guarded_template_publications: int | None = None
    guarded_template_bypasses: int | None = None
    guarded_prefix_macro_requests: int | None = None
    guarded_prefix_root_candidates: int | None = None
    guarded_prefix_global_root_candidates: int | None = None
    guarded_prefix_slice_candidates: int | None = None
    guarded_prefix_action_operand_bits: int | None = None
    guarded_prefix_source_operand_bits: int | None = None
    guarded_prefix_publications: int | None = None
    guarded_prefix_budget_bypasses: int | None = None
    root_checkpoint_work: tuple[tuple[str, int], ...] = field(default=(), kw_only=True)
    border_return_work: tuple[tuple[str, int], ...] = field(default=(), kw_only=True)


@dataclass(frozen=True, slots=True)
class TemporalCommaWork:
    """Guarded comma construction; represented cycles are not executed work."""

    operations: int | None = None
    binary_compositions: int | None = None
    transfer_constructions: int | None = None
    transfer_phase_terms: int | None = None
    cycle_rule_evaluations: int | None = None
    child_candidate_checks: int | None = None
    seam_predicate_check_bound: int | None = None
    operand_bits: int | None = None
    represented_phase_cycles: int | None = None
    powered_image_applications: int | None = None
    represented_transitions: int | None = None
    evaluated_transitions: int | None = None
    seam_steps: int | None = None
    relative_guard_checks: int | None = None
    relative_cycle_rebindings: int | None = None
    boundary_template_hits: int | None = None
    boundary_template_misses: int | None = None
    boundary_template_publications: int | None = None
    boundary_template_retained_nodes: int | None = None
    boundary_seal_checks: int | None = None
    boundary_explicit_audit_component_checks: int | None = None
    boundary_explicit_audit_operand_bits: int | None = None
    boundary_seal_retained_slots: int | None = None
    boundary_seal_retained_integer_bits: int | None = None
    boundary_prefix_applications: int | None = None
    boundary_represented_transitions: int | None = None
    stream_requests: int | None = None
    stream_emitted_digits: int | None = None
    stream_workspace_peak_slots: int | None = None
    stream_workspace_peak_integer_bits: int | None = None
    certificate_operations: int | None = None
    certificate_sector_entries: int | None = None
    certificate_boundary_classifications: int | None = None
    certificate_candidate_digit_trials: int | None = None
    certificate_operand_bits: int | None = None
    certificate_read_bytes: int | None = None
    certificate_uncompressed_bytes: int | None = None
    certificate_frontier_peak: int | None = None
    certificate_local_hits: int | None = None
    certificate_cache_hits: int | None = None
    certificate_cache_misses: int | None = None
    certificate_cache_bypasses: int | None = None
    certificate_cache_publications: int | None = None
    budget_refusals: int | None = None
    certificate_budget_refusals: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalResources:
    """Whole-ledger retention; these counts are never attributed to one lane."""

    entries: int | None = None
    nodes: int | None = None
    peak_entries: int | None = None
    peak_nodes: int | None = None
    audit_complete: bool | None = None
    accounting_mismatch: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalReportingWork:
    """Measured reporting traversal, separate from computational work."""

    captured_counter_items: int | None = None
    captured_mapping_bytes: int | None = None
    projected_counter_items: int | None = None
    inspected_inventory_rows: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalMacrocellWork:
    """Semantic interning and occurrence application are separate reuse lanes.

    ``max_level`` is log2 of represented family transitions (D8 is level 3),
    never an archive-specific level relative to its bootstrap size. A semantic
    hit alone makes no claim that occurrence construction was avoided.
    """

    family: str
    index_unit: str
    cache_scope: str
    semantic: TemporalReuseLane
    occurrence: TemporalReuseLane
    source_action: TemporalReuseLane = field(default_factory=TemporalReuseLane)
    joint_action: TemporalReuseLane = field(default_factory=TemporalReuseLane)
    mixed_action: CompleteActionReuse = field(default_factory=CompleteActionReuse)
    outer_observer: TemporalReuseLane = field(default_factory=TemporalReuseLane)
    width_projection: TemporalReuseLane = field(default_factory=TemporalReuseLane)
    outer_observer_scope: str | None = None
    merges: int | None = None
    max_level: int | None = None
    primitive_steps: int | None = None
    spatial_leaf_visits: int | None = None
    operand_bits: int | None = None
    key_operand_bits: int | None = None
    cold_child_discoveries: int | None = None
    coefficient_compositions: int | None = None
    occurrence_frontier_joins: int | None = None
    gain_local_hits: int | None = None
    gain_process_hits: int | None = None
    gain_key_operand_bits: int | None = None
    gain_construction_operand_bits: int | None = None
    gain_validation_operand_bits: int | None = None
    gain_bypasses: int | None = None
    capacity_bypasses: int | None = None
    output_region_visits: int | None = None
    emitted_digits: int | None = None
    failed_work: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalAffineWidth:
    """Charged exact width comparisons, distinct from growth or emitted digits."""

    requests: int | None = None
    operand_bits: int | None = None
    interval_checks: int | None = None
    refinements: int | None = None
    exact_boundaries: int | None = None
    failures: int | None = None


@dataclass(frozen=True, slots=True)
class TemporalExecutionDiagnostics:
    """Compact schema-eight view beside the preserved raw work counters."""

    schema_version: int = METRICS_SCHEMA_VERSION
    action: TemporalReuseLane = field(default_factory=TemporalReuseLane)
    application: TemporalReuseLane = field(default_factory=TemporalReuseLane)
    projection: TemporalReuseLane = field(default_factory=TemporalReuseLane)
    construction: TemporalConstruction = TemporalConstruction()
    demand: TemporalDemand = TemporalDemand()
    stream: TemporalStreamDemand = TemporalStreamDemand()
    observations: TemporalObservations = TemporalObservations()
    growth_readout: TemporalGrowthReadout = TemporalGrowthReadout()
    affine_width: TemporalAffineWidth = TemporalAffineWidth()
    family_work: tuple[TemporalFamilyWork, ...] = ()
    macrocells: tuple[TemporalMacrocellWork, ...] = ()
    comma: TemporalCommaWork = TemporalCommaWork()
    cellular: tuple[CellularTemporalWork, ...] = ()
    resources: TemporalResources = TemporalResources()
    reporting: TemporalReportingWork = TemporalReportingWork()
    rendering: TemporalRenderingWork = TemporalRenderingWork()

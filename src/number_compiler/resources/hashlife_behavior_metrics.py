"""Behavior-specific metrics collected from a powered HashLife execution."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.resources.metric_records import LedgerMetrics


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


__all__ = ["HashLifeBehaviorMetrics"]

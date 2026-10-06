"""Legacy report schema projected from the actual dyadic source-image owner."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.resources.metric_collection import (
    collect_ledger_metrics,
    ledger_fields_from,
)
from number_compiler.resources.metric_records import HashLifeBehaviorMetrics
from number_compiler.resources.metric_replace import replace_metric

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm


def collatz_behavior_metrics(term: PoweredCollatzTerm) -> HashLifeBehaviorMetrics:
    workspace = term._workspace
    # Reporting does not discover the source or evaluate the endpoint.
    actions = 0 if workspace is None else len(workspace.actions)
    sources = 0 if workspace is None else len(workspace.sources)
    images = 0 if workspace is None else len(workspace.images)
    support = 0 if workspace is None else len(workspace.support)
    report = collect_ledger_metrics(term._ledger, audit_payloads=False)
    result = HashLifeBehaviorMetrics(
        effect_exponent=term.steps,
        logical_width_bound=term.maximum_width,
        seed_payload_tile_nodes=0,
        padded_root_tile_nodes=0,
        retained_spatial_tile_nodes=0,
        application_spatial_tile_nodes=0,
        powered_operator_nodes=term.operator_nodes,
        temporal_quotient_family="collatz-dyadic-source-image",
        temporal_quotient_horizon=term.steps,
        temporal_cell_payload_bits=0,
        temporal_residue_prime=2,
        temporal_residue_precision=term.steps,
        temporal_residue_classes=0,
        temporal_symbolic_exponent_fields=1,
        temporal_quotient_state_class_bound=0,
        temporal_quotient_action_class_bound=0,
        temporal_local_action_class_bound=2,
        temporal_quotient_descriptor_bits_bound=0,
        temporal_cocycle_weight_fields=2,
        compiler_temporal_state_nodes=0,
        compiler_temporal_action_nodes=report.compiler_program_nodes,
        compiler_recursive_state_action_shared_nodes=0,
        temporal_description_nodes=report.compiler_program_nodes + actions,
        seed_application_temporal_state_nodes=sources,
        seed_application_temporal_action_nodes=actions,
        seed_application_temporal_description_nodes=sources
        + actions
        + images
        + support,
        spatial_occurrence_state_nodes=0,
        spatial_occurrence_action_nodes=0,
        spatial_occurrence_recursive_state_action_shared_nodes=0,
        spatial_occurrence_description_nodes=0,
        unquotiented_recursive_application_state_nodes=0,
        unquotiented_recursive_application_action_nodes=0,
        unquotiented_recursive_application_description_nodes=0,
        execution_memo_entries=report.resource_ledger_entries,
        retained_effect_memo_entries=0,
        recursive_spatial_residual_max_extent=0,
        recursive_spatial_residual_max_depth=0,
        recursive_boundary_wrapper_nodes=0,
        spatial_occurrence_accounting_delta=report.resource_accounting_mismatch,
        raw_temporal_scalar_length_fields=0,
        raw_temporal_span_fields=report.forbidden_future_payloads,
        raw_spatial_occurrence_scalar_extent_fields=0,
        eager_spatial_observer_fields=report.forbidden_future_payloads,
    )
    return replace_metric(result, ledger_fields_from(report))

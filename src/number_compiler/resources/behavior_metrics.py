"""Behavior reports derived from actual index-owned lazy resource inventories."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.resources.metric_collection import ledger_fields_from
from number_compiler.resources.metric_records import HashLifeBehaviorMetrics
from number_compiler.resources.metric_replace import replace_metric

if TYPE_CHECKING:
    from number_compiler.hashlife.observation.hashlife_projection import (
        HashLifeBlockIndex,
    )


def collect_behavior_metrics(index: HashLifeBlockIndex) -> HashLifeBehaviorMetrics:
    report = index.metrics()
    baseline = dict(index._effect_metric_baseline)
    seed_nodes = index._collect_tile_nodes(
        {chunk.tile for chunk in index.seed_root.chunks}
    )
    root_nodes = index._collect_tile_nodes(
        {chunk.tile for chunk in index.evaluation_root.chunks}
    )
    retained_nodes = index._retained_tile_nodes()
    seen: set[int] = set()
    stack: list[object] = [index.effect]
    while stack:
        node = stack.pop()
        if id(node) in seen:
            continue
        seen.add(id(node))
        for name in ("first", "second"):
            child = getattr(node, name, None)
            if child is not None:
                stack.append(child)
    from number_compiler.hashlife.observation.tile_projection import (
        LazyProjection as TileProjection,
    )

    family = "generic-tile-hashlife"
    horizon = bits = local_bound = symbolic_exponents = cocycle_fields = 0
    state_bound = action_bound = 0
    carry_function_bound = interval_bound = interval_classes = 0
    certificate = index._certificate
    tile_runtime = type(index._lazy_application) is TileProjection
    if certificate is not None and tile_runtime:
        family = f"{certificate.family}-tile-hashlife"
        state_bound = report.local_interface_nodes
        action_bound = report.field_action_nodes
        if certificate.family == "reverse-add":
            from number_compiler.arithmetic.carry.event_memory import (
                event_memory_horizon,
            )

            horizon = (
                event_memory_horizon(certificate.base) if certificate.base >= 3 else 0
            )
            bits, local_bound = 3, 7
            carry_function_bound, interval_bound = 3, 7
            interval_classes = report.local_interface_nodes
            symbolic_exponents = 2
        else:
            bits, local_bound = 2, 3
            symbolic_exponents, cocycle_fields = 2, 1
    result = HashLifeBehaviorMetrics(
        effect_exponent=int(index.effect.exponent),
        logical_width_bound=index.logical_length,
        seed_payload_tile_nodes=len(seed_nodes),
        padded_root_tile_nodes=len(root_nodes),
        retained_spatial_tile_nodes=len(retained_nodes),
        application_spatial_tile_nodes=len(retained_nodes - root_nodes),
        powered_operator_nodes=len(seen),
        temporal_quotient_family=family,
        temporal_quotient_horizon=horizon,
        temporal_cell_payload_bits=bits,
        carry_port_function_class_bound=carry_function_bound,
        spatial_interval_action_classes=interval_classes,
        spatial_interval_action_class_bound=interval_bound,
        temporal_residue_prime=0,
        temporal_residue_precision=0,
        temporal_residue_classes=0,
        temporal_symbolic_exponent_fields=symbolic_exponents,
        temporal_quotient_state_class_bound=state_bound,
        temporal_quotient_action_class_bound=action_bound,
        temporal_local_action_class_bound=local_bound,
        temporal_quotient_descriptor_bits_bound=0,
        temporal_cocycle_weight_fields=cocycle_fields,
        compiler_temporal_state_nodes=0,
        compiler_temporal_action_nodes=report.compiler_program_nodes,
        compiler_recursive_state_action_shared_nodes=0,
        temporal_description_nodes=report.temporal_program_nodes,
        seed_application_temporal_state_nodes=0,
        seed_application_temporal_action_nodes=report.application_program_nodes,
        seed_application_temporal_description_nodes=(report.application_program_nodes),
        spatial_occurrence_state_nodes=report.spatial_binding_nodes
        + report.boundary_state_nodes,
        spatial_occurrence_action_nodes=(
            report.canonical_transfer_nodes
            + report.image_action_nodes
            + report.spatial_action_program_nodes
        ),
        spatial_occurrence_recursive_state_action_shared_nodes=0,
        spatial_occurrence_description_nodes=(
            report.spatial_binding_nodes
            + report.boundary_state_nodes
            + report.canonical_transfer_nodes
            + report.image_action_nodes
            + report.spatial_action_program_nodes
            + report.diamond_cell_nodes
        ),
        unquotiented_recursive_application_state_nodes=0,
        unquotiented_recursive_application_action_nodes=0,
        unquotiented_recursive_application_description_nodes=0,
        execution_memo_entries=report.resource_ledger_entries,
        retained_effect_memo_entries=baseline.get("retained_cache_entries", 0),
        recursive_spatial_residual_max_extent=0,
        recursive_spatial_residual_max_depth=0,
        recursive_boundary_wrapper_nodes=0,
        spatial_occurrence_accounting_delta=report.resource_accounting_mismatch,
        raw_temporal_scalar_length_fields=0,  # Coordinates are permitted geometry.
        raw_temporal_span_fields=report.forbidden_future_payloads,
        raw_spatial_occurrence_scalar_extent_fields=0,
        eager_spatial_observer_fields=report.forbidden_future_payloads,
    )
    values = ledger_fields_from(report)
    for name in (
        "exact_spatial_occurrences",
        "symbolic_action_nodes",
        "jump_entries",
        "primitive_step_evaluations",
        "action_compositions",
        "action_applications",
        "nonlinear_branch_evaluations",
        "exact_endpoint_entries",
        "query_requests",
        "quotient_builds",
        "residual_physical_steps",
    ):
        key = "bounded_application_" + name
        values[key] = getattr(report, key)
    return replace_metric(result, values)

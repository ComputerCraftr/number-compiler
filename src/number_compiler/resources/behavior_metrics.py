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


def _registered_root(index: HashLifeBlockIndex, value: object) -> bool:
    """Check the ledger's issued-root registry without pruning or mutation."""
    reference = index._ledger._execution_roots.get(id(value))
    return reference is not None and reference() is value


def _live_tile_lease(lease: object, tiles: object) -> bool:
    """Inspect one issued tile lease without resolving semantic tile content."""
    from number_compiler.hashlife.tiles.tiles import TileArena, TileID, TileLease

    if (
        type(tiles) is not TileArena
        or type(lease) is not TileLease
        or lease._arena is not tiles
        or lease._closed is not False
        or type(lease._id) is not int
    ):
        return False
    tile = tiles._leases.get(lease._id)
    return (
        type(tile) is TileID
        and tile.owner is tiles.owner
        and tile.kind == "canonical-tile"
        and type(tile.local_id) is int
        and tile.local_id in tiles._nodes
    )


def _tile_runtime_blocker(index: HashLifeBlockIndex) -> str:
    """Attest the issued tile stack using identity and liveness only.

    Reporting deliberately does not call ``_open()``, ``_validate_key()``, an
    interface reducer, or any semantic observation.  Those operations either
    perform work or repeat admission that was sealed when the application was
    issued.
    """
    from number_compiler.hashlife.actions.field_actions import FieldCellActionID
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )
    from number_compiler.hashlife.execution.tile_scheduler import (
        TileApplication,
        TileScheduler,
    )
    from number_compiler.hashlife.observation.tile_projection import LazyProjection
    from number_compiler.hashlife.tiles.tile_results import (
        CompletedResultArena,
        ResultLease,
    )
    from number_compiler.hashlife.tiles.tiles import TileArena

    projection = index._lazy_application
    if type(projection) is not LazyProjection:
        return "unattested_execution_carrier"
    scheduler, application = projection.scheduler, projection._application
    if (
        projection.ledger is not index._ledger
        or projection._closed is not False
        or not _registered_root(index, projection)
        or type(scheduler) is not TileScheduler
        or scheduler.ledger is not index._ledger
        or not _registered_root(index, scheduler)
        or type(application) is not TileApplication
        or application.scheduler is not scheduler
        or application._closed is not False
        or not _registered_root(index, application)
    ):
        return "invalid_tile_application_authority"
    tiles, results, adapter = scheduler.tiles, scheduler.results, scheduler.adapter
    if (
        type(tiles) is not TileArena
        or tiles.ledger is not index._ledger
        or not _registered_root(index, tiles)
        or type(results) is not CompletedResultArena
        or results.ledger is not index._ledger
        or results.tiles is not tiles
        or results.action_authority is not adapter
        or not _registered_root(index, results)
        or type(adapter) is not PrimitiveTileKernelAdapter
        or adapter.ledger is not index._ledger
        or not _registered_root(index, adapter)
    ):
        return "invalid_tile_runtime_ownership"
    action = application.action
    if (
        type(action) is not FieldCellActionID
        or action.owner is not adapter.owner
        or action.kind != "field-cell-action"
        or type(action.local_id) is not int
        or action.local_id not in adapter._actions
        or type(application.identity) is not int
        or not 0 <= application.identity < scheduler._next_application
        or not _live_tile_lease(application._input, tiles)
    ):
        return "invalid_tile_runtime_identity"
    root = application._root
    if root is not None and (
        type(root) is not ResultLease
        or root._issuer is not results
        or root._closed is not False
        or root._key.action != action
        or root._key.input != tiles._leases.get(application._input._id)
        or root._key.ports != application.ports
        or root._key.wiring != application.wiring
        or not _live_tile_lease(root._tile, tiles)
    ):
        return "invalid_tile_root_lease"
    return ""


def _cutover_blocker(index: HashLifeBlockIndex, sequential_advances: int) -> str:
    """Classify the actual executor, independently of representation validity.

    A composition certificate alone is insufficient.  The issued tile stack
    must be live and index-owned, and any observed retired-executor work keeps
    the cutover failed. Unknown carriers fail closed instead of self-attesting.
    """
    if sequential_advances:
        return "sequential_generation_advances"
    counters = index._ledger.counters
    if counters.get("whole_word_sweeps", 0):
        return "whole_word_sweeps"
    if counters.get("whole_word_symbol_visits", 0):
        return "whole_word_symbol_visits"
    if counters.get("proof_machine_applications", 0):
        return "proof_machine_applications"
    if any(
        counters.get(name, 0)
        for name in (
            "higher_action_continuation_requests",
            "higher_concrete_operation_evaluations",
            "higher_operation_publications",
        )
    ):
        return "higher_continuation_execution"
    return _tile_runtime_blocker(index)


def collect_behavior_metrics(index: HashLifeBlockIndex) -> HashLifeBehaviorMetrics:
    report = index.metrics()
    cutover_blocker = _cutover_blocker(index, report.sequential_generation_advances)
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
        bounded_temporal_runtime_cutover_complete=int(not cutover_blocker),
        bounded_temporal_runtime_cutover_blocker=cutover_blocker,
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

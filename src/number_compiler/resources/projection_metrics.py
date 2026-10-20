"""Projection metric compatibility derived from one ledger snapshot."""

from __future__ import annotations

from dataclasses import fields
from typing import TYPE_CHECKING

from number_compiler.resources.metric_collection import (
    collect_ledger_metrics,
    ledger_fields_from,
)
from number_compiler.resources.metric_keys import (
    arithmetic_contracts as _contracts_keys,
)
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)
from number_compiler.resources.metric_records import HashLifeProjectionMetrics
from number_compiler.resources.metric_registry import normalized_role as _role
from number_compiler.resources.metric_replace import replace_metric

if TYPE_CHECKING:
    from number_compiler.hashlife.observation.hashlife_projection import (
        HashLifeBlockIndex,
    )


def _has_registered_tile_application(index: HashLifeBlockIndex) -> bool:
    """Validate the live application against its ledger-issued bound record.

    This is an identity and lease check only. Metric collection must not replay
    semantic admission or perform an observation to produce a certificate.
    """
    from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
    from number_compiler.hashlife.actions.field_actions import FieldCellActionID
    from number_compiler.hashlife.execution.tile_application import TileApplication
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
    from number_compiler.hashlife.observation.tile_projection import LazyProjection
    from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
    from number_compiler.hashlife.tiles.tiles import TileArena, TileID, TileLease

    def issued(value: object) -> bool:
        return index.resource_ledger.owns_execution_root(value)

    projection = index.audit_snapshot().lazy_application
    if (
        type(projection) is not LazyProjection
        or projection.ledger is not index.resource_ledger
        or projection.audit_snapshot().closed is not False
        or not issued(projection)
    ):
        return False
    projection_snapshot = projection.audit_snapshot()
    scheduler, application = (
        projection_snapshot.scheduler,
        projection_snapshot.application,
    )
    if (
        type(scheduler) is not TileScheduler
        or scheduler.ledger is not index.resource_ledger
        or not issued(scheduler)
        or type(application) is not TileApplication
        or application.audit_snapshot().scheduler is not scheduler
        or application.audit_snapshot().closed is not False
        or not issued(application)
    ):
        return False
    tiles, results, adapter = scheduler.tiles, scheduler.results, scheduler.adapter
    result_snapshot = results.audit_snapshot()
    scheduler_snapshot = scheduler.audit_snapshot()
    if (
        type(tiles) is not TileArena
        or tiles.ledger is not index.resource_ledger
        or not issued(tiles)
        or type(results) is not CompletedResultArena
        or results.ledger is not index.resource_ledger
        or results.tiles is not tiles
        or results.action_authority is not adapter
        or result_snapshot.ledger is not index.resource_ledger
        or not issued(results)
        or type(adapter) is not PrimitiveTileKernelAdapter
        or adapter.ledger is not index.resource_ledger
        or not issued(adapter)
        or type(adapter.owner) is not ArenaToken
        or scheduler_snapshot.ledger is not index.resource_ledger
    ):
        return False
    adapter_snapshot = adapter.audit_snapshot()
    application_snapshot = application.audit_snapshot()
    action, identity, lease = (
        application_snapshot.action,
        application_snapshot.identity,
        application_snapshot.input_lease,
    )
    if (
        type(action) is not FieldCellActionID
        or action.owner is not adapter.owner
        or action.kind != "field-cell-action"
        or type(action.local_id) is not int
        or action.local_id not in adapter_snapshot.actions
        or type(identity) is not int
        or scheduler_snapshot.next_application is None
        or not 0 <= identity < scheduler_snapshot.next_application
        or type(lease) is not TileLease
        or lease.audit_snapshot().arena is not tiles
        or lease.audit_snapshot().closed is not False
    ):
        return False
    try:
        source = lease.tile
        if type(source) is not TileID or not scheduler.application_is_registered(
            application
        ):
            return False
    except (AttributeError, KeyError, TypeError, ValueError):
        return False
    return True


def collect_projection_metrics(index: HashLifeBlockIndex) -> HashLifeProjectionMetrics:
    """Compiler snapshots and index-owned work have separate accounting scopes."""
    from number_compiler.arithmetic.fields.dyadic_tile import (
        tile_arena_metrics,
        tile_metrics,
    )
    from number_compiler.hashlife.observation.tile_projection import (
        LazyProjection as TileProjection,
    )

    ledger = collect_ledger_metrics(index.resource_ledger, audit_payloads=False)
    index_snapshot = index.audit_snapshot()
    baseline = dict(index_snapshot.effect_metric_baseline)
    geometry = tile_metrics(index.evaluation_root)
    tile_nodes = index_snapshot.retained_spatial_tile_nodes
    values = ledger_fields_from(ledger)
    compiler_entries = sum(
        item.entries
        for item in ledger.resource_inventory
        if _role(item.role) in ("compiled_action_program", "compiled_action_interner")
    )
    source_entries = sum(
        item.entries
        for item in ledger.resource_inventory
        if _role(item.role) == "exact_source"
    )
    # Compiler counts are frozen at index construction. They never inherit work
    # performed later by another index sharing an operator or a global arena.
    for item in fields(HashLifeProjectionMetrics):
        if item.name in values:
            continue
        if item.name.startswith("compiler_"):
            values[item.name] = baseline.get(item.name.removeprefix("compiler_"), 0)
        elif item.name.startswith(
            ("canonical_function_", "canonical_partition_", "canonical_recursive_")
        ):
            values[item.name] = baseline.get(item.name, 0)
    values.update(
        point_queries=index_snapshot.point_queries,
        direct_powered_point_queries=index_snapshot.direct_powered_point_queries,
        canonical_tile_roots=index_snapshot.canonical_tile_roots,
        retained_execution_nodes=ledger.resource_ledger_nodes
        - ledger.source_payload_nodes,
        compiler_retained_execution_nodes=ledger.compiler_program_nodes,
        query_retained_execution_nodes=(
            ledger.resource_ledger_nodes
            - ledger.source_payload_nodes
            - ledger.compiler_program_nodes
        ),
        canonical_program_word_roots=baseline.get("canonical_program_word_roots", 0),
        dyadic_forest_chunks=geometry["forest_chunks"],
        dyadic_max_level=geometry["max_level"],
        peak_live_tile_roots=tile_nodes,
        tile_observations=ledger.resource_work_counters.get(
            _contracts_keys.SOURCE_LEAF_READS, 0
        ),
        canonical_tile_arena_nodes=tile_nodes,
        canonical_tile_arena_nodes_index_build=tile_nodes,
        canonical_tile_arena_nodes_query=0,
        # Compatibility population of shared immutable source-geometry tiles.
        # Index-owned execution content is reported by canonical_tile_nodes.
        canonical_tile_arena_nodes_global=tile_arena_metrics()["canonical_nodes"],
        retained_cache_entries=ledger.resource_ledger_entries,
        compiler_retained_cache_entries=compiler_entries,
        query_retained_cache_entries=ledger.resource_ledger_entries
        - compiler_entries
        - source_entries,
        budgeted_cache_entries=ledger.resource_ledger_entries,
        retained_cache_accounting_delta=ledger.resource_accounting_mismatch,
        total_hashlife_retained_entries=ledger.cache_slots,
        source_index_cache_entries=source_entries,
    )
    application_view: object = index_snapshot.lazy_application
    if type(application_view) is TileProjection:
        from number_compiler.resources.application_metrics import (
            tile_application_compatibility_values,
        )

        values.update(
            tile_application_compatibility_values(index, ledger, compiler_entries)
        )
        action_hits = ledger.tile_temporal_action_hits
        action_aliases = ledger.tile_temporal_action_semantic_alias_hits
        action_evaluations = ledger.tile_temporal_action_publications + action_aliases
        values.update(
            temporal_parent_requests=action_hits + action_evaluations,
            temporal_parent_early_hits=action_hits,
            temporal_parent_compositions=action_evaluations,
            temporal_parent_late_duplicate_reductions=action_aliases,
            bounded_application_action_compositions=action_evaluations,
            scheduler_transitions=ledger.resource_work_counters.get(
                _execution_keys.TILE_CAUSAL_FRAMES, 0
            )
            + ledger.tile_temporal_complete_frames,
            scheduler_workspace_peak=max(
                ledger.resource_work_counters.get(
                    _execution_keys.TILE_CAUSAL_WORKSPACE_PEAK, 0
                ),
                ledger.tile_scheduler_workspace_peak,
                ledger.tile_fused_workspace_peak,
            ),
        )
        # The certificate is the live ledger-bound application record, not a
        # family annotation. The check validates that exact issued binding and
        # its leases without replaying its semantics.
        values["bimachine_composition_certified"] = int(
            _has_registered_tile_application(index)
        )
    return replace_metric(HashLifeProjectionMetrics(*([0] * 15)), values)

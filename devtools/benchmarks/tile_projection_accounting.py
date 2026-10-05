"""Current scheduler work, separated from retired interpreter compatibility names."""

from time import perf_counter
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from number_compiler.hashlife.tiles.tile_results import CompletedResultArena

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.metric_records import LedgerMetrics

_COUNTERS = (
    "sequential_generation_advances",
    "primitive_transition_evaluations",
    "tile_scheduler_leaf_function_applications",
    "tile_scheduler_frames",
    "tile_scheduler_workspace_peak",
    "completed_result_requests",
    "completed_result_early_hits",
    "completed_result_entries",
    "tile_temporal_action_publications",
    "spatial_interface_composition_publications",
    "fused_interface_publications",
    "endpoint_lowering_requests",
    "explicitly_lowered_digits",
    "completed_result_port_variants_peak",
    "completed_result_evictions",
    "completed_result_evicted_entries",
    "tile_retirements",
    "canonical_tile_nodes",
    "local_interface_nodes",
    "field_action_nodes",
)


def explicit_resource_audit(
    ledger: ResourceLedger,
) -> tuple[LedgerMetrics, float, dict[str, int]]:
    """Run and time a charged payload/ownership audit outside query metrics.

    Public metric snapshots are intentionally read-only and do not force a
    deep resource walk. Benchmarks that require audited accounting must call
    this explicitly after the measured query, and report the audit's own work
    separately from construction and observation.
    """
    before = dict(ledger.counters)
    started = perf_counter()
    metrics = collect_ledger_metrics(ledger)
    elapsed = perf_counter() - started
    after = dict(ledger.counters)
    work = {
        name: value - before.get(name, 0)
        for name, value in sorted(after.items())
        if value != before.get(name, 0)
    }
    return metrics, elapsed, work


def projection_accounting(metrics: LedgerMetrics) -> dict[str, int]:
    """Validate the installed route without declaring finite leaf work forbidden."""
    if (
        metrics.sequential_generation_advances
        or metrics.higher_concrete_operation_evaluations
        or metrics.higher_action_continuation_requests
        or metrics.temporal_leaf_diamond_descents
    ):
        raise AssertionError("retired-temporal-interpreter-work-observed")
    counters = {name: int(getattr(metrics, name)) for name in _COUNTERS}
    for name in (
        "reverse_morphism_directional_leaf_consumers",
        "reverse_morphism_directional_compositions",
        "reverse_morphism_leaf_bindings",
        "collatz_physical_factored_output_compilations",
        "collatz_physical_joint_output_tables_elided",
        "collatz_physical_event_source_reads_elided",
        "reverse_threshold_summary_requests",
        "reverse_threshold_summary_known_missing_probe_elisions",
        "primitive_behavior_refinement_observation_checks",
        "primitive_behavior_refinement_successor_checks",
        "primitive_behavioral_quotient_evaluations",
        "primitive_output_evaluations",
    ):
        counters[name] = metrics.resource_work_counters.get(name, 0)
    return counters


def retained_result_profile(
    results: "CompletedResultArena", *, max_entries: int = 20_000
) -> dict[str, object]:
    """Attribute retained occurrence keys without evaluating future content.

    Groups are diagnostic projections of keys, not certified function IDs.
    Equal bound outputs alone do not justify dropping a consumer context.
    """
    from collections import Counter

    from number_compiler.hashlife.tiles.tile_result_records import (
        CompletedResult,
        PoweredResultKey,
    )

    entries: list[tuple[PoweredResultKey, CompletedResult]] = []
    for key, value in results._memo.items():
        if type(key) is PoweredResultKey and type(value) is CompletedResult:
            if len(entries) >= max_entries:
                raise ValueError("completed-result profile exceeds entry budget")
            entries.append((key, value))
    return {
        "retained_result_profile": {
            "entries": len(entries),
            "input_tiles": len({key.input for key, _ in entries}),
            "action_input_pairs": len({(key.action, key.input) for key, _ in entries}),
            "finite_contracts_excluding_spatial_bindings": len(
                {(key.action, key.ports, key.wiring, key.fusion) for key, _ in entries}
            ),
            "contexts_excluding_ports": len(
                {
                    (
                        key.action,
                        key.input,
                        key.wiring,
                        key.boundaries,
                        key.fusion,
                        key.region,
                    )
                    for key, _ in entries
                }
            ),
            "exact_output_tiles": len({value.output for _, value in entries}),
            "complete_output_records": len({value for _, value in entries}),
            "entries_by_input_level": dict(
                sorted(
                    Counter(
                        results.tiles.resolve(key.input).level for key, _ in entries
                    ).items()
                )
            ),
            "entries_with_boundaries": sum(
                key.boundaries.left is not None or key.boundaries.right is not None
                for key, _ in entries
            ),
            "entries_with_fusion": sum(key.fusion is not None for key, _ in entries),
        }
    }

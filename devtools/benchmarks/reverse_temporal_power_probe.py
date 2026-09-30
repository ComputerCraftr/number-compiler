"""Schema-seven probe separating compiled images from actual projection work.

Compact binary action syntax and a small image graph do not certify output
absorption. Report concrete continuation work, semantic interpreter frames,
and temporal leaf descents alongside canonical spatial/temporal populations.
"""

from __future__ import annotations

import itertools
import json
from collections.abc import Mapping, Sequence
from time import perf_counter

from devtools.benchmarks.temporal_probe_support import (
    common_temporal_blockers,
    shared_cutover_sources,
)
from devtools.checks.dependency_graph import source_syntax
from devtools.paths import report_output, repository_root

ROOT = repository_root()


CONSTRUCTION_INDICES = (16, 256, 1_000_000, 10**18)
PROJECTION_INDICES = (16, 32, 64, 128, 256)


def _metric_int(value: object) -> int:
    if type(value) is not int:
        raise AssertionError(("probe-metric-is-not-an-exact-integer", value))
    return value


def _construction_rows() -> list[dict[str, int | float]]:
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

    rows: list[dict[str, int | float]] = []
    for generation in CONSTRUCTION_INDICES:
        started = perf_counter()
        term = ReverseAddPoweredTerm(196, generation, base=10)
        elapsed = perf_counter() - started
        metrics = term.metrics()
        row = {
            "generation": generation,
            "index_bits": generation.bit_length(),
            "operator_nodes": metrics.operator_nodes,
            "compose_operations": metrics.compose_operations,
            "syntax_depth_bound": metrics.syntax_depth_bound,
            "descriptor_bits": metrics.descriptor_bits,
            "construction_seconds": elapsed,
            "point_queries": metrics.point_queries,
        }
        bits = max(1, generation.bit_length())
        if metrics.operator_nodes > 4 * bits or metrics.compose_operations > 4 * bits:
            raise AssertionError(("operator-construction-regression", row))
        if metrics.point_queries:
            raise AssertionError(("construction-performed-projection", row))
        rows.append(row)
    return rows


def _scalar_digit(generation: int, position: int) -> int:
    value = 196
    for _ in range(generation):
        text = str(value)
        value += int(text[::-1])
    return int((value // (10**position)) % 10)


def _production_projection_rows() -> list[dict[str, object]]:
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

    rows: list[dict[str, object]] = []
    for generation in PROJECTION_INDICES:
        term = ReverseAddPoweredTerm(196, generation, base=10)
        position = max(0, term.maximum_width // 3)
        started = perf_counter()
        digit = term.digit(position)
        elapsed = perf_counter() - started
        if digit != _scalar_digit(generation, position):
            raise AssertionError((generation, position, digit))
        metrics = term.metrics()
        before_replay = dict(term._ledger.counters)
        if term.digit(position) != digit:
            raise AssertionError(
                ("runtime-image-replay-mismatch", generation, position)
            )
        after_replay = term._ledger.counters
        behavior = term.behavior_metrics()
        counters = metrics.resource_work_counters
        source_publications = counters.get("source_image_publications", 0)
        projection_publications = counters.get(
            "source_image_projection_publications", 0
        )
        if source_publications <= 0 or projection_publications <= 0:
            raise AssertionError(
                ("source-image-publication-missing", generation, counters)
            )
        if behavior.unquotiented_recursive_application_description_nodes:
            raise AssertionError(("generic-residual-reappeared", generation, behavior))
        if (
            not metrics.resource_audit_complete
            or metrics.resource_accounting_mismatch
            or metrics.forbidden_future_payloads
            or metrics.retained_unbounded_future_integers
        ):
            raise AssertionError(("lazy-resource-audit-failed", generation, metrics))
        rows.append(
            {
                "generation": generation,
                "metrics_schema_version": metrics.metrics_schema_version,
                "resource_ledger_entries": metrics.resource_ledger_entries,
                "cache_slots": metrics.cache_slots,
                "exact_source_occurrences": metrics.exact_source_occurrences,
                "spatial_occurrence_bindings": metrics.spatial_occurrence_bindings,
                "spatial_binding_nodes": metrics.spatial_binding_nodes,
                "canonical_transfer_nodes": metrics.canonical_transfer_nodes,
                "temporal_program_nodes": metrics.temporal_program_nodes,
                "finite_port_state_nodes": metrics.finite_port_state_nodes,
                "other_retained_nodes": metrics.other_retained_nodes,
                "resource_ledger_nodes": metrics.resource_ledger_nodes,
                "resource_observed_entries": metrics.resource_observed_entries,
                "resource_observed_nodes": metrics.resource_observed_nodes,
                "resource_accounting_mismatch": metrics.resource_accounting_mismatch,
                "resource_audit_complete": metrics.resource_audit_complete,
                "forbidden_future_payloads": metrics.forbidden_future_payloads,
                "retained_unbounded_future_integers": metrics.retained_unbounded_future_integers,
                "compiler_program_nodes": metrics.compiler_program_nodes,
                "application_program_nodes": metrics.application_program_nodes,
                "bounded_limb_operations": metrics.bounded_limb_operations,
                "maximum_arithmetic_bits": metrics.maximum_arithmetic_bits,
                "explicitly_materialized_endpoints": metrics.explicitly_materialized_endpoints,
                "index_bits": generation.bit_length(),
                "position": position,
                "higher_concrete_operation_evaluations": metrics.higher_concrete_operation_evaluations,
                "higher_semantic_evaluations": metrics.higher_semantic_evaluations,
                "higher_semantic_task_frames": metrics.higher_semantic_task_frames,
                "higher_action_continuation_requests": metrics.higher_action_continuation_requests,
                "temporal_leaf_diamond_descents": metrics.temporal_leaf_diamond_descents,
                "digit": digit,
                "runtime_image_matches_scalar": True,
                "source_image_replay_stable": (
                    after_replay.get("source_image_publications", 0)
                    == before_replay.get("source_image_publications", 0)
                    and after_replay.get("source_image_projection_publications", 0)
                    == before_replay.get("source_image_projection_publications", 0)
                ),
                "source_image_publications": source_publications,
                "source_image_projection_publications": projection_publications,
                "source_action_nodes": term.operator_nodes,
                "source_action_compositions": term.compose_operations,
                "resource_accounting_exact": (
                    metrics.resource_audit_complete == 1
                    and metrics.resource_accounting_mismatch == 0
                ),
                "projection_seconds": elapsed,
                "recursive_value_cache_entries": metrics.recursive_value_cache_entries,
                "unquotiented_recursive_application_nodes": behavior.unquotiented_recursive_application_description_nodes,
                "whole_word_sweeps": metrics.whole_word_sweeps,
                "whole_word_symbol_visits": metrics.whole_word_symbol_visits,
                "proof_machine_applications": metrics.proof_machine_applications,
                "total_internal_action_work": metrics.total_internal_action_work,
            }
        )
    return rows


def _source_audit() -> dict[str, bool]:
    hashlife = source_syntax(
        ROOT / "src" / "number_compiler" / "hashlife/observation/hashlife_projection.py"
    )
    reverse = source_syntax(
        ROOT / "src" / "number_compiler" / "sequences/reverse_add/power.py"
    )
    (
        compatibility_names,
        compatibility_imports,
        runtime,
        spacetime,
        boundary,
        _unused_router_syntax_binding,
        _unused_router_imports_binding,
        generic_executor_imported,
    ) = shared_cutover_sources(ROOT)
    checks = {
        "causal_engine_absent_from_reverse_power": "ReverseAddCausalSpacetimeEngine"
        not in reverse.identifiers,
        "t2_partition_interpreter_deleted": "_partition3" not in hashlife.functions
        and "_leaf_partition3" not in hashlife.functions,
        "whole_output_projection_deleted": "output_word" not in hashlife.functions,
        "ordinary_point_fallback_deleted": "point" not in hashlife.functions,
        "prefix_pop_residual_deleted": "program_pop_last" not in runtime.identifiers,
        "history_word_carrier_deleted": "..program_word" not in compatibility_imports
        and "CanonicalWord" not in compatibility_names,
        "exact_future_tile_output_deleted": "_output_tile_macro"
        not in spacetime.functions,
        "bounded_temporal_application_installed": (
            ROOT
            / "src"
            / "number_compiler"
            / "hashlife/execution/bounded_application.py"
        ).exists(),
        "certified_family_has_no_generic_executor_import": not generic_executor_imported,
        "raw_spacetime_boundary_runtime_deleted": (
            "SpacetimeBoundary" not in compatibility_names
            and "intern_boundary" not in compatibility_names
            and "_intern_spacetime_state" not in compatibility_names
            and "_advance_effect_boundary" not in compatibility_names
        ),
        "raw_boundary_carrier_class_deleted": "SpacetimeBoundary"
        not in boundary.classes,
    }
    if not all(checks.values()):
        raise AssertionError(checks)
    return checks


def _doubling_envelope(rows: Sequence[Mapping[str, object]], field: str) -> bool:
    """Measure growth in one unit, allowing a fixed first-sample bootstrap.

    Thousands of canonical cells are permissible.  A small compiler graph
    cannot excuse quadratic work or memo retention in another population.
    """
    if len(rows) < 2:
        return False
    bootstrap = _metric_int(rows[0][field])
    return all(
        _metric_int(current["generation"]) == 2 * _metric_int(previous["generation"])
        and _metric_int(current[field]) <= 2 * _metric_int(previous[field]) + bootstrap
        for previous, current in itertools.pairwise(rows)
    )


def run_probe() -> dict[str, object]:
    from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError

    construction = _construction_rows()
    rejection: UnsupportedInterfaceError | None = None
    projection: list[dict[str, object]]
    try:
        projection = _production_projection_rows()
    except UnsupportedInterfaceError as error:
        projection = []
        rejection = error
    envelopes = {
        field: _doubling_envelope(projection, field)
        for field in (
            "total_internal_action_work",
            "resource_ledger_nodes",
            "resource_ledger_entries",
            "source_image_publications",
            "source_image_projection_publications",
        )
    }
    blockers = common_temporal_blockers(projection, rejection, _metric_int)
    if projection and not all(
        _metric_int(row["source_image_publications"]) > 0
        and _metric_int(row["source_image_projection_publications"]) > 0
        and bool(row["runtime_image_matches_scalar"])
        and bool(row["source_image_replay_stable"])
        for row in projection
    ):
        blockers.append("source_image_runtime_contract_unverified")
    if not envelopes["total_internal_action_work"]:
        blockers.append("internal_action_work_exceeds_doubling_envelope")
    for field in (
        "resource_ledger_nodes",
        "resource_ledger_entries",
        "source_image_publications",
        "source_image_projection_publications",
    ):
        if not envelopes[field]:
            blockers.append(field + "_exceeds_doubling_envelope")
    if any(
        _metric_int(current["higher_concrete_operation_evaluations"])
        > 2 * _metric_int(previous["higher_concrete_operation_evaluations"]) + 64
        for previous, current in itertools.pairwise(projection)
    ):
        blockers.append("higher_interface_work_exceeds_doubling_envelope")
    interpreter_observed = any(
        _metric_int(row["temporal_leaf_diamond_descents"]) > 0 for row in projection
    )
    continuation_observed = any(
        _metric_int(row["higher_action_continuation_requests"]) > 0
        for row in projection
    )
    if interpreter_observed or continuation_observed:
        blockers.append("powered_output_still_replays_temporal_interpreter")
    return {
        "version": "0.63.0-schema8-certified-execution",
        "status": "RED" if blockers else "GREEN",
        "construction": construction,
        "projection": projection,
        "source_audit": _source_audit(),
        "execution_available": rejection is None,
        "execution_status": "available" if rejection is None else "unavailable",
        "measurements_complete": rejection is None and bool(projection),
        "measured_scaling_gate": "PASS" if not blockers else "BLOCKED",
        "release_blockers": blockers,
        "measured_doubling_envelopes": envelopes,
        "growth_policy": "linear-or-sublinear measured work and retention; no absolute cell cap",
        "execution_rejection_type": (
            None if rejection is None else type(rejection).__name__
        ),
        "execution_rejection_reason": None if rejection is None else str(rejection),
        "temporal_leaf_interpreter_present": interpreter_observed,
        "temporal_continuation_interpreter_present": continuation_observed,
        "cache_scope": "per-index; no prior index query memos reused",
    }


def main() -> int:
    from devtools.checks.test_run_evidence import source_fingerprint

    fingerprint = source_fingerprint(ROOT)
    result = run_probe()
    result["source_fingerprint"] = fingerprint
    result["source_unchanged"] = fingerprint == source_fingerprint(ROOT)
    out = report_output(
        "devtools.benchmarks.reverse_temporal_power_probe", "report.json"
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("x") as stream:
        stream.write(json.dumps(result, sort_keys=True, separators=(",", ":")) + "\n")
    print(json.dumps(result, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))

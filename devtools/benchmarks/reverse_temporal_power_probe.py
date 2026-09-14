"""Schema-six probe separating compiled images from actual projection work.

Compact binary action syntax and a small image graph do not certify output
absorption. Report concrete continuation work, semantic interpreter frames,
and temporal leaf descents alongside canonical spatial/temporal populations.
"""

from __future__ import annotations

import ast
import itertools
import json
from collections.abc import Mapping, Sequence
from time import perf_counter

from devtools.benchmarks.tile_projection_accounting import (
    projection_accounting,
)
from devtools.paths import repository_root

ROOT = repository_root()


CONSTRUCTION_INDICES = (16, 256, 1_000_000, 10**18)
PROJECTION_INDICES = (16, 32, 64, 128, 256)


def _metric_int(value: object) -> int:
    if type(value) is not int:
        raise AssertionError(("probe-metric-is-not-an-exact-integer", value))
    return value


def _construction_rows() -> list[dict[str, int | float]]:
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

    rows = []
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
    from number_compiler.hashlife.observation.tile_projection import LazyProjection
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

    rows = []
    for generation in PROJECTION_INDICES:
        term = ReverseAddPoweredTerm(196, generation, base=10)
        position = max(0, term.maximum_width // 3)
        started = perf_counter()
        digit = term.digit(position)
        elapsed = perf_counter() - started
        if digit != _scalar_digit(generation, position):
            raise AssertionError((generation, position, digit))
        metrics = term.metrics()
        point_metrics = term._point_index().metrics()
        behavior = term.behavior_metrics()
        scheduler_work = projection_accounting(point_metrics)
        projection = term._point_index()._lazy_application
        if type(projection) is not LazyProjection:
            raise AssertionError(
                ("reverse-projection-is-not-tile-hashlife", generation)
            )
        if (
            metrics.hashlife_section_cache_entries
            or metrics.hashlife_leaf_cache_entries
        ):
            raise AssertionError(("retired-output-path-reappeared", generation))
        if metrics.hashlife_direct_powered_point_queries != 1:
            raise AssertionError(("not-direct-point", generation, metrics))
        if not point_metrics.bounded_application_enabled:
            raise AssertionError(
                ("bounded-application-not-installed", generation, metrics)
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
                **scheduler_work,
                "retained_tile_output_nodes": metrics.completed_result_entries,
                "retained_tile_action_nodes": metrics.field_action_nodes,
                "retained_tile_logical_extent": term.maximum_width,
                "retained_tile_source_extent": len(term.seed_pair),
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
                "higher_concrete_operation_evaluations": point_metrics.higher_concrete_operation_evaluations,
                "higher_semantic_evaluations": point_metrics.higher_semantic_evaluations,
                "higher_semantic_task_frames": point_metrics.higher_semantic_task_frames,
                "higher_action_continuation_requests": point_metrics.higher_action_continuation_requests,
                "temporal_leaf_diamond_descents": point_metrics.temporal_leaf_diamond_descents,
                "digit": digit,
                "projection_seconds": elapsed,
                "direct_powered_point_queries": metrics.hashlife_direct_powered_point_queries,
                "boundary_cache_entries": metrics.hashlife_boundary_cache_entries,
                "retained_spacetime_nodes": metrics.retained_execution_nodes,
                "canonical_history_word_roots": metrics.canonical_program_word_roots,
                "canonical_spacetime_macrocell_roots": metrics.canonical_spacetime_macrocell_roots,
                "recursive_action_left_nodes": metrics.recursive_action_left_nodes,
                "recursive_action_right_nodes": metrics.recursive_action_right_nodes,
                "recursive_value_cache_entries": metrics.recursive_value_cache_entries,
                "spacetime_macro_cache_hits": metrics.spacetime_macro_cache_hits,
                "spacetime_macro_cache_misses": metrics.spacetime_macro_cache_misses,
                "spacetime_macro_cache_entries": metrics.spacetime_macro_cache_entries,
                "sparse_carrier_layers_left": metrics.sparse_carrier_layers_left,
                "sparse_carrier_layers_right": metrics.sparse_carrier_layers_right,
                "raw_spacetime_boundary_cache_entries": metrics.raw_spacetime_boundary_cache_entries,
                "retained_cache_accounting_delta": metrics.retained_cache_accounting_delta,
                "spacetime_tile_output_entries": metrics.spacetime_tile_output_entries,
                "spacetime_tile_output_max_level": metrics.spacetime_tile_output_max_level,
                "spacetime_temporal_absorption_max": metrics.spacetime_temporal_absorption_max,
                "left_boundary_residuals": metrics.left_boundary_residuals,
                "right_boundary_residuals": metrics.right_boundary_residuals,
                "temporal_leaf_applications": metrics.hashlife_temporal_leaf_applications,
                "bounded_application_enabled": point_metrics.bounded_application_enabled,
                # Legacy key counts observed spatial effects, not temporal states.
                "bounded_temporal_state_classes": point_metrics.bounded_application_temporal_state_classes,
                "reverse_t2_proof_left_state_classes": point_metrics.reverse_t2_proof_left_state_classes,
                "reverse_t2_proof_right_state_classes": point_metrics.reverse_t2_proof_right_state_classes,
                "spatial_interval_action_classes": behavior.spatial_interval_action_classes,
                "spatial_interval_action_class_bound": behavior.spatial_interval_action_class_bound,
                "carry_port_function_class_bound": behavior.carry_port_function_class_bound,
                "minimal_interval_class_code_bits": behavior.temporal_cell_payload_bits,
                "bounded_temporal_action_classes": point_metrics.bounded_application_temporal_action_classes,
                "bounded_exact_spatial_occurrences": point_metrics.bounded_application_exact_spatial_occurrences,
                "bounded_symbolic_action_nodes": point_metrics.bounded_application_symbolic_action_nodes,
                "bounded_jump_entries": point_metrics.bounded_application_jump_entries,
                "bounded_primitive_step_evaluations": point_metrics.bounded_application_primitive_step_evaluations,
                "bounded_action_compositions": point_metrics.bounded_application_action_compositions,
                "bounded_action_applications": point_metrics.bounded_application_action_applications,
                "bounded_nonlinear_branch_evaluations": point_metrics.bounded_application_nonlinear_branch_evaluations,
                "bounded_exact_endpoint_entries": point_metrics.bounded_application_exact_endpoint_entries,
                "unquotiented_recursive_application_nodes": behavior.unquotiented_recursive_application_description_nodes,
                "bounded_temporal_runtime_cutover_complete": behavior.bounded_temporal_runtime_cutover_complete,
                "bounded_temporal_runtime_cutover_blocker": behavior.bounded_temporal_runtime_cutover_blocker,
                "temporal_parent_requests": point_metrics.temporal_parent_requests,
                "temporal_parent_early_hits": point_metrics.temporal_parent_early_hits,
                "temporal_parent_compositions": point_metrics.temporal_parent_compositions,
                "temporal_parent_late_duplicate_reductions": point_metrics.temporal_parent_late_duplicate_reductions,
                "spatial_parent_requests": point_metrics.spatial_parent_requests,
                "spatial_parent_cache_hits": point_metrics.spatial_parent_cache_hits,
                "whole_word_sweeps": point_metrics.whole_word_sweeps,
                "whole_word_symbol_visits": point_metrics.whole_word_symbol_visits,
                "proof_machine_applications": point_metrics.proof_machine_applications,
                "new_canonical_field_images_published": point_metrics.new_canonical_field_images_published,
                "field_image_nodes": point_metrics.field_image_nodes,
                "field_interface_nodes": point_metrics.field_interface_nodes,
                "total_internal_action_work": point_metrics.total_internal_action_work,
            }
        )
    return rows


def _source_audit() -> dict[str, bool]:
    hashlife = (
        ROOT / "src" / "number_compiler" / "hashlife/observation/hashlife_projection.py"
    ).read_text()
    reverse = (
        ROOT / "src" / "number_compiler" / "sequences/reverse_add/power.py"
    ).read_text()
    proof = ROOT / "devtools" / "proofs"
    runtime = (proof / "block_runtime.py").read_text()
    spacetime = (proof / "block_spacetime_runtime.py").read_text()
    compatibility_runtime = runtime + spacetime
    boundary = (ROOT / "devtools" / "proofs" / "spacetime_boundary.py").read_text()
    router_path = ROOT / "src" / "number_compiler" / "sequences" / "runtime_router.py"
    router_tree = ast.parse(router_path.read_text(), filename=str(router_path))
    router_imports = {
        node.module.lstrip(".")
        for node in ast.walk(router_tree)
        if isinstance(node, ast.ImportFrom) and node.module
    } | {
        alias.name
        for node in ast.walk(router_tree)
        if isinstance(node, ast.Import)
        for alias in node.names
    }
    generic_executor_imported = any(
        name.endswith("diamond_runtime") for name in router_imports
    )
    checks = {
        "causal_engine_absent_from_reverse_power": "ReverseAddCausalSpacetimeEngine"
        not in reverse,
        "t2_partition_interpreter_deleted": "def _partition3" not in hashlife
        and "def _leaf_partition3" not in hashlife,
        "whole_output_projection_deleted": "def output_word" not in hashlife,
        "ordinary_point_fallback_deleted": "def point(" not in hashlife,
        "prefix_pop_residual_deleted": "program_pop_last" not in runtime,
        "history_word_carrier_deleted": "from ..program_word"
        not in compatibility_runtime
        and "CanonicalWord" not in compatibility_runtime,
        "exact_future_tile_output_deleted": "def _output_tile_macro" not in spacetime,
        "bounded_temporal_application_installed": (
            ROOT
            / "src"
            / "number_compiler"
            / "hashlife/execution/bounded_application.py"
        ).exists(),
        "certified_family_has_no_generic_executor_import": not generic_executor_imported,
        "raw_spacetime_boundary_runtime_deleted": (
            "import SpacetimeBoundary" not in compatibility_runtime
            and "SpacetimeBoundary," not in compatibility_runtime
            and "intern_boundary(" not in compatibility_runtime
            and "_intern_spacetime_state" not in compatibility_runtime
            and "_advance_effect_boundary" not in compatibility_runtime
        ),
        "raw_boundary_carrier_class_deleted": "class SpacetimeBoundary" not in boundary,
    }
    if not all(checks.values()):
        raise AssertionError(checks)
    return checks


def _projection_closure_flags(
    rows: Sequence[Mapping[str, object]],
) -> tuple[bool, bool, bool, bool]:
    """Compatibility helper retained for older release tests.

    ``carrier_fixed`` and ``legacy_removed`` mean the direct-only path is
    installed. The sample flag compares symbolic program retention and actual
    discovery work with the binary index size. Finite spatial carry classes
    are not temporal states, and no finite sample proves global closure.
    """
    carrier_fixed = all(
        _metric_int(row.get("sequential_generation_advances", 0)) == 0
        and _metric_int(row.get("higher_action_continuation_requests", 0)) == 0
        and _metric_int(row.get("direct_powered_point_queries", 1)) >= 1
        for row in rows
    )
    legacy_removed = all(
        _metric_int(row.get("section_cache_entries", 0)) == 0
        and _metric_int(row.get("leaf_cache_entries", 0)) == 0
        for row in rows
    )
    polylog_sample = bool(rows) and all(
        _metric_int(row.get("unquotiented_recursive_application_nodes", 1)) == 0
        and _metric_int(row.get("bounded_symbolic_action_nodes", 10**9))
        <= 4 * max(1, _metric_int(row.get("index_bits", 0)))
        and _metric_int(row.get("bounded_nonlinear_branch_evaluations", 10**9))
        <= 4 * max(1, _metric_int(row.get("index_bits", 0)))
        for row in rows
    )
    return (
        carrier_fixed,
        legacy_removed,
        polylog_sample,
        False,  # No temporal successor-closure theorem is supplied by this probe.
    )


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
    flags = _projection_closure_flags(projection)
    envelopes = {
        field: _doubling_envelope(projection, field)
        for field in (
            "total_internal_action_work",
            "resource_ledger_nodes",
            "resource_ledger_entries",
            "completed_result_entries",
            "higher_semantic_task_frames",
        )
    }
    blockers: list[str] = []
    if not projection:
        blockers.append("execution_measurements_missing")
    if rejection is not None:
        blockers.append("certified_execution_unavailable")
    if projection and not all(
        _metric_int(row["whole_word_sweeps"]) == 0
        and _metric_int(row["whole_word_symbol_visits"]) == 0
        and _metric_int(row["proof_machine_applications"]) == 0
        for row in projection
    ):
        blockers.append("forbidden_execution_work_observed")
    if projection and not all(
        _metric_int(row["temporal_parent_compositions"])
        <= 2 * max(1, _metric_int(row["index_bits"])) + 4
        for row in projection
    ):
        blockers.append("temporal_composition_exceeds_binary_envelope")
    if projection and not all(
        _metric_int(row["tile_temporal_action_publications"]) > 0 for row in projection
    ):
        blockers.append("certified_path_published_no_tile_actions")
    if not envelopes["total_internal_action_work"]:
        blockers.append("internal_action_work_exceeds_doubling_envelope")
    for field in (
        "resource_ledger_nodes",
        "resource_ledger_entries",
        "completed_result_entries",
        "higher_semantic_task_frames",
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
        "version": "0.62.0-schema6-certified-execution",
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
        "direct_only_fast_path": rejection is None,
        "whole_state_successor_loop_present": False,
        "temporal_leaf_interpreter_present": interpreter_observed,
        "temporal_continuation_interpreter_present": continuation_observed,
        "prefix_pop_residual_present": False,
        "history_word_carrier_present": False,
        "spacetime_macrocell_absorption_installed": False,
        "linear_bisimulation_checkpoint_installed": False,
        "lazy_program_projection_installed": False,
        "cache_scope": "per-index; no prior index query memos reused",
        "bounded_temporal_application_installed": rejection is None,
        "spacetime_logarithmic_closure_proved": flags[3],
    }


def main() -> int:
    from devtools.checks.test_run_evidence import source_fingerprint

    fingerprint = source_fingerprint(ROOT)
    result = run_probe()
    result["source_fingerprint"] = fingerprint
    result["source_unchanged"] = fingerprint == source_fingerprint(ROOT)
    out = ROOT / "results" / ("reverse_temporal_power_" + fingerprint[:12] + ".json")
    out.parent.mkdir(exist_ok=True)
    with out.open("x") as stream:
        stream.write(json.dumps(result, sort_keys=True, separators=(",", ":")) + "\n")
    print(json.dumps(result, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

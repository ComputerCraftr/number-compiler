"""Release probe for source-independent physical-Collatz block powering."""

from __future__ import annotations

import itertools
import json
from time import perf_counter

from devtools.benchmarks.tile_projection_accounting import (
    projection_accounting,
)
from devtools.checks.dependency_graph import source_syntax
from devtools.paths import repository_root
from number_compiler.api.number_api import NumberCompiler
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm

ROOT = repository_root()

CONSTRUCTION_STEPS = (16, 256, 1_000_000, 10**18)
PROJECTION_STEPS = (16, 32, 64, 128, 256)


def _metric_int(value: object) -> int:
    if type(value) is not int:
        raise AssertionError(("probe-metric-is-not-an-exact-integer", value))
    return value


def _physical(value: int) -> int:
    return 3 * value + 1 if value & 1 else value // 2


def _scalar(seed: int, steps: int) -> int:
    value = int(seed)
    for _ in range(int(steps)):
        value = _physical(value)
    return value


def _construction_rows() -> list[dict[str, int | float]]:
    rows = []
    for steps in CONSTRUCTION_STEPS:
        started = perf_counter()
        term = PoweredCollatzTerm(27, steps)
        elapsed = perf_counter() - started
        metrics = term.metrics()
        bits = max(1, steps.bit_length())
        if metrics.operator_nodes > 4 * bits or metrics.compose_operations > 4 * bits:
            raise AssertionError((steps, metrics))
        if metrics.point_queries or metrics.direct_powered_point_queries:
            raise AssertionError(("construction-executed-endpoint", steps))
        rows.append(
            {
                "steps": steps,
                "index_bits": bits,
                "operator_nodes": metrics.operator_nodes,
                "compose_operations": metrics.compose_operations,
                "syntax_depth_bound": metrics.syntax_depth_bound,
                "construction_seconds": elapsed,
                "point_queries": metrics.point_queries,
            }
        )
    return rows


def _projection_rows() -> list[dict[str, object]]:
    rows = []
    for steps in PROJECTION_STEPS:
        term = PoweredCollatzTerm(27, steps)
        expected = _scalar(27, steps)
        started = perf_counter()
        low = term.digit(0)
        elapsed = perf_counter() - started
        if low != (expected & 1):
            raise AssertionError((steps, low, expected))
        metrics = term.metrics()
        behavior = term.behavior_metrics()
        point_metrics = term.metrics()
        scheduler_work = projection_accounting(point_metrics)
        if metrics.direct_powered_point_queries != 1:
            raise AssertionError(("not-direct-point", steps, metrics))
        if not metrics.resource_audit_complete or metrics.resource_accounting_mismatch:
            raise AssertionError(("incomplete-resource-inventory", steps, metrics))
        if (
            metrics.forbidden_future_payloads
            or metrics.retained_unbounded_future_integers
        ):
            raise AssertionError(("future-payload-retained", steps, metrics))
        rows.append(
            {
                **scheduler_work,
                "steps": steps,
                "index_bits": max(1, steps.bit_length()),
                "schema_version": metrics.metrics_schema_version,
                "resource_audit_complete": metrics.resource_audit_complete,
                "resource_accounting_mismatch": metrics.resource_accounting_mismatch,
                "forbidden_future_payloads": metrics.forbidden_future_payloads,
                "retained_unbounded_future_integers": metrics.retained_unbounded_future_integers,
                "retained_entries": metrics.resource_ledger_entries,
                "cache_slots": metrics.cache_slots,
                "exact_source_occurrences": metrics.exact_source_occurrences,
                "spatial_occurrence_bindings": metrics.spatial_occurrence_bindings,
                "spatial_binding_nodes": metrics.spatial_binding_nodes,
                "canonical_transfer_nodes": metrics.canonical_transfer_nodes,
                "temporal_program_nodes": metrics.temporal_program_nodes,
                "finite_port_state_nodes": metrics.finite_port_state_nodes,
                "other_retained_nodes": metrics.other_retained_nodes,
                "retained_nodes": metrics.resource_ledger_nodes,
                "maximum_arithmetic_bits": metrics.maximum_arithmetic_bits,
                "bounded_limb_operations": metrics.bounded_limb_operations,
                "higher_concrete_operation_evaluations": metrics.higher_concrete_operation_evaluations,
                "low_bit": low,
                "projection_seconds": elapsed,
                "operator_nodes": metrics.operator_nodes,
                "direct_powered_point_queries": metrics.direct_powered_point_queries,
                "retained_spacetime_nodes": metrics.retained_execution_nodes,
                "canonical_history_word_roots": metrics.canonical_program_word_roots,
                "canonical_spacetime_macrocell_roots": metrics.canonical_spacetime_macrocell_roots,
                "recursive_action_left_nodes": metrics.recursive_action_left_nodes,
                "recursive_action_right_nodes": metrics.recursive_action_right_nodes,
                "recursive_value_cache_entries": metrics.recursive_value_cache_entries,
                "spacetime_macro_cache_hits": metrics.spacetime_macro_cache_hits,
                "spacetime_macro_cache_misses": metrics.spacetime_macro_cache_misses,
                "spacetime_macro_cache_entries": metrics.spacetime_macro_cache_entries,
                "raw_spacetime_boundary_cache_entries": metrics.raw_spacetime_boundary_cache_entries,
                "retained_cache_accounting_delta": metrics.retained_cache_accounting_delta,
                "sparse_carrier_layers_left": metrics.sparse_carrier_layers_left,
                "sparse_carrier_layers_right": metrics.sparse_carrier_layers_right,
                "spacetime_tile_output_entries": metrics.spacetime_tile_output_entries,
                "spacetime_tile_output_max_level": metrics.spacetime_tile_output_max_level,
                "spacetime_temporal_absorption_max": metrics.spacetime_temporal_absorption_max,
                "left_boundary_residuals": metrics.left_boundary_residuals,
                "right_boundary_residuals": metrics.right_boundary_residuals,
                "bounded_application_enabled": metrics.bounded_application_enabled,
                "bounded_temporal_state_classes": metrics.bounded_application_temporal_state_classes,
                "bounded_temporal_action_classes": metrics.bounded_application_temporal_action_classes,
                "bounded_exact_spatial_occurrences": metrics.bounded_application_exact_spatial_occurrences,
                "bounded_symbolic_action_nodes": metrics.bounded_application_symbolic_action_nodes,
                "bounded_jump_entries": metrics.bounded_application_jump_entries,
                "bounded_primitive_step_evaluations": metrics.bounded_application_primitive_step_evaluations,
                "bounded_residual_physical_steps": metrics.bounded_application_residual_physical_steps,
                "bounded_temporal_runtime_cutover_complete": behavior.bounded_temporal_runtime_cutover_complete,
                "bounded_temporal_runtime_cutover_blocker": behavior.bounded_temporal_runtime_cutover_blocker,
                "collatz_c4_proof_left_state_classes": metrics.collatz_c4_proof_left_state_classes,
                "collatz_c4_proof_right_state_classes": metrics.collatz_c4_proof_right_state_classes,
                "temporal_parent_requests": metrics.temporal_parent_requests,
                "temporal_parent_early_hits": metrics.temporal_parent_early_hits,
                "temporal_parent_compositions": metrics.temporal_parent_compositions,
                "whole_word_sweeps": metrics.whole_word_sweeps,
                "whole_word_symbol_visits": metrics.whole_word_symbol_visits,
                "proof_machine_applications": metrics.proof_machine_applications,
                "new_canonical_field_images_published": metrics.new_canonical_field_images_published,
                "field_image_nodes": metrics.field_image_nodes,
                "field_interface_nodes": metrics.field_interface_nodes,
                "total_internal_action_work": metrics.total_internal_action_work,
                "unquotiented_recursive_application_nodes": behavior.unquotiented_recursive_application_description_nodes,
            }
        )
    return rows


def _source_audit() -> dict[str, bool]:
    api = source_syntax(ROOT / "src" / "number_compiler" / "api/number_api.py")
    block = source_syntax(
        ROOT / "src" / "number_compiler" / "sequences/collatz/block_power.py"
    )
    proof = ROOT / "devtools" / "proofs"
    runtime = source_syntax(proof / "block_runtime.py")
    spacetime = source_syntax(proof / "block_spacetime_runtime.py")
    compatibility_names = runtime.identifiers | spacetime.identifiers
    compatibility_imports = runtime.imports | spacetime.imports
    init = source_syntax(ROOT / "src" / "number_compiler" / "__init__.py")
    bounded = source_syntax(
        ROOT
        / "src"
        / "number_compiler"
        / "hashlife"
        / "execution"
        / "bounded_application.py"
    )
    boundary = source_syntax(proof / "spacetime_boundary.py")
    router_path = ROOT / "src" / "number_compiler" / "sequences" / "runtime_router.py"
    router_syntax = source_syntax(router_path)
    router_imports = router_syntax.imports | router_syntax.dynamic_imports
    generic_executor_imported = router_syntax.unknown_dynamic_import or any(
        name.endswith("diamond_runtime") for name in router_imports
    )
    public_modules = init.imports | init.export_modules | init.dynamic_imports
    checks = {
        "number_api_has_no_orbit_builder": "collatz_orbit_formulas"
        not in api.identifiers,
        "number_api_has_no_ternary_orbit_builder": "collatz_orbit_formulas_ternary"
        not in api.identifiers,
        "number_api_has_no_composite_orbit_builder": "collatz_orbit_formulas_local_composite_radix"
        not in api.identifiers,
        "powered_term_has_no_causal_engine": "CollatzCausalSpacetimeEngine"
        not in block.identifiers,
        "slow_causal_engine_not_public": not any(
            name.endswith("collatz_spacetime") for name in public_modules
        )
        and "CollatzCausalSpacetimeEngine" not in init.exports,
        "legacy_germ_cache_not_public": not any(
            name.endswith("collatz_germ_cache") for name in public_modules
        ),
        "accelerated_reference_power_not_public": "collatz_affine_suffix_event_power_word"
        not in init.identifiers
        and "collatz_affine_suffix_event_power_word" not in init.exports
        and "collatz_affine_suffix_event_power_value" not in init.identifiers
        and "collatz_affine_suffix_event_power_value" not in init.exports,
        "history_word_carrier_deleted": "..program_word" not in compatibility_imports
        and "CanonicalWord" not in compatibility_names,
        "exact_future_tile_output_deleted": "_output_tile_macro"
        not in spacetime.functions,
        "certified_family_has_no_generic_executor_import": not generic_executor_imported,
        "raw_spacetime_boundary_runtime_deleted": (
            "SpacetimeBoundary" not in compatibility_names
            and "intern_boundary" not in compatibility_names
            and "_intern_spacetime_state" not in compatibility_names
            and "_advance_effect_boundary" not in compatibility_names
        ),
        "generic_recursive_carrier_available_for_other_effects": "_RecursiveBoundaryState"
        in compatibility_names,
        "bounded_temporal_application_boundary_present": "build_certified_field_application"
        in bounded.identifiers,
        "raw_boundary_carrier_class_deleted": "SpacetimeBoundary"
        not in boundary.classes,
    }
    if not all(checks.values()):
        raise AssertionError(checks)
    return checks


def run_probe() -> dict[str, object]:
    from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError

    rejection: UnsupportedInterfaceError | None = None
    try:
        projection = _projection_rows()
    except UnsupportedInterfaceError as error:
        projection = []
        rejection = error
    exact: dict[str, int] = {}
    if rejection is None:
        compiler = NumberCompiler()
        exact = {
            str(radix): compiler.nth("collatz", 10, seed=27, radix=radix)
            for radix in (2, 3, 6)
        }
        if set(exact.values()) != {214}:
            raise AssertionError(exact)
    tail_sublinear = False
    if len(projection) >= 2:
        prev, tail = projection[-2], projection[-1]
        prev_steps = _metric_int(prev["bounded_primitive_step_evaluations"])
        tail_steps = _metric_int(tail["bounded_primitive_step_evaluations"])
        tail_sublinear = prev_steps > 0 and tail_steps < 2 * prev_steps
    bounded_cutover = bool(projection) and all(
        _metric_int(row["bounded_application_enabled"]) == 1
        and _metric_int(row["bounded_temporal_runtime_cutover_complete"]) == 1
        and _metric_int(row["unquotiented_recursive_application_nodes"]) == 0
        and _metric_int(row["sequential_generation_advances"]) == 0
        and _metric_int(row["recursive_value_cache_entries"]) == 0
        for row in projection
    )
    work_envelope = True
    if len(projection) > 1:
        bootstrap = _metric_int(projection[0]["total_internal_action_work"])
        work_envelope = all(
            _metric_int(current["total_internal_action_work"])
            <= 2 * _metric_int(previous["total_internal_action_work"]) + bootstrap
            for previous, current in itertools.pairwise(projection)
        )
    retention_envelope = len(projection) > 1 and all(
        _metric_int(current["completed_result_entries"])
        <= 2 * _metric_int(previous["completed_result_entries"])
        + _metric_int(projection[0]["completed_result_entries"])
        for previous, current in itertools.pairwise(projection)
    )
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
    if not retention_envelope:
        blockers.append("completed_result_entries_exceeds_doubling_envelope")
    if not work_envelope:
        blockers.append("internal_action_work_exceeds_doubling_envelope")
    if any(
        _metric_int(current["higher_concrete_operation_evaluations"])
        > 2 * _metric_int(previous["higher_concrete_operation_evaluations"]) + 64
        for previous, current in itertools.pairwise(projection)
    ):
        blockers.append("higher_interface_work_exceeds_doubling_envelope")
    return {
        "version": "0.62.0-schema7-certified-execution",
        "schema_version": 7,
        "status": "RED" if blockers else "GREEN",
        "construction": _construction_rows(),
        "projection": projection,
        "execution_available": rejection is None,
        "execution_status": "available" if rejection is None else "unavailable",
        "measurements_complete": rejection is None and bool(projection),
        "measured_scaling_gate": "PASS" if not blockers else "BLOCKED",
        "release_blockers": blockers,
        "completed_result_retention_envelope": retention_envelope,
        "execution_rejection_type": (
            None if rejection is None else type(rejection).__name__
        ),
        "execution_rejection_reason": None if rejection is None else str(rejection),
        "source_audit": _source_audit(),
        "public_radix_exactness": exact,
        "public_radix_exactness_available": rejection is None,
        "whole_state_successor_loop_present": False,
        "parity_itinerary_required_for_physical_nth_state": True,
        "history_word_carrier_present": False,
        "spacetime_macrocell_absorption_installed": False,
        "lazy_program_projection_installed": False,
        "linear_bisimulation_checkpoint_installed": False,
        "bounded_temporal_runtime_cutover_complete": bounded_cutover,
        "representative_seed_tail_sublinear": tail_sublinear,
        # Seed 27 now saturates under the measured quotient, but that is not a
        # proof of arbitrary-source logarithmic physical-Collatz projection.
        "spacetime_logarithmic_closure_proved": False,
    }


def main() -> int:
    result = run_probe()
    out = ROOT / "results" / "collatz_temporal_power_metrics.json"
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

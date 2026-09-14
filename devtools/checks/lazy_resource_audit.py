"""Fresh-process exactness, retained-resource, and measured-work audit."""

from __future__ import annotations

import argparse
import json
import os
import resource
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from dataclasses import asdict
from pathlib import Path
from time import perf_counter, process_time
from typing import TypedDict, cast

from devtools.checks.lazy_scaling_audit import (
    MetricSnapshot,
    QueryDelta,
    ScalingSample,
    metric_value,
    sample_deltas,
    scaling_report,
)
from devtools.paths import repository_root
from number_compiler.resources.metric_registry import (
    DIAMOND_MEMO_ROLES,
    DIAMOND_WORK_COUNTERS,
)


class MeasuredPhase(TypedDict):
    position: int
    cpu_seconds: float
    digit: int
    seconds: float
    metrics: MetricSnapshot
    delta: QueryDelta


ROOT = repository_root()
FIELDS = (
    (
        "metrics_schema_version",
        "resource_ledger_entries",
        "resource_ledger_nodes",
        "cache_slots",
        "exact_source_occurrences",
        "spatial_occurrence_bindings",
        "spatial_binding_nodes",
        "canonical_transfer_nodes",
        "temporal_program_nodes",
        "spatial_action_program_nodes",
        "context_program_nodes",
        "boundary_expression_program_nodes",
        "boundary_expression_free_port_references",
        "boundary_expression_max_free_ports",
        "higher_context_program_nodes",
        "higher_unary_program_nodes",
        "higher_observation_cache_entries",
        "expression_closure_program_nodes",
        "expression_closure_parameter_references",
        "expression_call_argument_references",
        "expression_head_cache_entries",
        "context_observation_cache_entries",
        "unary_function_cache_entries",
        "image_action_nodes",
        "diamond_cell_nodes",
        "bimachine_composition_certified",
        "boundary_state_nodes",
        "boundary_function_nodes",
        "primitive_kernel_nodes",
        "finite_expression_nodes",
        "macro_transfer_action_nodes",
        "causal_geometry_nodes",
        "right_reset_certificate_nodes",
        "finite_cycle_certificate_nodes",
        "diamond_instrumentation_complete",
        "canonical_parent_identity_entries",
        "reverse_leaf_binding_entries",
        "reverse_parent_binding_entries",
        "reverse_source_tile_binding_entries",
        "collatz_range_binding_entries",
        "collatz_source_tile_binding_entries",
        "collatz_event_binding_entries",
        "finite_port_state_nodes",
        "other_retained_nodes",
        "collatz_mul3_summary_requests",
        "collatz_mul3_summary_cache_hits",
        "collatz_mul3_summary_evaluations",
        "joint_interval_composition_requests",
        "joint_interval_composition_cache_hits",
        "joint_interval_composition_evaluations",
        "interval_effect_intern_hits",
        "interval_effect_intern_misses",
        "interval_literal_requests",
        "interval_literal_cache_hits",
        "interval_literal_evaluations",
        "interval_reflection_requests",
        "interval_reflection_cache_hits",
        "interval_reflection_identity_hits",
        "interval_reflection_evaluations",
        "reverse_summary_lookup_requests",
        "reverse_summary_lookup_hits",
        "reverse_summary_lookup_misses",
        "reverse_summary_reflection_hits",
        "resource_observed_entries",
        "resource_observed_nodes",
        "resource_accounting_mismatch",
        "resource_peak_entries",
        "resource_peak_nodes",
        "resource_audit_complete",
        "resource_audit_unknown_payloads",
        "resource_unregistered_containers",
        "resource_unregistered_payload_resolvers",
        "forbidden_future_payloads",
        "retained_unbounded_future_integers",
        "source_payload_nodes",
        "compiler_program_nodes",
        "application_program_nodes",
        "transfer_summary_nodes",
        "exact_endpoint_nodes",
        "bounded_application_nonlinear_branch_evaluations",
        "retained_point_response_scalars",
        "bounded_application_primitive_step_evaluations",
        "composition_requests",
        "composition_cache_hits",
        "composition_evaluations",
        "retained_composition_entries",
        "summary_evaluations",
        "summary_cache_hits",
        "symbolic_port_queries",
        "symbolic_maximum_port_bits",
        "bounded_limb_operations",
        "maximum_arithmetic_bits",
        "unbounded_arithmetic_observations",
        "endpoint_lowering_requests",
        "explicitly_materialized_endpoints",
        "resource_work_counters",
        "resource_workspace_peaks",
        "representation_boundary_complete",
        "finite_port_applications",
        "finite_port_decision_visits",
        "reverse_carry_function_classifications",
    )
    + DIAMOND_WORK_COUNTERS
    + tuple(name for name, _ in DIAMOND_MEMO_ROLES)
)


def worker(family: str, steps: int, seed: int | None = None) -> dict[str, object]:
    from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

    seed = (196 if family == "reverse" else 27) if seed is None else seed
    construction_start = perf_counter()
    construction_cpu_start = process_time()
    term = (
        ReverseAddPoweredTerm(seed, steps)
        if family == "reverse"
        else PoweredCollatzTerm(seed, steps)
    )
    construction_seconds = perf_counter() - construction_start
    construction_cpu_seconds = process_time() - construction_cpu_start

    def take() -> MetricSnapshot:
        metrics = term.metrics()
        return {name: getattr(metrics, name) for name in FIELDS}

    construction = take()
    start = perf_counter()
    cpu_start = process_time()
    digit = term.digit(0)
    cold_seconds = perf_counter() - start
    cold_cpu_seconds = process_time() - cpu_start
    cold_process_peak_bytes = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * (
        1 if sys.platform == "darwin" else 1024
    )
    snapshot_start = perf_counter()
    cold = take()
    cold_metrics_snapshot_seconds = perf_counter() - snapshot_start
    start = perf_counter()
    cpu_start = process_time()
    repeated = term.digit(0)
    warm_seconds = perf_counter() - start
    warm_cpu_seconds = process_time() - cpu_start
    warm = take()
    query_phases: dict[str, MeasuredPhase] = {}
    previous = warm
    for name, position in (("adjacent", 1), ("revisited", 0)):
        start, cpu_start = perf_counter(), process_time()
        observed = term.digit(position)
        seconds, cpu_seconds = perf_counter() - start, process_time() - cpu_start
        measured = take()
        query_phases[name] = {
            "position": position,
            "digit": observed,
            "seconds": seconds,
            "cpu_seconds": cpu_seconds,
            "metrics": measured,
            "delta": sample_deltas(previous, measured),
        }
        previous = measured
    # Independent scalar arithmetic is an oracle after the measured queries;
    # it does not supply any digit or branch to the production engine.
    value = seed
    oracle_odd_events = 0
    oracle_one_shift_events = 0
    for _ in range(steps):
        if family == "reverse":
            value += int(str(value)[::-1])
        else:
            if value % 2:
                oracle_odd_events += 1
                oracle_one_shift_events += (3 * value + 1) % 4 == 2
            value = value // 2 if value % 2 == 0 else 3 * value + 1
    expected = value % (10 if family == "reverse" else 2)
    assert digit == repeated == expected
    assert query_phases["adjacent"]["digit"] == value // (
        10 if family == "reverse" else 2
    ) % (10 if family == "reverse" else 2)
    assert query_phases["revisited"]["digit"] == expected
    assert cold["resource_audit_complete"] == 1
    for measured in (
        construction,
        cold,
        warm,
        *(phase["metrics"] for phase in query_phases.values()),
    ):
        assert metric_value(measured, "representation_boundary_complete") == 1
        assert metric_value(measured, "composition_requests") == metric_value(
            measured, "composition_cache_hits"
        ) + metric_value(measured, "composition_evaluations")
        assert metric_value(
            measured, "joint_interval_composition_requests"
        ) == metric_value(
            measured, "joint_interval_composition_cache_hits"
        ) + metric_value(measured, "joint_interval_composition_evaluations")
        assert metric_value(measured, "interval_literal_requests") == metric_value(
            measured, "interval_literal_cache_hits"
        ) + metric_value(measured, "interval_literal_evaluations")
        assert metric_value(measured, "interval_reflection_requests") == metric_value(
            measured, "interval_reflection_cache_hits"
        ) + metric_value(measured, "interval_reflection_identity_hits") + metric_value(
            measured, "interval_reflection_evaluations"
        )
        assert metric_value(measured, "collatz_mul3_summary_requests") == metric_value(
            measured, "collatz_mul3_summary_cache_hits"
        ) + metric_value(measured, "collatz_mul3_summary_evaluations")
        assert metric_value(
            measured, "reverse_summary_lookup_requests"
        ) == metric_value(measured, "reverse_summary_lookup_hits") + metric_value(
            measured, "reverse_summary_lookup_misses"
        )
        assert metric_value(measured, "resource_observed_nodes") == sum(
            metric_value(measured, name)
            for name in (
                "source_payload_nodes",
                "spatial_binding_nodes",
                "canonical_transfer_nodes",
                "temporal_program_nodes",
                "finite_port_state_nodes",
                "exact_endpoint_nodes",
                "other_retained_nodes",
                "image_action_nodes",
                "diamond_cell_nodes",
                "spatial_action_program_nodes",
            )
        )
    assert cold["resource_accounting_mismatch"] == 0
    assert cold["resource_unregistered_containers"] == 0
    assert cold["exact_endpoint_nodes"] == cold["endpoint_lowering_requests"] == 0
    assert cold["diamond_instrumentation_complete"] == 1
    assert cold["bimachine_composition_certified"] == 1
    assert cold["sequential_generation_advances"] == 0
    for measured in (
        cold,
        warm,
        *(phase["metrics"] for phase in query_phases.values()),
    ):
        for prefix in (
            "diamond",
            "macro_transfer",
            "image_program",
            "output_function",
            "boundary_substitution",
            "spatial_parent",
        ):
            assert metric_value(measured, prefix + "_requests") == metric_value(
                measured, prefix + "_cache_hits"
            ) + metric_value(measured, prefix + "_evaluations")
    assert (
        cold["forbidden_future_payloads"]
        == cold["retained_unbounded_future_integers"]
        == 0
    )
    assert cold["resource_ledger_entries"] == cold["resource_observed_entries"]
    assert cold["resource_ledger_nodes"] == cold["resource_observed_nodes"]
    behavior = term.behavior_metrics()
    action_inventory = {
        "execution_family": behavior.temporal_quotient_family,
        "temporal_program_nodes": cold["temporal_program_nodes"],
        "image_action_nodes": cold["image_action_nodes"],
        "canonical_transfer_nodes": cold["canonical_transfer_nodes"],
        "spatial_action_program_nodes": cold["spatial_action_program_nodes"],
        "context_program_nodes": cold["context_program_nodes"],
        "boundary_state_nodes": cold["boundary_state_nodes"],
        "boundary_function_nodes": cold["boundary_function_nodes"],
        "macro_transfer_bindings": cold["macro_transfer_cache_entries"],
        "macro_transfer_action_nodes": cold["macro_transfer_action_nodes"],
        "image_program_bindings": cold["image_program_cache_entries"],
    }
    return {
        "action_inventory": action_inventory,
        "family": family,
        "seed": seed,
        "steps": steps,
        "point": 0,
        "original_seed_bits": seed.bit_length(),
        "oracle_odd_events": oracle_odd_events,
        "oracle_one_shift_events": oracle_one_shift_events,
        "digit": digit,
        "scalar_digit": expected,
        "exact": True,
        "cold_seconds": cold_seconds,
        "warm_seconds": warm_seconds,
        "cold_cpu_seconds": cold_cpu_seconds,
        "warm_cpu_seconds": warm_cpu_seconds,
        "construction_seconds": construction_seconds,
        "construction_cpu_seconds": construction_cpu_seconds,
        "cold_metrics_snapshot_seconds": cold_metrics_snapshot_seconds,
        "cold_process_peak_bytes": cold_process_peak_bytes,
        "cold_query_delta": sample_deltas(construction, cold),
        "warm_query_delta": sample_deltas(cold, warm),
        "query_phases": query_phases,
        "construction": construction,
        "cold": cold,
        "warm": warm,
        "inventory": [asdict(item) for item in term.metrics().resource_inventory],
    }


def _run_worker(case: tuple[str, int, int | None]) -> dict[str, object]:
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "devtools.checks.lazy_resource_audit",
            "--worker",
            case[0],
            str(case[1]),
            *([] if case[2] is None else ["--seed", str(case[2])]),
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=ROOT,
        env=dict(os.environ),
    )
    value: object = json.loads(completed.stdout)
    if not isinstance(value, dict) or any(not isinstance(key, str) for key in value):
        raise TypeError("worker output must be a JSON object")
    return cast("dict[str, object]", value)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--worker", choices=("reverse", "collatz"))
    parser.add_argument("steps", type=int, nargs="?")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--seed", type=int, help="original input for a single worker")
    parser.add_argument(
        "--stress-collatz",
        action="store_true",
        help="separate fixed 513-bit noncycle workload, never mixed with the seed-27 matrix",
    )
    parser.add_argument(
        "--require-logarithmic",
        action="store_true",
        help="exit nonzero while execution certification or sampled resource growth is blocked",
    )
    parser.add_argument("--workers", type=int, default=1)
    args = parser.parse_args()
    if args.output is None:
        name = (
            "lazy_resource_stress_v7.json"
            if args.stress_collatz
            else "lazy_resource_audit_v7.json"
        )
        args.output = ROOT / "results" / name
    if args.workers < 1:
        parser.error("workers must be positive")
    protected = {
        (ROOT / f"results/{kind}_v{revision}.json").resolve()
        for kind in ("lazy_resource_audit", "lazy_resource_stress")
        for revision in range(2, 7)
    }
    if args.output.resolve() in protected:
        parser.error("historical resource audits must not be overwritten")
    if args.worker is not None:
        if args.steps is None:
            parser.error("worker requires a step count")
        print(json.dumps(worker(args.worker, args.steps, args.seed)))
        return
    if args.seed is not None:
        parser.error(
            "seed requires worker mode; use stress-collatz for the separate fixed wide-source matrix"
        )
    cases = (
        [("collatz", count, (1 << 513) - 1) for count in (16, 32, 64, 128, 256)]
        if args.stress_collatz
        else [
            (family, count, None)
            for family in ("reverse", "collatz")
            for count in (16, 32, 64, 128, 256)
        ]
    )
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        rows = list(pool.map(_run_worker, cases))
    if args.stress_collatz:
        assert all(
            row["original_seed_bits"] == 513
            and row["oracle_odd_events"] == cast("int", row["steps"]) // 2
            and row["oracle_one_shift_events"] == row["oracle_odd_events"]
            for row in rows
        )
    result = {
        "metrics_schema_version": 4,
        "audit_revision": 7,
        "cold_process_per_row": True,
        "maximum_parallel_workers": args.workers,
        "workload": "fixed-513-bit-collatz-noncycle"
        if args.stress_collatz
        else "reverse-196-and-collatz-27",
        "audit_scope": "registered per-index retained objects and measured operation counters",
        "memory_scope": "process high-water bytes include interpreter/import/source/retained/transient allocations; component workspace counters are named maxima, not a byte total",
        "limitations": [
            "Complete bimachine composition certification is separate from measured resource growth; finite samples do not prove logarithmic complexity."
        ],
        "rows": rows,
        "scaling_release_gate": scaling_report(
            [cast("ScalingSample", row) for row in rows]
        ),
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(args.output)
    if args.require_logarithmic and result["scaling_release_gate"]["status"] != "PASS":
        raise SystemExit(
            "BLOCKED: " + ", ".join(result["scaling_release_gate"]["release_blockers"])
        )


if __name__ == "__main__":
    main()

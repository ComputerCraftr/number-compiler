"""Finite-sample release gates for each measured resource, without complexity proofs."""

from __future__ import annotations

import itertools
from collections.abc import Mapping, Sequence
from math import log2
from typing import NotRequired, Required, TypedDict

from number_compiler.resources.metric_registry import DIAMOND_WORK_COUNTERS

MetricSnapshot = dict[str, int | dict[str, int]]


class SeriesAssessment(TypedDict):
    values: list[int]
    doubling_ratios: list[float | None]
    local_exponents: list[float | None]
    values_per_log2_horizon_plus_one: list[float]
    sampled_log_envelope: list[float]
    status: str


class QueryDelta(TypedDict, total=False):
    retained: dict[str, int]
    work: dict[str, int]
    workspace_peak_increases: dict[str, int]


class QueryPhase(TypedDict, total=False):
    delta: QueryDelta


class ScalingSample(TypedDict):
    family: str
    steps: int
    cold: MetricSnapshot
    warm: MetricSnapshot
    cold_seconds: float
    warm_seconds: float
    query_phases: NotRequired[dict[str, QueryPhase]]


class FamilyAssessment(TypedDict, total=False):
    status: Required[str]
    reason: str
    steps: list[int]
    cold_metrics: dict[str, SeriesAssessment]
    warm_work_metrics: dict[str, SeriesAssessment]
    cold_blockers: list[str]
    warm_blockers: list[str]
    other_query_work_metrics: dict[str, SeriesAssessment]
    other_query_blockers: list[str]
    missing_instrumentation: list[str]
    cold_seconds: list[float]
    warm_seconds: list[float]


class ScalingAssessment(TypedDict):
    status: str
    sampled_envelope_status: str
    release_blockers: list[str]
    criterion: str
    slack: float
    bimachine_composition: str
    identical_point_primitive_reuse: str
    scope: str
    timing_policy: str
    families: dict[str, FamilyAssessment]


def work_counters(snapshot: Mapping[str, int | dict[str, int]]) -> dict[str, int]:
    counters = snapshot["resource_work_counters"]
    if not isinstance(counters, dict):
        raise TypeError("resource_work_counters must be a counter mapping")
    return counters


def metric_value(
    snapshot: Mapping[str, int | dict[str, int]], name: str, default: int = 0
) -> int:
    value = snapshot.get(name, default)
    if not isinstance(value, int):
        raise TypeError(f"{name} must be an integer measurement")
    return value


SPACE_METRICS = (
    "cache_slots",
    "resource_observed_nodes",
    "resource_peak_entries",
    "resource_peak_nodes",
    "source_payload_nodes",
    "compiler_program_nodes",
    "application_program_nodes",
    "temporal_program_nodes",
    "spatial_occurrence_bindings",
    "spatial_binding_nodes",
    "image_action_nodes",
    "diamond_cell_nodes",
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
    "primitive_spatial_cache_entries",
    "boundary_state_nodes",
    "boundary_function_nodes",
    "primitive_kernel_nodes",
    "finite_expression_nodes",
    "macro_transfer_action_nodes",
    "causal_geometry_nodes",
    "right_reset_certificate_nodes",
    "finite_cycle_certificate_nodes",
    "diamond_cache_entries",
    "macro_transfer_cache_entries",
    "image_program_cache_entries",
    "output_function_cache_entries",
    "boundary_substitution_cache_entries",
    "spatial_parent_cache_entries",
    "canonical_parent_identity_entries",
    "canonical_transfer_nodes",
    "finite_port_state_nodes",
    "exact_endpoint_nodes",
    "other_retained_nodes",
    "reverse_leaf_binding_entries",
    "reverse_parent_binding_entries",
    "reverse_source_tile_binding_entries",
    "collatz_range_binding_entries",
    "collatz_source_tile_binding_entries",
    "collatz_event_binding_entries",
    "retained_point_response_scalars",
)
WORK_METRICS = (
    "bounded_application_nonlinear_branch_evaluations",
    "bounded_application_primitive_step_evaluations",
)
REQUIRED_COUNTERS = {
    "reverse": ("reverse_offset_dag_visits", "reverse_evaluator_transitions"),
    "collatz": ("collatz_dag_visits", "collatz_evaluator_transitions"),
}


def assess_series(
    steps: Sequence[int], values: Sequence[int], *, slack: float = 1.25
) -> SeriesAssessment:
    """Test a declared log envelope anchored at the smallest measured horizon.

    This is a falsifiable sampled engineering criterion, not a big-O theorem.
    The one-unit allowance accommodates integer counters starting at zero.
    """
    if len(steps) != len(values) or len(steps) < 2:
        raise ValueError("scaling requires at least two paired samples")
    if slack < 1 or any(n <= 0 for n in steps) or any(v < 0 for v in values):
        raise ValueError(
            "positive horizons, nonnegative values and slack >= 1 required"
        )
    if any(b <= a for a, b in itertools.pairwise(steps)):
        raise ValueError("horizons must increase")
    logs = [1 + log2(n) for n in steps]
    normalized = [value / size for value, size in zip(values, logs, strict=True)]
    envelope = [(values[0] + 1) * size / logs[0] * slack for size in logs]
    ratios = [
        None if before == 0 else after / before
        for before, after in itertools.pairwise(values)
    ]
    exponents = [
        None if before == 0 or after == 0 else log2(after / before) / log2(b / a)
        for a, b, before, after in zip(
            steps, steps[1:], values, values[1:], strict=False
        )
    ]
    return {
        "values": list(values),
        "doubling_ratios": ratios,
        "local_exponents": exponents,
        "values_per_log2_horizon_plus_one": normalized,
        "sampled_log_envelope": envelope,
        "status": "PASS"
        if all(v <= bound for v, bound in zip(values, envelope, strict=True))
        else "BLOCKED",
    }


def sample_deltas(
    before: Mapping[str, int | dict[str, int]],
    after: Mapping[str, int | dict[str, int]],
) -> QueryDelta:
    """Keep every measured counter; do not hide warm work behind stable classes."""
    left, right = work_counters(before), work_counters(after)
    return {
        "retained": {
            name: metric_value(after, name) - metric_value(before, name)
            for name in SPACE_METRICS
        },
        "work": {
            name: right.get(name, 0) - left.get(name, 0)
            for name in sorted(left.keys() | right.keys())
            if not (name.endswith("_peak") or "_peak_" in name)
        },
        "workspace_peak_increases": {
            name: right.get(name, 0) - left.get(name, 0)
            for name in sorted(left.keys() | right.keys())
            if (name.endswith("_peak") or "_peak_" in name)
        },
    }


def scaling_report(
    rows: Sequence[ScalingSample], *, slack: float = 1.25
) -> ScalingAssessment:
    families: dict[str, FamilyAssessment] = {}
    for family in sorted({str(row["family"]) for row in rows}):
        samples = sorted(
            (row for row in rows if row["family"] == family),
            key=lambda row: int(row["steps"]),
        )
        steps = [int(row["steps"]) for row in samples]
        if len(steps) < 3:
            families[family] = {
                "status": "BLOCKED",
                "reason": "at least three horizons required",
            }
            continue
        counter_names = set().union(*(work_counters(row["warm"]) for row in samples))
        metrics: dict[str, SeriesAssessment] = {}
        for name in (*SPACE_METRICS, *WORK_METRICS):
            metrics[name] = assess_series(
                steps, [metric_value(row["cold"], name) for row in samples], slack=slack
            )
        warm_metrics: dict[str, SeriesAssessment] = {}
        for name in sorted(counter_names):
            values = [int(work_counters(row["cold"]).get(name, 0)) for row in samples]
            metrics["work." + name] = assess_series(steps, values, slack=slack)
            if not (name.endswith("_peak") or "_peak_" in name):
                delta = [
                    int(work_counters(row["warm"]).get(name, 0)) - value
                    for row, value in zip(samples, values, strict=True)
                ]
                warm_metrics[name] = assess_series(steps, delta, slack=slack)
        other_query_metrics: dict[str, SeriesAssessment] = {}
        phases = set().union(*(row.get("query_phases", {}) for row in samples))
        for phase in sorted(phases):
            names = set().union(
                *(
                    row.get("query_phases", {})
                    .get(phase, {})
                    .get("delta", {})
                    .get("work", {})
                    for row in samples
                )
            )
            for name in sorted(names):
                values = [
                    int(
                        row.get("query_phases", {})
                        .get(phase, {})
                        .get("delta", {})
                        .get("work", {})
                        .get(name, 0)
                    )
                    for row in samples
                ]
                other_query_metrics[phase + "." + name] = assess_series(
                    steps, values, slack=slack
                )
        required = (
            DIAMOND_WORK_COUNTERS
            if all(
                metric_value(row["cold"], "metrics_schema_version") >= 4
                for row in samples
            )
            else REQUIRED_COUNTERS.get(family, ())
        )
        missing = sorted(set(required) - counter_names)
        blockers = [
            name for name, metric in metrics.items() if metric["status"] != "PASS"
        ]
        warm_blockers = [
            name for name, metric in warm_metrics.items() if metric["status"] != "PASS"
        ]
        other_blockers = [
            name
            for name, metric in other_query_metrics.items()
            if metric["status"] != "PASS"
        ]
        families[family] = {
            "steps": steps,
            "cold_metrics": metrics,
            "warm_work_metrics": warm_metrics,
            "cold_blockers": blockers,
            "warm_blockers": warm_blockers,
            "other_query_work_metrics": other_query_metrics,
            "other_query_blockers": other_blockers,
            "missing_instrumentation": missing,
            "status": "BLOCKED"
            if blockers or warm_blockers or other_blockers or missing
            else "PASS",
            "cold_seconds": [row["cold_seconds"] for row in samples],
            "warm_seconds": [row["warm_seconds"] for row in samples],
        }
    sampled = (
        "PASS"
        if families and all(row["status"] == "PASS" for row in families.values())
        else "BLOCKED"
    )
    certified = bool(rows) and all(
        metric_value(row["cold"], "bimachine_composition_certified") == 1
        for row in rows
    )
    release_blockers = [] if certified else ["bimachine_composition_not_certified"]
    if any(
        metric_value(row["cold"], "sequential_generation_advances") > 0 for row in rows
    ):
        release_blockers.append("sequential_generation_advances_observed")
    repeated_primitive_work = any(
        metric_value(row["warm"], name) > metric_value(row["cold"], name)
        for row in rows
        for name in ("primitive_transition_evaluations", "primitive_output_evaluations")
    )
    if repeated_primitive_work:
        release_blockers.append("repeated_identical_point_evaluates_primitive_kernel")
    if sampled != "PASS":
        release_blockers.append(
            "measured_resource_growth_exceeds_sampled_envelope_or_instrumentation_missing"
        )
    return {
        "status": "BLOCKED" if release_blockers else "PASS",
        "sampled_envelope_status": sampled,
        "release_blockers": release_blockers,
        "criterion": "Every measured cold resource and repeated/adjacent/revisited query work counter fits slack*(first_value+1)*(1+log2(N))/(1+log2(first_N)).",
        "slack": slack,
        "bimachine_composition": "CERTIFIED" if certified else "NOT_CERTIFIED",
        "identical_point_primitive_reuse": "BLOCKED"
        if repeated_primitive_work
        else "PASS",
        "scope": "Sampled counter growth; not a proof of asymptotic complexity or complete CPU/byte accounting.",
        "timing_policy": "Wall times and process high-water bytes are observations, excluded from deterministic counter gates.",
        "families": families,
    }

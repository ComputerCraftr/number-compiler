"""Fresh-process orchestration for causal tile growth evidence."""

from __future__ import annotations

import argparse
import json
import math
import os
import statistics
import sys
import tempfile
from collections.abc import Mapping, Sequence
from dataclasses import asdict, fields, replace
from pathlib import Path
from time import perf_counter
from typing import Required, TypedDict, TypeGuard, cast

from devtools.benchmarks.causal_tile_growth_probe import (
    CausalGrowthRow,
    CausalSeriesReport,
    cold_row,
    power_of_two_at_least,
    series_report,
)
from devtools.checks.process_guard import run_guarded
from devtools.checks.validation_policy import (
    PYTHON_COMMAND_SECONDS,
    PYTHON_MEMORY_BYTES,
)
from devtools.git_source import GitSource, git_source, same_git_revision
from devtools.paths import repository_root
from number_compiler.resources.temporal_diagnostics import METRICS_SCHEMA_VERSION


class TrialRecord(TypedDict, total=False):
    scenario: str
    temporal_steps: int
    spatial_width: int
    coordinate: int
    trial: int
    status: Required[str]
    failure_reason: str
    stdout: str
    stderr: str
    returncode: int | None
    process_wall_seconds: float
    sampled_peak_bytes: int
    memory_measurement: str
    memory_samples: int
    git_source_before: dict[str, str | bool]
    git_source_after: dict[str, str | bool]
    row: dict[str, object]


class RequestRecord(TypedDict):
    scenario: str
    temporal_steps: int
    spatial_width: int
    coordinate: int


class RegionManifest(TypedDict):
    requests: list[RequestRecord]


class ProbeManifest(RegionManifest):
    horizons: list[int]
    spatial_widths: list[int]
    fixed_width: int
    fresh_process_trials_per_sample: int
    invocation_limit_seconds: int
    memory_limit_bytes: int


class SampleReport(TypedDict):
    request: RequestRecord
    expected_trials: int
    completed_trials: int
    timing_seconds: dict[str, dict[str, float | None]]
    process_wall_seconds: dict[str, float | None]
    release_blockers: list[str]
    status: str
    trials: Sequence[Mapping[str, object]]


class CausalProbeReport(TypedDict):
    metrics_schema_version: int
    git_source_before: dict[str, str | bool]
    git_source_after: dict[str, str | bool]
    git_revision_unchanged: bool
    evidence_mode: str
    cacheable: bool
    reusable: bool
    fresh_process_trials_per_sample: int
    invocation_limit_seconds: int
    memory_limit_bytes: int
    timed_environment: dict[str, str]
    default_release_horizons: list[int]
    release_manifest_complete: bool
    requested_manifest: ProbeManifest
    required_manifest: ProbeManifest
    observed_manifest: RegionManifest
    missing_manifest: RegionManifest
    collection_complete: bool
    logarithmic_execution_claim: bool
    coordinate_policy: str
    diagnostic_status: str
    status_scope: str
    release_complete: bool
    release_blockers: list[str]
    status: str
    samples: dict[str, list[SampleReport]]
    series: dict[str, CausalSeriesReport]


ROOT = repository_root()
HORIZONS = (16, 32, 64, 128, 256, 512, 1024)
TRIALS = 5
INVOCATION_LIMIT_SECONDS = PYTHON_COMMAND_SECONDS
MEMORY_LIMIT_BYTES = PYTHON_MEMORY_BYTES
RELEASE_FIXED_WIDTH = 16
_TIMING_FIELDS = (
    "setup_seconds",
    "observation_seconds",
    "diagnostics_seconds",
    "cold_seconds",
)


def worker(
    scenario: str, temporal_steps: int, spatial_width: int, coordinate: int
) -> dict[str, object]:
    source = git_source(ROOT)
    row, _ledger = cold_row(
        scenario, temporal_steps, spatial_width, coordinate=coordinate
    )
    return {
        "scenario": scenario,
        "temporal_steps": temporal_steps,
        "spatial_width": spatial_width,
        "coordinate": coordinate,
        "pid": os.getpid(),
        "git_source_before": source.as_dict(),
        "git_source_after": git_source(ROOT).as_dict(),
        "row": asdict(row),
    }


def _failure(
    scenario: str,
    temporal_steps: int,
    spatial_width: int,
    coordinate: int,
    trial: int,
    status: str,
    *,
    reason: str,
    stdout: str = "",
    stderr: str = "",
    returncode: int | None = None,
) -> TrialRecord:
    return {
        "scenario": scenario,
        "temporal_steps": temporal_steps,
        "spatial_width": spatial_width,
        "coordinate": coordinate,
        "trial": trial,
        "status": status,
        "failure_reason": reason,
        "stdout": stdout,
        "stderr": stderr,
        "returncode": returncode,
    }


def _json_object(value: object) -> TypeGuard[dict[str, object]]:
    if type(value) is not dict:
        return False
    candidate = cast(dict[object, object], value)
    return all(type(key) is str for key in candidate)


def _required_text(value: Mapping[str, object], name: str) -> str:
    item = value.get(name)
    if type(item) is not str:
        raise ValueError(f"{name} must be text")
    return item


def _required_counter(value: Mapping[str, object], name: str) -> int:
    item = value.get(name)
    if type(item) is not int or item < 0:
        raise ValueError(f"{name} must be a nonnegative exact integer")
    return item


def _optional_counter(value: Mapping[str, object], name: str) -> int | None:
    item = value.get(name)
    if item is None:
        return None
    if type(item) is not int or item < 0:
        raise ValueError(f"{name} must be a nonnegative exact integer or null")
    return item


def _required_seconds(value: Mapping[str, object], name: str) -> float:
    item = value.get(name)
    if type(item) is int:
        try:
            seconds = float(item)
        except OverflowError as error:
            raise ValueError(f"{name} must be a finite nonnegative number") from error
    elif type(item) is float:
        seconds = item
    else:
        raise ValueError(f"{name} must be a finite nonnegative number")
    if not math.isfinite(seconds) or seconds < 0:
        raise ValueError(f"{name} must be a finite nonnegative number")
    return seconds


def parse_causal_growth_row(value: object) -> CausalGrowthRow | None:
    if not _json_object(value):
        return None
    expected = {item.name for item in fields(CausalGrowthRow)}
    if set(value) != expected:
        return None
    try:
        return CausalGrowthRow(
            scenario=_required_text(value, "scenario"),
            temporal_steps=_required_counter(value, "temporal_steps"),
            spatial_width=_required_counter(value, "spatial_width"),
            coordinate=_required_counter(value, "coordinate"),
            temporal_exponent=_required_counter(value, "temporal_exponent"),
            spatial_exponent=_required_counter(value, "spatial_exponent"),
            action_physical_ticks=_required_counter(value, "action_physical_ticks"),
            digit=_required_counter(value, "digit"),
            setup_seconds=_required_seconds(value, "setup_seconds"),
            observation_seconds=_required_seconds(value, "observation_seconds"),
            diagnostics_seconds=_required_seconds(value, "diagnostics_seconds"),
            cold_seconds=_required_seconds(value, "cold_seconds"),
            causal_accounting_version=_required_counter(
                value, "causal_accounting_version"
            ),
            causal_frames=_required_counter(value, "causal_frames"),
            task_memo_evaluations=_required_counter(value, "task_memo_evaluations"),
            task_memo_hits=_required_counter(value, "task_memo_hits"),
            primitive_emits=_required_counter(value, "primitive_emits"),
            finite_pair_transfers=_required_counter(value, "finite_pair_transfers"),
            finite_transfer_parent_observations=_required_counter(
                value, "finite_transfer_parent_observations"
            ),
            result_evaluations=_required_counter(value, "result_evaluations"),
            result_hits=_required_counter(value, "result_hits"),
            midpoint_reuse=_required_counter(value, "midpoint_reuse"),
            demand_descents=_required_counter(value, "demand_descents"),
            workspace_peak_slots=_required_counter(value, "workspace_peak_slots"),
            boundary_output_requests=_optional_counter(
                value, "boundary_output_requests"
            ),
            boundary_output_hits=_optional_counter(value, "boundary_output_hits"),
            boundary_output_evaluations=_required_counter(
                value, "boundary_output_evaluations"
            ),
            boundary_output_completions=_required_counter(
                value, "boundary_output_completions"
            ),
            boundary_output_failures=_optional_counter(
                value, "boundary_output_failures"
            ),
            boundary_requested_extent=_required_counter(
                value, "boundary_requested_extent"
            ),
            boundary_cached_extent=_required_counter(value, "boundary_cached_extent"),
            boundary_output_piece_normalizations=_required_counter(
                value, "boundary_output_piece_normalizations"
            ),
            spatial_buffer_allocations=_required_counter(
                value, "spatial_buffer_allocations"
            ),
            spatial_buffer_allocated_bytes=_required_counter(
                value, "spatial_buffer_allocated_bytes"
            ),
            spatial_buffer_appends=_required_counter(value, "spatial_buffer_appends"),
            spatial_buffer_reversal_visits=_required_counter(
                value, "spatial_buffer_reversal_visits"
            ),
            spatial_buffer_live_slots=_required_counter(
                value, "spatial_buffer_live_slots"
            ),
            spatial_buffer_live_bytes=_required_counter(
                value, "spatial_buffer_live_bytes"
            ),
            spatial_buffer_peak_slots=_required_counter(
                value, "spatial_buffer_peak_slots"
            ),
            spatial_buffer_peak_bytes=_required_counter(
                value, "spatial_buffer_peak_bytes"
            ),
            boundary_transfer_requests=_required_counter(
                value, "boundary_transfer_requests"
            ),
            boundary_transfer_frames=_required_counter(
                value, "boundary_transfer_frames"
            ),
            boundary_transfer_parent_observations=_required_counter(
                value, "boundary_transfer_parent_observations"
            ),
            boundary_transfer_descents=_required_counter(
                value, "boundary_transfer_descents"
            ),
            boundary_transfer_workspace_peak=_required_counter(
                value, "boundary_transfer_workspace_peak"
            ),
            directed_transfer_requests=_required_counter(
                value, "directed_transfer_requests"
            ),
            directed_transfer_early_hits=_required_counter(
                value, "directed_transfer_early_hits"
            ),
            directed_transfer_publication_requests=_required_counter(
                value, "directed_transfer_publication_requests"
            ),
            directed_transfer_publications=_required_counter(
                value, "directed_transfer_publications"
            ),
            directed_transfer_late_duplicates=_required_counter(
                value, "directed_transfer_late_duplicates"
            ),
            directed_transfer_leaf_evaluations=_required_counter(
                value, "directed_transfer_leaf_evaluations"
            ),
            directed_transfer_parent_evaluations=_required_counter(
                value, "directed_transfer_parent_evaluations"
            ),
            directed_transfer_workspace_peak=_required_counter(
                value, "directed_transfer_workspace_peak"
            ),
            causal_frame_publications=_required_counter(
                value, "causal_frame_publications"
            ),
            causal_frame_payload_reference_publications=_required_counter(
                value, "causal_frame_payload_reference_publications"
            ),
            causal_frame_peak_slots=_required_counter(value, "causal_frame_peak_slots"),
            completed_result_port_validation_requests=_required_counter(
                value, "completed_result_port_validation_requests"
            ),
            completed_result_port_validation_visits=_required_counter(
                value, "completed_result_port_validation_visits"
            ),
            directed_transfer_validation_requests=_required_counter(
                value, "directed_transfer_validation_requests"
            ),
            directed_transfer_validation_visits=_required_counter(
                value, "directed_transfer_validation_visits"
            ),
            action_nodes=_required_counter(value, "action_nodes"),
            action_composition_entries=_required_counter(
                value, "action_composition_entries"
            ),
            completed_result_entries=_required_counter(
                value, "completed_result_entries"
            ),
            directed_transfer_entries=_required_counter(
                value, "directed_transfer_entries"
            ),
            causal_interface_entries=_required_counter(
                value, "causal_interface_entries"
            ),
            powered_interface_entries=_required_counter(
                value, "powered_interface_entries"
            ),
            fused_interface_entries=_required_counter(value, "fused_interface_entries"),
            spatial_interface_entries=_required_counter(
                value, "spatial_interface_entries"
            ),
            other_result_memo_entries=_required_counter(
                value, "other_result_memo_entries"
            ),
            canonical_tile_nodes=_required_counter(value, "canonical_tile_nodes"),
            retained_entries=_required_counter(value, "retained_entries"),
            retained_nodes=_required_counter(value, "retained_nodes"),
            peak_entries=_required_counter(value, "peak_entries"),
            peak_nodes=_required_counter(value, "peak_nodes"),
            semantic_contract_classes=_required_counter(
                value, "semantic_contract_classes"
            ),
            temporal_edge_classes=_required_counter(value, "temporal_edge_classes"),
            retained_spatial_interval_bindings=_required_counter(
                value, "retained_spatial_interval_bindings"
            ),
            retained_spatial_interval_union_cells=_required_counter(
                value, "retained_spatial_interval_union_cells"
            ),
            sequential_generation_advances=_required_counter(
                value, "sequential_generation_advances"
            ),
            whole_word_sweeps=_required_counter(value, "whole_word_sweeps"),
            whole_word_symbol_visits=_required_counter(
                value, "whole_word_symbol_visits"
            ),
            proof_machine_applications=_required_counter(
                value, "proof_machine_applications"
            ),
            future_behavior_requests=_optional_counter(
                value, "future_behavior_requests"
            ),
            future_behavior_binding_requests=_optional_counter(
                value, "future_behavior_binding_requests"
            ),
            future_behavior_binding_early_hits=_optional_counter(
                value, "future_behavior_binding_early_hits"
            ),
            future_behavior_classification_evaluations=_optional_counter(
                value, "future_behavior_classification_evaluations"
            ),
            future_behavior_refinement_observation_checks=_optional_counter(
                value, "future_behavior_refinement_observation_checks"
            ),
            future_behavior_refinement_successor_checks=_optional_counter(
                value, "future_behavior_refinement_successor_checks"
            ),
            behavior_classification_summary_checks=_optional_counter(
                value, "behavior_classification_summary_checks"
            ),
            behavior_classification_port_checks=_optional_counter(
                value, "behavior_classification_port_checks"
            ),
            behavior_point_observations=_optional_counter(
                value, "behavior_point_observations"
            ),
            behavior_width_observations=_optional_counter(
                value, "behavior_width_observations"
            ),
            exact_causal_fallback_requests=_optional_counter(
                value, "exact_causal_fallback_requests"
            ),
            tile_region_application_validation_visits=_optional_counter(
                value, "tile_region_application_validation_visits"
            ),
            causal_extent_discharged_by_behavior=_optional_counter(
                value, "causal_extent_discharged_by_behavior"
            ),
        )
    except ValueError:
        return None


def _command(
    scenario: str, temporal_steps: int, spatial_width: int, coordinate: int
) -> list[str]:
    return [
        sys.executable,
        "-m",
        "devtools.benchmarks.causal_tile_growth_runner",
        "--worker",
        "--scenario",
        scenario,
        "--temporal-steps",
        str(temporal_steps),
        "--spatial-width",
        str(spatial_width),
        "--coordinate",
        str(coordinate),
    ]


def run_causal_growth_trial(
    request: tuple[str, int, int, int],
    trial: int,
    source: GitSource,
) -> TrialRecord:
    _scenario, _temporal_steps, _spatial_width, _coordinate = request
    command = _command(*request)
    process_started = perf_counter()
    with tempfile.TemporaryDirectory(prefix="causal-growth-worker-") as directory:
        output = Path(directory) / "worker.log"
        guard = run_guarded(
            tuple(command),
            output=output,
            cwd=ROOT,
            timeout=PYTHON_COMMAND_SECONDS,
            memory_bytes=MEMORY_LIMIT_BYTES,
        )
        worker_output = output.read_text()
    if guard.outcome == "timeout":
        failure = _failure(
            *request,
            trial,
            "timed_out",
            reason="worker exhausted the shared command deadline",
            stdout=worker_output,
        )
        failure["process_wall_seconds"] = perf_counter() - process_started
        return failure
    if guard.outcome != "completed":
        failure = _failure(
            *request,
            trial,
            "failed",
            reason=f"worker guard stopped execution: {guard.outcome}",
            stdout=worker_output,
            returncode=guard.child_returncode,
        )
        failure["process_wall_seconds"] = perf_counter() - process_started
        return failure
    if guard.samples <= 0 or guard.sampled_peak_bytes is None:
        failure = _failure(
            *request,
            trial,
            "failed",
            reason="worker guard produced no memory samples",
            stdout=worker_output,
            returncode=guard.child_returncode,
        )
        failure["process_wall_seconds"] = perf_counter() - process_started
        return failure
    process_wall_seconds = perf_counter() - process_started
    if guard.child_returncode:
        failure = _failure(
            *request,
            trial,
            "failed",
            reason="worker exited unsuccessfully",
            stdout=worker_output,
            returncode=guard.child_returncode,
        )
        failure["process_wall_seconds"] = process_wall_seconds
        return failure
    try:
        parsed = json.loads(worker_output)
    except (json.JSONDecodeError, TypeError) as error:
        failure = _failure(
            *request,
            trial,
            "failed",
            reason=f"invalid worker JSON: {error}",
            stdout=worker_output,
            returncode=guard.child_returncode,
        )
        failure["process_wall_seconds"] = process_wall_seconds
        return failure
    if not _json_object(parsed):
        failure = _failure(
            *request, trial, "failed", reason="worker returned another record"
        )
        failure["process_wall_seconds"] = process_wall_seconds
        return failure
    identity = (
        parsed.get("scenario"),
        parsed.get("temporal_steps"),
        parsed.get("spatial_width"),
        parsed.get("coordinate"),
    )
    if identity != request:
        failure = _failure(
            *request, trial, "failed", reason="worker identified another sample"
        )
        failure["process_wall_seconds"] = process_wall_seconds
        return failure
    if (
        parsed.get("git_source_before") != source.as_dict()
        or parsed.get("git_source_after") != source.as_dict()
    ):
        failure = _failure(
            *request, trial, "failed", reason="worker Git state differed from parent"
        )
        failure["process_wall_seconds"] = process_wall_seconds
        return failure
    row = parse_causal_growth_row(parsed.get("row"))
    if (
        row is None
        or (
            row.scenario,
            row.temporal_steps,
            row.spatial_width,
            row.coordinate,
        )
        != request
    ):
        failure = _failure(
            *request, trial, "failed", reason="worker returned an invalid row"
        )
        failure["process_wall_seconds"] = process_wall_seconds
        return failure
    return {
        "scenario": request[0],
        "temporal_steps": request[1],
        "spatial_width": request[2],
        "coordinate": request[3],
        "trial": trial,
        "status": "passed",
        "git_source_before": source.as_dict(),
        "git_source_after": source.as_dict(),
        "row": asdict(row),
        "process_wall_seconds": process_wall_seconds,
        "sampled_peak_bytes": guard.sampled_peak_bytes,
        "memory_measurement": guard.memory_measurement,
        "memory_samples": guard.samples,
    }


def aggregate_causal_growth_trials(
    request: tuple[str, int, int, int],
    trials: Sequence[Mapping[str, object]],
    expected_trials: int,
) -> tuple[CausalGrowthRow | None, SampleReport]:
    parsed_rows = [
        parse_causal_growth_row(item.get("row"))
        for item in trials
        if item.get("status") == "passed"
    ]
    rows = [row for row in parsed_rows if row is not None]
    complete = len(trials) == expected_trials and len(rows) == expected_trials
    stable = False
    representative: CausalGrowthRow | None = None
    empty_timing: dict[str, float | None] = {
        "minimum": None,
        "median": None,
        "maximum": None,
        "spread": None,
    }
    timing: dict[str, dict[str, float | None]] = {
        name: dict(empty_timing) for name in _TIMING_FIELDS
    }
    process_timing: dict[str, float | None] = dict(empty_timing)
    if complete:
        without_time = [
            replace(
                row,
                setup_seconds=0.0,
                observation_seconds=0.0,
                diagnostics_seconds=0.0,
                cold_seconds=0.0,
            )
            for row in rows
        ]
        stable = all(row == without_time[0] for row in without_time[1:])
        for name in _TIMING_FIELDS:
            seconds = [float(getattr(row, name)) for row in rows]
            timing[name] = {
                "minimum": min(seconds),
                "median": statistics.median(seconds),
                "maximum": max(seconds),
                "spread": max(seconds) - min(seconds),
            }
        process_seconds = [
            _required_seconds(item, "process_wall_seconds") for item in trials
        ]
        process_timing = {
            "minimum": min(process_seconds),
            "median": statistics.median(process_seconds),
            "maximum": max(process_seconds),
            "spread": max(process_seconds) - min(process_seconds),
        }
        if stable:
            representative = replace(
                rows[0],
                setup_seconds=statistics.median([row.setup_seconds for row in rows]),
                observation_seconds=statistics.median(
                    [row.observation_seconds for row in rows]
                ),
                diagnostics_seconds=statistics.median(
                    [row.diagnostics_seconds for row in rows]
                ),
                cold_seconds=statistics.median([row.cold_seconds for row in rows]),
            )
    blockers: list[str] = []
    if not complete:
        blockers.append("fresh_process_trials_incomplete")
    elif not stable:
        blockers.append("non_timing_counters_changed_between_cold_trials")
    return representative, {
        "request": {
            "scenario": request[0],
            "temporal_steps": request[1],
            "spatial_width": request[2],
            "coordinate": request[3],
        },
        "expected_trials": expected_trials,
        "completed_trials": len(rows),
        "timing_seconds": timing,
        "process_wall_seconds": process_timing,
        "release_blockers": blockers,
        "status": "MEASURED" if not blockers else "RED",
        "trials": trials,
    }


def _requests(
    horizons: tuple[int, ...], spatial_widths: tuple[int, ...], fixed_width: int
) -> dict[str, tuple[tuple[str, int, int, int], ...]]:
    fixed_depth = horizons[0]
    return {
        "fixed_width_temporal": tuple(
            ("fixed-width", horizon, fixed_width, min(2, fixed_width - 1))
            for horizon in horizons
        ),
        "fixed_depth_spatial": tuple(
            ("fixed-depth", fixed_depth, width, min(2, width - 1))
            for width in spatial_widths
        ),
        "growing_196": tuple(
            (
                "growing-196",
                horizon,
                power_of_two_at_least(3 + horizon),
                0,
            )
            for horizon in horizons
        ),
    }


def _flat_requests(
    groups: dict[str, tuple[tuple[str, int, int, int], ...]],
) -> tuple[tuple[str, int, int, int], ...]:
    return tuple(request for values in groups.values() for request in values)


def _request_record(request: tuple[str, int, int, int]) -> RequestRecord:
    return {
        "scenario": request[0],
        "temporal_steps": request[1],
        "spatial_width": request[2],
        "coordinate": request[3],
    }


def build_causal_growth_manifest(
    horizons: tuple[int, ...],
    spatial_widths: tuple[int, ...],
    fixed_width: int,
    trials: int,
) -> ProbeManifest:
    groups = _requests(horizons, spatial_widths, fixed_width)
    return {
        "horizons": list(horizons),
        "spatial_widths": list(spatial_widths),
        "fixed_width": fixed_width,
        "fresh_process_trials_per_sample": trials,
        "invocation_limit_seconds": INVOCATION_LIMIT_SECONDS,
        "memory_limit_bytes": MEMORY_LIMIT_BYTES,
        "requests": [_request_record(request) for request in _flat_requests(groups)],
    }


def run_fresh_process_probe(
    *,
    horizons: tuple[int, ...] = HORIZONS,
    spatial_widths: tuple[int, ...] = HORIZONS,
    fixed_width: int = 16,
    trials: int = TRIALS,
) -> CausalProbeReport:
    if type(trials) is not int or trials < 1:
        raise ValueError("fresh causal probe requires a positive exact trial count")
    if not horizons or not spatial_widths or fixed_width < 3:
        raise ValueError("fresh causal probe requires nonempty source-containing axes")
    axes = (*horizons, *spatial_widths, fixed_width)
    if any(
        type(value) is not int or value < 1 or value & (value - 1) for value in axes
    ):
        raise ValueError("fresh causal probe axes require exact powers of two")
    source = git_source(ROOT)
    samples: dict[str, list[SampleReport]] = {}
    representatives: dict[str, list[CausalGrowthRow]] = {}
    request_sets = _requests(horizons, spatial_widths, fixed_width)
    for label, requests in request_sets.items():
        samples[label] = []
        representatives[label] = []
        for request in requests:
            trial_rows = [
                run_causal_growth_trial(request, trial, source)
                for trial in range(trials)
            ]
            representative, sample = aggregate_causal_growth_trials(
                request, trial_rows, trials
            )
            samples[label].append(sample)
            if representative is not None:
                representatives[label].append(representative)
    after = git_source(ROOT)
    reports = {
        "fixed_width_temporal": series_report(
            representatives["fixed_width_temporal"],
            horizons,
            axis="temporal_steps",
        ),
        "fixed_depth_spatial": series_report(
            representatives["fixed_depth_spatial"],
            spatial_widths,
            axis="spatial_width",
        ),
        "growing_196": series_report(
            representatives["growing_196"],
            horizons,
            axis="temporal_steps",
        ),
    }
    revision_unchanged = same_git_revision(source, after)
    collection_complete = all(
        sample["status"] == "MEASURED" for group in samples.values() for sample in group
    )
    diagnostic_accepted = (
        revision_unchanged
        and collection_complete
        and all(report["status"] == "MEASURED_PASS" for report in reports.values())
    )
    required_groups = _requests(HORIZONS, HORIZONS, RELEASE_FIXED_WIDTH)
    required_requests = _flat_requests(required_groups)
    requested_requests = _flat_requests(request_sets)
    observed_requests = tuple(
        (
            sample["request"]["scenario"],
            sample["request"]["temporal_steps"],
            sample["request"]["spatial_width"],
            sample["request"]["coordinate"],
        )
        for group in samples.values()
        for sample in group
        if sample["status"] == "MEASURED"
    )
    release_manifest_complete = (
        horizons == HORIZONS
        and spatial_widths == HORIZONS
        and fixed_width == RELEASE_FIXED_WIDTH
        and trials == TRIALS
        and requested_requests == required_requests
    )
    release_blockers: list[str] = []
    if not release_manifest_complete:
        release_blockers.append("release_manifest_incomplete")
    if not revision_unchanged:
        release_blockers.append("git_revision_changed_during_measurement")
    if not collection_complete:
        release_blockers.append("measurement_collection_incomplete")
    if any(report["status"] != "MEASURED_PASS" for report in reports.values()):
        release_blockers.append("growth_envelope_violation_or_missing_evidence")
    release_measurement_pass = release_manifest_complete and diagnostic_accepted
    observed = set(observed_requests)
    return {
        "metrics_schema_version": METRICS_SCHEMA_VERSION,
        "git_source_before": source.as_dict(),
        "git_source_after": after.as_dict(),
        "git_revision_unchanged": revision_unchanged,
        "evidence_mode": os.environ.get("NUMBER_COMPILER_EVIDENCE_MODE", "development"),
        "cacheable": False,
        "reusable": False,
        "fresh_process_trials_per_sample": trials,
        "invocation_limit_seconds": INVOCATION_LIMIT_SECONDS,
        "memory_limit_bytes": MEMORY_LIMIT_BYTES,
        "timed_environment": {
            "python_executable": sys.executable,
            "python_version": sys.version,
            "platform": sys.platform,
        },
        "default_release_horizons": list(HORIZONS),
        "release_manifest_complete": release_manifest_complete,
        "requested_manifest": build_causal_growth_manifest(
            horizons, spatial_widths, fixed_width, trials
        ),
        "required_manifest": build_causal_growth_manifest(
            HORIZONS,
            HORIZONS,
            RELEASE_FIXED_WIDTH,
            TRIALS,
        ),
        "observed_manifest": {
            "requests": [_request_record(request) for request in observed_requests]
        },
        "missing_manifest": {
            "requests": [
                _request_record(request)
                for request in required_requests
                if request not in observed
            ]
        },
        "collection_complete": collection_complete,
        "logarithmic_execution_claim": False,
        "coordinate_policy": (
            "scaling series observes coordinate zero; worker mode accepts explicit "
            "midpoint or last-active diagnostic coordinates"
        ),
        "diagnostic_status": "MEASURED_PASS" if diagnostic_accepted else "RED",
        "status_scope": (
            "causal growth evidence only; full-suite, static checks, and production "
            "cutover require independent release evidence"
        ),
        "release_complete": False,
        "release_blockers": release_blockers,
        "status": "MEASURED_PASS" if release_measurement_pass else "RED",
        "samples": samples,
        "series": reports,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--worker", action="store_true")
    parser.add_argument(
        "--scenario", choices=("fixed-width", "fixed-depth", "growing-196")
    )
    parser.add_argument("--temporal-steps", type=int)
    parser.add_argument("--spatial-width", type=int)
    parser.add_argument("--coordinate", type=int)
    args = parser.parse_args(argv)
    if args.worker:
        values = (
            args.scenario,
            args.temporal_steps,
            args.spatial_width,
            args.coordinate,
        )
        if type(values[0]) is not str or any(
            type(value) is not int for value in values[1:]
        ):
            parser.error("worker requires one complete causal request")
        print(json.dumps(worker(*values)))
        return 0
    if args.output is None:
        from devtools.paths import report_output

        args.output = report_output(
            "devtools.benchmarks.causal_tile_growth_runner", "report.json"
        )
    if args.output.exists() or args.output.is_symlink():
        parser.error("historical results must not be overwritten")
    result = run_fresh_process_probe()
    with args.output.open("x") as stream:
        json.dump(result, stream, indent=2)
        stream.write("\n")
    return 0 if result["status"] == "MEASURED_PASS" else 1


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))

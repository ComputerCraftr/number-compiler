"""Fresh-process orchestration for causal tile growth evidence."""

from __future__ import annotations

import argparse
import json
import math
import os
import statistics
import subprocess
import sys
from collections.abc import Mapping, Sequence
from dataclasses import asdict, fields, replace
from pathlib import Path
from time import perf_counter
from typing import Required, TypedDict, cast

from devtools.benchmarks.causal_tile_growth_probe import (
    CausalGrowthRow,
    CausalSeriesReport,
    _power_of_two_at_least,
    cold_row,
    series_report,
)
from devtools.checks.test_run_evidence import source_fingerprint
from devtools.paths import repository_root


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
    source_before: str
    source_after: str
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
    worker_watchdog_seconds: int


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
    source_fingerprint: str
    source_unchanged: bool
    fresh_process_trials_per_sample: int
    worker_watchdog_seconds: int
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
WORKER_TIMEOUT_SECONDS = 35
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
    fingerprint = source_fingerprint(ROOT)
    row, _ledger = cold_row(
        scenario, temporal_steps, spatial_width, coordinate=coordinate
    )
    return {
        "scenario": scenario,
        "temporal_steps": temporal_steps,
        "spatial_width": spatial_width,
        "coordinate": coordinate,
        "pid": os.getpid(),
        "source_before": fingerprint,
        "source_after": source_fingerprint(ROOT),
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


def _text(value: str | bytes | None) -> str:
    if value is None:
        return ""
    return value.decode(errors="replace") if isinstance(value, bytes) else value


def _parse_row(value: object) -> CausalGrowthRow | None:
    if type(value) is not dict:
        return None
    expected = {item.name for item in fields(CausalGrowthRow)}
    if set(value) != expected:
        return None
    try:
        row = CausalGrowthRow(**value)
    except (TypeError, ValueError):
        return None
    if type(row.scenario) is not str or any(
        type(getattr(row, name)) not in (int, float)
        or not math.isfinite(getattr(row, name))
        or getattr(row, name) < 0
        for name in _TIMING_FIELDS
    ):
        return None
    for item in fields(CausalGrowthRow):
        if item.name == "scenario" or item.name in _TIMING_FIELDS:
            continue
        field_value = getattr(row, item.name)
        if field_value is not None and type(field_value) is not int:
            return None
        if type(field_value) is int and field_value < 0:
            return None
    return row


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


def _one_trial(
    request: tuple[str, int, int, int],
    trial: int,
    fingerprint: str,
    timeout: int,
) -> TrialRecord:
    _scenario, _temporal_steps, _spatial_width, _coordinate = request
    command = _command(*request)
    environment = dict(os.environ)
    try:
        process_started = perf_counter()
        completed = subprocess.run(
            command,
            cwd=ROOT,
            env=environment,
            capture_output=True,
            text=True,
            check=False,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as error:
        failure = _failure(
            *request,
            trial,
            "timed_out",
            reason=f"worker exceeded {timeout}s watchdog",
            stdout=_text(error.stdout),
            stderr=_text(error.stderr),
        )
        failure["process_wall_seconds"] = perf_counter() - process_started
        return failure
    process_wall_seconds = perf_counter() - process_started
    if completed.returncode:
        failure = _failure(
            *request,
            trial,
            "failed",
            reason="worker exited unsuccessfully",
            stdout=completed.stdout,
            stderr=completed.stderr,
            returncode=completed.returncode,
        )
        failure["process_wall_seconds"] = process_wall_seconds
        return failure
    try:
        parsed = json.loads(completed.stdout)
    except (json.JSONDecodeError, TypeError) as error:
        failure = _failure(
            *request,
            trial,
            "failed",
            reason=f"invalid worker JSON: {error}",
            stdout=completed.stdout,
            stderr=completed.stderr,
            returncode=completed.returncode,
        )
        failure["process_wall_seconds"] = process_wall_seconds
        return failure
    if type(parsed) is not dict:
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
        parsed.get("source_before") != fingerprint
        or parsed.get("source_after") != fingerprint
    ):
        failure = _failure(
            *request, trial, "failed", reason="worker source fingerprint changed"
        )
        failure["process_wall_seconds"] = process_wall_seconds
        return failure
    row = _parse_row(parsed.get("row"))
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
    parsed["trial"] = trial
    parsed["status"] = "passed"
    parsed["process_wall_seconds"] = process_wall_seconds
    return cast("TrialRecord", parsed)


def _aggregate(
    request: tuple[str, int, int, int],
    trials: Sequence[Mapping[str, object]],
    expected_trials: int,
) -> tuple[CausalGrowthRow | None, SampleReport]:
    parsed_rows = [
        _parse_row(item.get("row")) for item in trials if item.get("status") == "passed"
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
    process_timing = dict(empty_timing)
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
            float(cast("float", item["process_wall_seconds"])) for item in trials
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
                setup_seconds=float(cast("float", timing["setup_seconds"]["median"])),
                observation_seconds=float(
                    cast("float", timing["observation_seconds"]["median"])
                ),
                diagnostics_seconds=float(
                    cast("float", timing["diagnostics_seconds"]["median"])
                ),
                cold_seconds=float(cast("float", timing["cold_seconds"]["median"])),
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
                _power_of_two_at_least(3 + horizon),
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


def _manifest(
    horizons: tuple[int, ...],
    spatial_widths: tuple[int, ...],
    fixed_width: int,
    trials: int,
    timeout: int,
) -> ProbeManifest:
    groups = _requests(horizons, spatial_widths, fixed_width)
    return {
        "horizons": list(horizons),
        "spatial_widths": list(spatial_widths),
        "fixed_width": fixed_width,
        "fresh_process_trials_per_sample": trials,
        "worker_watchdog_seconds": timeout,
        "requests": [_request_record(request) for request in _flat_requests(groups)],
    }


def run_fresh_process_probe(
    *,
    horizons: tuple[int, ...] = HORIZONS,
    spatial_widths: tuple[int, ...] = HORIZONS,
    fixed_width: int = 16,
    trials: int = TRIALS,
    timeout: int = WORKER_TIMEOUT_SECONDS,
) -> CausalProbeReport:
    if type(trials) is not int or trials < 1 or type(timeout) is not int or timeout < 1:
        raise ValueError("fresh causal probe requires positive exact trial limits")
    if not horizons or not spatial_widths or fixed_width < 3:
        raise ValueError("fresh causal probe requires nonempty source-containing axes")
    axes = (*horizons, *spatial_widths, fixed_width)
    if any(
        type(value) is not int or value < 1 or value & (value - 1) for value in axes
    ):
        raise ValueError("fresh causal probe axes require exact powers of two")
    fingerprint = source_fingerprint(ROOT)
    samples: dict[str, list[SampleReport]] = {}
    representatives: dict[str, list[CausalGrowthRow]] = {}
    request_sets = _requests(horizons, spatial_widths, fixed_width)
    for label, requests in request_sets.items():
        samples[label] = []
        representatives[label] = []
        for request in requests:
            trial_rows = [
                _one_trial(request, trial, fingerprint, timeout)
                for trial in range(trials)
            ]
            representative, sample = _aggregate(request, trial_rows, trials)
            samples[label].append(sample)
            if representative is not None:
                representatives[label].append(representative)
    after = source_fingerprint(ROOT)
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
    source_unchanged = after == fingerprint
    collection_complete = all(
        sample["status"] == "MEASURED" for group in samples.values() for sample in group
    )
    diagnostic_accepted = (
        source_unchanged
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
        and timeout == WORKER_TIMEOUT_SECONDS
        and requested_requests == required_requests
    )
    release_blockers: list[str] = []
    if not release_manifest_complete:
        release_blockers.append("release_manifest_incomplete")
    if not source_unchanged:
        release_blockers.append("source_changed_during_measurement")
    if not collection_complete:
        release_blockers.append("measurement_collection_incomplete")
    if any(report["status"] != "MEASURED_PASS" for report in reports.values()):
        release_blockers.append("growth_envelope_violation_or_missing_evidence")
    release_measurement_pass = release_manifest_complete and diagnostic_accepted
    observed = set(observed_requests)
    return {
        "metrics_schema_version": 6,
        "source_fingerprint": fingerprint,
        "source_unchanged": source_unchanged,
        "fresh_process_trials_per_sample": trials,
        "worker_watchdog_seconds": timeout,
        "timed_environment": {
            "python_executable": sys.executable,
            "python_version": sys.version,
            "platform": sys.platform,
        },
        "default_release_horizons": list(HORIZONS),
        "release_manifest_complete": release_manifest_complete,
        "requested_manifest": _manifest(
            horizons, spatial_widths, fixed_width, trials, timeout
        ),
        "required_manifest": _manifest(
            HORIZONS,
            HORIZONS,
            RELEASE_FIXED_WIDTH,
            TRIALS,
            WORKER_TIMEOUT_SECONDS,
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
        parser.error("parent runner requires --output")
    if args.output.exists() or args.output.is_symlink():
        parser.error("historical results must not be overwritten")
    result = run_fresh_process_probe()
    with args.output.open("x") as stream:
        json.dump(result, stream, indent=2)
        stream.write("\n")
    return 0 if result["status"] == "MEASURED_PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())

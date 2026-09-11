"""Fresh causal evidence preserves timeout and fingerprint failures."""

from __future__ import annotations

import json
import subprocess
from dataclasses import asdict, fields, replace
from subprocess import CompletedProcess, TimeoutExpired
from typing import Never

import pytest

import devtools.benchmarks.causal_tile_growth_runner as runner
from devtools.benchmarks.causal_tile_growth_probe import CausalGrowthRow


def _row() -> CausalGrowthRow:
    values: dict[str, object] = {
        item.name: None if "boundary_output" in item.name else 0
        for item in fields(CausalGrowthRow)
    }
    values.update(
        scenario="fixed-width",
        temporal_steps=4,
        spatial_width=4,
        coordinate=1,
        temporal_exponent=2,
        spatial_exponent=2,
        action_physical_ticks=4,
        setup_seconds=0.05,
        observation_seconds=0.15,
        diagnostics_seconds=0.01,
        cold_seconds=0.2,
        causal_accounting_version=1,
        boundary_output_requests=0,
        boundary_output_hits=0,
        boundary_output_evaluations=0,
        boundary_output_completions=0,
        boundary_output_failures=0,
        boundary_output_piece_normalizations=0,
    )
    return CausalGrowthRow(**values)  # type: ignore[arg-type]


def test_release_runner_keeps_five_trials_and_full_horizon_manifest() -> None:
    assert runner.TRIALS == 5
    assert runner.HORIZONS == (16, 32, 64, 128, 256, 512, 1024)
    assert runner.WORKER_TIMEOUT_SECONDS == 35


def test_worker_timeout_remains_missing_evidence(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(runner, "source_fingerprint", lambda _root: "frozen")

    def timed_out(command: list[str], **kwargs: object) -> None:
        assert kwargs["timeout"] == 7
        raise TimeoutExpired(command, 7, output="partial", stderr="watchdog")

    monkeypatch.setattr(subprocess, "run", timed_out)
    result = runner.run_fresh_process_probe(
        horizons=(4, 8),
        spatial_widths=(4, 8),
        fixed_width=4,
        trials=1,
        timeout=7,
    )
    assert result["status"] == "RED"
    assert result["collection_complete"] is False
    assert all(
        sample["status"] == "RED"
        for group in result["samples"].values()
        for sample in group
    )
    assert all(
        report["measurements_complete"] is False for report in result["series"].values()
    )


def test_worker_fingerprint_is_checked_before_row_payload(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    payload = {
        "scenario": "fixed-width",
        "temporal_steps": 4,
        "spatial_width": 4,
        "coordinate": 1,
        "source_before": "changed",
        "source_after": "changed",
        "row": {"malformed": True},
    }
    monkeypatch.setattr(
        subprocess,
        "run",
        lambda *_args, **_kwargs: CompletedProcess([], 0, json.dumps(payload), ""),
    )

    def forbidden(_value: object) -> Never:
        raise AssertionError("row decoded before source identity was validated")

    monkeypatch.setattr(runner, "_parse_row", forbidden)
    result = runner._one_trial(("fixed-width", 4, 4, 1), 0, "frozen", 35)
    assert result["status"] == "failed"
    assert result["failure_reason"] == "worker source fingerprint changed"


def test_trial_aggregation_reports_median_spread_and_stable_counters() -> None:
    row = _row()
    trials = []
    for trial, seconds in enumerate((0.3, 0.1, 0.2)):
        trials.append(
            {
                "status": "passed",
                "row": asdict(replace(row, cold_seconds=seconds)),
                "trial": trial,
                "process_wall_seconds": seconds + 0.05,
            }
        )
    representative, report = runner._aggregate(("fixed-width", 4, 4, 1), trials, 3)
    assert representative is not None and representative.cold_seconds == 0.2
    assert report["status"] == "MEASURED"
    assert report["timing_seconds"]["cold_seconds"] == {
        "minimum": 0.1,
        "median": 0.2,
        "maximum": 0.3,
        "spread": 0.19999999999999998,
    }


def test_trial_counter_instability_is_not_collapsed_into_a_median() -> None:
    row = _row()
    trials = [
        {"status": "passed", "row": asdict(row), "process_wall_seconds": 0.3},
        {
            "status": "passed",
            "row": asdict(replace(row, causal_frames=row.causal_frames + 1)),
            "process_wall_seconds": 0.3,
        },
    ]
    representative, report = runner._aggregate(("fixed-width", 4, 4, 1), trials, 2)
    assert representative is None
    assert report["status"] == "RED"
    assert report["release_blockers"] == [
        "non_timing_counters_changed_between_cold_trials"
    ]


def test_worker_row_rejects_negative_counters_and_nonfinite_time() -> None:
    row = _row()
    assert runner._parse_row(asdict(replace(row, causal_frames=-1))) is None
    assert runner._parse_row(asdict(replace(row, cold_seconds=float("nan")))) is None


def test_passing_subset_remains_red_for_missing_release_manifest(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(runner, "source_fingerprint", lambda _root: "frozen")

    def passed(
        request: tuple[str, int, int, int],
        trial: int,
        fingerprint: str,
        timeout: object,
    ) -> runner.TrialRecord:
        scenario, temporal_steps, spatial_width, coordinate = request
        row = replace(
            _row(),
            scenario=scenario,
            temporal_steps=temporal_steps,
            spatial_width=spatial_width,
            coordinate=coordinate,
            temporal_exponent=temporal_steps.bit_length() - 1,
            spatial_exponent=spatial_width.bit_length() - 1,
            action_physical_ticks=(
                temporal_steps - 1 if scenario == "growing-196" else temporal_steps
            ),
        )
        return {
            "scenario": scenario,
            "temporal_steps": temporal_steps,
            "spatial_width": spatial_width,
            "coordinate": coordinate,
            "trial": trial,
            "source_before": fingerprint,
            "source_after": fingerprint,
            "row": asdict(row),
            "process_wall_seconds": 0.3,
            "status": "passed",
        }

    monkeypatch.setattr(runner, "_one_trial", passed)
    result = runner.run_fresh_process_probe(
        horizons=(4, 8),
        spatial_widths=(4, 8),
        fixed_width=4,
        trials=1,
        timeout=35,
    )
    assert result["diagnostic_status"] == "MEASURED_PASS"
    assert result["status"] == "RED"
    assert result["release_complete"] is False
    assert result["release_manifest_complete"] is False
    assert result["release_blockers"] == ["release_manifest_incomplete"]
    assert result["requested_manifest"]["horizons"] == [4, 8]
    assert result["required_manifest"]["horizons"] == list(runner.HORIZONS)
    assert result["missing_manifest"]["requests"]
    assert "causal growth evidence only" in result["status_scope"]


def test_exact_default_protocol_is_required_for_release_measurement() -> None:
    required = runner._manifest(
        runner.HORIZONS,
        runner.HORIZONS,
        runner.RELEASE_FIXED_WIDTH,
        runner.TRIALS,
        runner.WORKER_TIMEOUT_SECONDS,
    )
    assert required["fresh_process_trials_per_sample"] == 5
    assert required["worker_watchdog_seconds"] == 35
    assert len(required["requests"]) == 3 * len(runner.HORIZONS)

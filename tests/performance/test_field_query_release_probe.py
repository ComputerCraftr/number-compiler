"""Release evidence preserves failures and measures each resource population."""

from __future__ import annotations

import json
import subprocess
from subprocess import CompletedProcess, TimeoutExpired
from typing import NotRequired, TypedDict

import pytest

import devtools.benchmarks.field_query_release_probe as probe


def _metrics(scale: int) -> dict[str, int]:
    result = {field: scale for field in probe.ENVELOPE_FIELDS}
    result.update({field: 0 for field in probe.FORBIDDEN_EXECUTION_FIELDS})
    result.update({field: 1 for field in probe.ABSORPTION_FIELDS})
    result["powered_absorption_max_span"] = 1024
    return result


def _worker_row(family: str, horizon: int, scale: int) -> WorkerFixture:
    return {
        "family": family,
        "horizon": horizon,
        "source_before": "frozen",
        "source_after": "frozen",
        "audit_unchanged": True,
        "digit": 1,
        "repeat_digit": 1,
        "cold_seconds": 0.01,
        "metrics": _metrics(scale),
    }


def test_release_probe_covers_the_full_unchanged_watchdog_series() -> None:
    assert probe.HORIZONS == (16, 32, 64, 128, 256, 512, 1024)
    assert probe.WORKER_TIMEOUT_SECONDS == 35


def test_failed_and_timed_out_workers_remain_in_complete_collection(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(probe, "source_fingerprint", lambda _root: "frozen")
    calls = 0

    def fake_run(
        command: list[str], **kwargs: object
    ) -> subprocess.CompletedProcess[str]:
        nonlocal calls
        assert kwargs["timeout"] == 35
        family, horizon = command[-3], int(command[-1])
        calls += 1
        if calls == 1:
            raise TimeoutExpired(command, 35, output="partial", stderr="watchdog")
        if calls == 2:
            return CompletedProcess(command, 7, "", "failed")
        row = _worker_row(family, horizon, horizon)
        return CompletedProcess(command, 0, json.dumps(row), "")

    monkeypatch.setattr(subprocess, "run", fake_run)
    result = probe.run_probe()
    assert result["source_unchanged"] is True
    assert result["collection_complete"] is True
    assert result["measurement_series_complete"] is False
    assert result["status"] == "RED"
    assert result["release_complete"] is False
    assert "measurement-only" in result["status_scope"]
    assert len(result["rows"]) == 2 * len(probe.HORIZONS)
    assert result["rows"][0]["status"] == "timed_out"
    assert result["rows"][0]["stdout"] == "partial"
    assert result["rows"][1]["status"] == "failed"
    for family in result["families"].values():
        if family["series_complete"] is False:
            assert "measurement_series_incomplete" in family["release_blockers"]


def test_family_envelopes_reject_quadratic_work_without_hiding_other_units() -> None:
    horizons = (16, 32, 64, 128)
    rows = []
    for index, horizon in enumerate(horizons):
        metrics = _metrics(1 << index)
        metrics["total_internal_action_work"] = 4**index
        rows.append(
            {
                **_worker_row("reverse", horizon, 1),
                "status": "passed",
                "metrics": metrics,
            }
        )
    report = probe._family_report("reverse", rows, horizons)
    envelopes = report["measured_doubling_envelopes"]
    assert envelopes["total_internal_action_work"] is False
    assert envelopes["resource_ledger_nodes"] is True
    assert envelopes["resource_ledger_entries"] is True
    assert envelopes["new_canonical_field_images_published"] is True
    assert envelopes["canonical_tile_nodes"] is True
    assert envelopes["tile_execution_memo_entries"] is True
    assert envelopes["spatial_interface_composition_entries"] is True
    assert report["status"] == "RED"


def test_invalid_worker_json_is_retained_as_failed_sample(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(probe, "HORIZONS", (16,))
    monkeypatch.setattr(probe, "source_fingerprint", lambda _root: "frozen")
    monkeypatch.setattr(
        subprocess,
        "run",
        lambda command, **_kwargs: CompletedProcess(command, 0, "not-json", "trace"),
    )
    result = probe.run_probe()
    assert result["collection_complete"] is True
    assert result["measurement_series_complete"] is False
    assert all(row["status"] == "failed" for row in result["rows"])
    assert all(
        isinstance(row["failure_reason"], str)
        and "invalid worker JSON" in row["failure_reason"]
        for row in result["rows"]
    )


def test_parent_source_consistency_is_reported_separately_from_worker_claims(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(probe, "HORIZONS", (16, 32))
    monkeypatch.setattr(probe, "source_fingerprint", lambda _root: "frozen")

    def fake_run(
        command: list[str], **_kwargs: object
    ) -> subprocess.CompletedProcess[str]:
        family, horizon = command[-3], int(command[-1])
        row = _worker_row(family, horizon, horizon)
        row["source_after"] = "changed-in-worker"
        return CompletedProcess(command, 0, json.dumps(row), "")

    monkeypatch.setattr(subprocess, "run", fake_run)
    result = probe.run_probe()
    assert result["source_unchanged"] is True
    assert result["worker_sources_consistent"] is False
    assert result["measurement_series_complete"] is True
    assert result["status"] == "RED"


def test_malformed_metrics_are_retained_as_failure_instead_of_aborting(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(probe, "HORIZONS", (16,))
    monkeypatch.setattr(probe, "source_fingerprint", lambda _root: "frozen")

    def fake_run(
        command: list[str], **_kwargs: object
    ) -> subprocess.CompletedProcess[str]:
        family, horizon = command[-3], int(command[-1])
        row = _worker_row(family, horizon, horizon)
        row["metrics"] = {"total_internal_action_work": True}
        return CompletedProcess(command, 0, json.dumps(row), "")

    monkeypatch.setattr(subprocess, "run", fake_run)
    result = probe.run_probe()
    assert result["collection_complete"] is True
    assert result["measurement_series_complete"] is False
    assert all(row["status"] == "failed" for row in result["rows"])
    assert all(
        isinstance(row["failure_reason"], str)
        and "invalid metrics" in row["failure_reason"]
        for row in result["rows"]
    )


def test_forbidden_execution_work_blocks_otherwise_linear_measurements() -> None:
    horizons = (16, 32)
    rows = []
    for horizon in horizons:
        metrics = _metrics(horizon)
        metrics["higher_action_continuation_requests"] = 1
        rows.append(
            {
                **_worker_row("collatz", horizon, horizon),
                "status": "passed",
                "metrics": metrics,
            }
        )
    report = probe._family_report("collatz", rows, horizons)
    assert report["measured_doubling_envelopes"]["total_internal_action_work"] is True
    assert "higher_action_continuation_requests_observed" in report["release_blockers"]
    assert report["status"] == "RED"


def test_timeout_does_not_report_unobserved_cache_growth() -> None:
    horizons = (16, 32, 64, 128)
    rows = [
        {**_worker_row("reverse", horizon, horizon), "status": "passed"}
        for horizon in horizons[:-1]
    ]
    rows.append({"family": "reverse", "horizon": 128, "status": "timed_out"})
    report = probe._family_report("reverse", rows, horizons)
    assert report["status"] == "RED"
    assert report["release_blockers"] == ["measurement_series_incomplete"]
    assert report["observed_prefix_horizons"] == [16, 32, 64]
    assert all(
        value is None for value in report["measured_doubling_envelopes"].values()
    )
    assert all(report["observed_prefix_doubling_envelopes"].values())


def test_single_sample_cannot_establish_or_refute_doubling() -> None:
    report = probe._family_report(
        "reverse",
        [{**_worker_row("reverse", 16, 1), "status": "passed"}],
        (16,),
    )
    assert report["status"] == "RED"
    assert report["release_blockers"] == ["doubling_evidence_insufficient"]
    assert all(
        value is None for value in report["measured_doubling_envelopes"].values()
    )


def test_compiler_growth_and_source_tiles_do_not_prove_absorption() -> None:
    rows = []
    for horizon in (16, 32):
        row = _worker_row("reverse", horizon, horizon)
        row["status"] = "passed"
        row["metrics"].update({field: 0 for field in probe.ABSORPTION_FIELDS})
        rows.append(row)
    report = probe._family_report("reverse", rows, (16, 32))
    assert all(report["measured_doubling_envelopes"].values())
    assert report["release_blockers"] == ["powered_tile_execution_not_demonstrated"]


def test_demanded_execution_does_not_require_a_completed_root() -> None:
    row = _worker_row("reverse", 32, 8)
    row["metrics"]["completed_result_entries"] = 0
    assert probe._runtime_executed(row)


def test_missing_absorption_measurements_are_not_observed_zeros() -> None:
    metrics = _metrics(8)
    del metrics["powered_absorption_max_span"]
    assert not probe._valid_worker_metrics(metrics)


def test_primitive_pair_absorption_cannot_claim_a_powered_public_cutover() -> None:
    row = _worker_row("reverse", 32, 8)
    row["metrics"]["powered_absorption_max_span"] = 2
    assert not probe._runtime_executed(row)
    row["metrics"]["powered_absorption_max_span"] = 31
    assert probe._runtime_executed(row)
    row["family"] = "collatz"
    assert not probe._runtime_executed(row)
    row["metrics"]["powered_absorption_max_span"] = 32
    assert probe._runtime_executed(row)


class WorkerFixture(TypedDict):
    family: str
    horizon: int
    source_before: str
    source_after: str
    audit_unchanged: bool
    digit: int
    repeat_digit: int
    cold_seconds: float
    metrics: dict[str, int]
    status: NotRequired[str]

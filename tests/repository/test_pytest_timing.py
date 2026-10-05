"""Bounded phase diagnostics preserve failing setup/call/teardown reports."""

from __future__ import annotations

import json
import pstats
from pathlib import Path
from types import SimpleNamespace
from typing import cast

import pytest

from devtools.benchmarks import pytest_timing


def _failed_report(longrepr: str, when: str = "call") -> pytest.TestReport:
    return cast(
        pytest.TestReport,
        SimpleNamespace(
            nodeid="tests/example.py::test_failure",
            when=when,
            outcome="failed",
            duration=0.25,
            longrepr=longrepr,
        ),
    )


def _read_records(path: Path) -> list[dict[str, object]]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines()]


@pytest.mark.parametrize("phase", ("setup", "call", "teardown"))
def test_failure_report_is_utf8_safe_and_per_record_bounded(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, phase: str
) -> None:
    monkeypatch.setattr(pytest_timing, "_FAILURE_TEXT_LIMIT", 64)
    path = tmp_path / "phases.jsonl"
    plugin = pytest_timing.PhaseTiming(path)
    plugin.pytest_runtest_logreport(_failed_report("π traceback " * 100, phase))
    plugin.pytest_sessionfinish(exitstatus=1)
    plugin.pytest_unconfigure()

    row = _read_records(path)[0]
    assert row["outcome"] == "failed"
    assert row["phase"] == phase
    assert row["nodeid"] == "tests/example.py::test_failure"
    assert row["failure_longrepr_truncated"] is True
    traceback = row["failure_longrepr"]
    assert isinstance(traceback, str)
    assert "[longrepr truncated]" in traceback
    assert len(traceback.encode("utf-8")) <= 64


def test_phase_log_byte_cap_writes_truncation_marker(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(pytest_timing, "_BYTE_LIMIT", 650)
    monkeypatch.setattr(pytest_timing, "_FAILURE_TEXT_LIMIT", 80)
    path = tmp_path / "phases.jsonl"
    plugin = pytest_timing.PhaseTiming(path)
    for _ in range(10):
        plugin.pytest_runtest_logreport(_failed_report("traceback " * 100))
    plugin.pytest_sessionfinish(exitstatus=1)
    plugin.pytest_unconfigure()

    rows = _read_records(path)
    assert rows[-2]["status"] == "truncated"
    assert rows[-1]["status"] == "finished"
    assert rows[-1]["exitstatus"] == 1
    assert path.stat().st_size <= 650


def test_optional_profile_records_executed_calls_without_changing_phase_output(
    tmp_path: Path,
) -> None:
    path = tmp_path / "phases.jsonl"
    profile = tmp_path / "calls.pstats"
    plugin = pytest_timing.PhaseTiming(path, profile)
    plugin.pytest_runtest_logreport(_failed_report("measured failure"))
    plugin.pytest_sessionfinish(exitstatus=1)
    plugin.pytest_unconfigure()
    plugin.pytest_unconfigure()
    assert pstats.Stats(str(profile)).get_stats_profile().func_profiles
    assert _read_records(path)[0]["failure_longrepr"] == "measured failure"
    assert _read_records(path)[-1]["exitstatus"] == 1


def test_diagnostic_limits_are_bound_to_each_recorder(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    path = tmp_path / "running-suite.jsonl"
    recorder = pytest_timing.PhaseTiming(path)
    monkeypatch.setattr(pytest_timing, "_BYTE_LIMIT", 1)
    monkeypatch.setattr(pytest_timing, "_RECORD_LIMIT", 1)
    monkeypatch.setattr(pytest_timing, "_FAILURE_TEXT_LIMIT", 32)
    recorder.pytest_runtest_logreport(_failed_report("full diagnostic " * 10))
    recorder.pytest_unconfigure()
    row = _read_records(path)[0]
    assert row["outcome"] == "failed"
    assert row["failure_longrepr"] == "full diagnostic " * 10
    assert not recorder.truncated

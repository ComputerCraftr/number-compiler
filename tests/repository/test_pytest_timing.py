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
    tmp_path: Path, phase: str
) -> None:
    path = tmp_path / "phases.jsonl"
    plugin = pytest_timing.PhaseTiming(path, failure_text_limit=64)
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
    tmp_path: Path,
) -> None:
    path = tmp_path / "phases.jsonl"
    plugin = pytest_timing.PhaseTiming(
        path,
        byte_limit=650,
        failure_text_limit=80,
    )
    for _ in range(10):
        plugin.pytest_runtest_logreport(_failed_report("traceback " * 100))
    plugin.pytest_sessionfinish(exitstatus=1)
    plugin.pytest_unconfigure()

    rows = _read_records(path)
    assert rows[-2]["status"] == "truncated"
    assert rows[-1]["status"] == "finished"
    assert rows[-1]["exitstatus"] == 1
    assert path.stat().st_size <= 650


def test_record_allowance_scales_from_selection_past_previous_ceiling(
    tmp_path: Path,
) -> None:
    # One selected item beyond the former three-phase record threshold.
    previous_ceiling = 32768
    selected_items = previous_ceiling // 3 + 1
    path = tmp_path / "large-selection.jsonl"
    plugin = pytest_timing.PhaseTiming(path)
    plugin.pytest_collection_finish(
        cast(pytest.Session, SimpleNamespace(items=range(selected_items)))
    )

    expected_allowance = 3 * selected_items + 3
    assert expected_allowance > previous_ceiling
    assert plugin.record_limit == expected_allowance
    assert plugin.record_safety_limit >= expected_allowance

    # Model the reports preceding the final ordinary phase without writing
    # thirty thousand fixture records. The selected run fits; an extra report
    # still hits the bounded-record marker.
    plugin.records = plugin.record_limit - 3
    plugin.pytest_runtest_logreport(_failed_report("last selected phase"))
    assert not plugin.truncated
    assert plugin.records == plugin.record_limit - 2
    plugin.pytest_runtest_logreport(_failed_report("extra retry phase"))
    assert plugin.truncated
    plugin.pytest_sessionfinish(exitstatus=1)
    plugin.pytest_unconfigure()

    rows = _read_records(path)
    assert rows[-2]["status"] == "truncated"
    assert rows[-1]["status"] == "finished"

    cap_path = tmp_path / "capped-selection.jsonl"
    safety_ceiling = expected_allowance - 1
    capped = pytest_timing.PhaseTiming(cap_path, record_safety_limit=safety_ceiling)
    capped.pytest_collection_finish(
        cast(pytest.Session, SimpleNamespace(items=range(selected_items)))
    )
    assert capped.record_limit == safety_ceiling
    capped.pytest_unconfigure()


@pytest.mark.parametrize("invalid_limit", (0, -1, True))
def test_record_safety_limit_is_validated_before_opening_output(
    tmp_path: Path, invalid_limit: int
) -> None:
    path = tmp_path / "invalid-limit.jsonl"
    with pytest.raises(ValueError, match="positive exact integer"):
        pytest_timing.PhaseTiming(path, record_safety_limit=invalid_limit)
    assert not path.exists()


@pytest.mark.parametrize(
    ("limit_name", "invalid_limit"),
    (("byte_limit", 0), ("failure_text_limit", False)),
)
def test_other_diagnostic_limits_are_validated_before_opening_output(
    tmp_path: Path, limit_name: str, invalid_limit: int
) -> None:
    path = tmp_path / "invalid-limit.jsonl"
    with pytest.raises(ValueError, match="positive exact integer"):
        if limit_name == "byte_limit":
            pytest_timing.PhaseTiming(path, byte_limit=invalid_limit)
        else:
            pytest_timing.PhaseTiming(path, failure_text_limit=invalid_limit)
    assert not path.exists()


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
    tmp_path: Path,
) -> None:
    path = tmp_path / "running-suite.jsonl"
    limited = pytest_timing.PhaseTiming(
        tmp_path / "limited.jsonl",
        record_safety_limit=1,
        byte_limit=1,
        failure_text_limit=32,
    )
    recorder = pytest_timing.PhaseTiming(path)
    assert limited.record_safety_limit == 1
    assert limited.byte_limit == 1
    assert limited.failure_text_limit == 32
    recorder.pytest_runtest_logreport(_failed_report("full diagnostic " * 10))
    recorder.pytest_unconfigure()
    limited.pytest_unconfigure()
    row = _read_records(path)[0]
    assert row["outcome"] == "failed"
    assert row["failure_longrepr"] == "full diagnostic " * 10
    assert not recorder.truncated

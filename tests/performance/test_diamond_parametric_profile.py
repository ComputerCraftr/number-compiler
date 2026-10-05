"""The candidate profiler preserves failures and bypasses response registers."""

import json
from typing import Never

import pytest

import devtools.benchmarks.diamond_parametric_profile as profile
from devtools.checks.validation_policy import (
    PYTHON_COMMAND_SECONDS,
    PYTHON_MEMORY_BYTES,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded


@pytest.mark.validation  # Runs a real profiled execution worker.
def test_profile_small_worker_reports_real_observations_and_inventory() -> None:
    row = profile.worker("reverse", 0)
    assert row["status"] == "completed"
    assert row["exact_completed_observations"]
    assert row["representation_audits_complete"]
    assert row["git_source"]["git_commit"]
    assert row["cacheable"] is False
    assert [item["result"] for item in row["phases"][1:]] == [6, 6, 9, 6, 3]
    for item in row["phases"]:
        report = item["audit"]["result"]
        assert report["retained_point_response_scalars"] == 0
        assert report["resource_accounting_mismatch"] == 0
        assert item["process_peak_rss_bytes"] > 0
    json.dumps(row)


def test_failed_construction_preserves_failure_and_null_skipped_work(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def fail(*args: object) -> Never:
        raise BlockContextBudgetExceeded("deliberate profile rejection")

    monkeypatch.setattr(profile, "construct", fail)
    row = profile.worker("reverse", 0)
    assert row["status"] == "blocked"
    assert row["phases"][0]["status"] == "budget_exceeded"
    assert row["phases"][0]["result"] is None
    assert row["phases"][0]["seconds"] >= 0
    for phase in row["phases"][1:]:
        assert phase["status"] == "skipped"
        assert (
            phase["result"]
            is phase["seconds"]
            is phase["cpu_seconds"]
            is phase["work_delta"]
            is None
        )


@pytest.mark.validation  # Two independently executed profile workers.
def test_worker_processes_have_independent_lifetimes_and_fixed_caps() -> None:
    first = profile.fresh_case("collatz", 0, 16)
    second = profile.fresh_case("collatz", 0, 32)
    assert first["status"] == second["status"] == "completed", (first, second)
    assert first["pid"] != second["pid"]
    assert first["source_width"] == 16 and second["source_width"] == 32
    assert profile.CACHE_ENTRIES == 180_000
    assert PYTHON_COMMAND_SECONDS == 60
    assert PYTHON_MEMORY_BYTES == 4 * 1024**3


def test_timeout_is_distinct_from_a_successful_zero_result() -> None:
    def fail() -> Never:
        raise TimeoutError("deliberate profile timeout")

    timed = profile.measured(fail)
    successful = profile.measured(lambda: 0)
    assert timed["status"] == "timeout" and timed["result"] is None
    assert successful["status"] == "ok" and successful["result"] == 0

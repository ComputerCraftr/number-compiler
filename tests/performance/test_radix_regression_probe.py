"""The fixed regression probe must fail closed without weakening its limits."""

from __future__ import annotations

from copy import deepcopy
from pathlib import Path

import pytest

from devtools.benchmarks.radix_regression_probe import (
    COLD_LIMIT,
    REPEAT_LIMIT,
    TRIALS,
    trial_passes,
    write_result,
)
from tests.support.report_values import object_record


def complete() -> dict[str, object]:
    return {
        "git_source_before": {
            "git_commit": "commit",
            "git_tree": "tree",
            "git_object_format": "sha1",
            "git_dirty": False,
        },
        "git_source_after": {
            "git_commit": "commit",
            "git_tree": "tree",
            "git_object_format": "sha1",
            "git_dirty": False,
        },
        "construction": {"status": "ok"},
        "cold": {"status": "ok", "seconds": COLD_LIMIT, "value": 2},
        "repeat": {"status": "ok", "seconds": REPEAT_LIMIT, "value": 2},
        "no_response_or_microblock_assistance": True,
        "audit": {
            "status": "ok",
            "ledger_unchanged": True,
            "resource_audit_complete": 1,
            "representation_boundary_complete": 1,
            "forbidden_future_payloads": 0,
        },
    }


def test_probe_accepts_exact_fixed_limits_without_changing_trial_count() -> None:
    assert (TRIALS, COLD_LIMIT, REPEAT_LIMIT) == (5, 0.25, 0.01)
    assert trial_passes(complete())


@pytest.mark.parametrize(
    "phase,field,value",
    (
        ("cold", "seconds", 0.250001),
        ("repeat", "seconds", 0.010001),
        ("cold", "value", 1),
        ("repeat", "status", "unavailable"),
        ("cold", "status", "error"),
        ("audit", "resource_audit_complete", 0),
        ("audit", "representation_boundary_complete", 0),
        ("audit", "forbidden_future_payloads", 1),
        ("audit", "ledger_unchanged", False),
    ),
)
def test_slow_incomplete_wrong_or_failed_audit_is_not_accepted(
    phase: str, field: str, value: bool | float | str
) -> None:
    row = deepcopy(complete())
    phase_record = object_record(row[phase])
    phase_record[field] = value
    row[phase] = phase_record
    assert not trial_passes(row)


@pytest.mark.parametrize(
    "field", ("git_source_after", "no_response_or_microblock_assistance")
)
def test_git_state_changes_or_forbidden_acceleration_are_not_accepted(
    field: str,
) -> None:
    row = complete()
    row[field] = False if field != "git_source_after" else {"git_commit": "changed"}
    assert not trial_passes(row)


def test_existing_evidence_cannot_be_overwritten_even_through_symlink(
    tmp_path: Path,
) -> None:
    historical = tmp_path / "radix_original_source_v1.json"
    historical.write_text("historical evidence\n")
    alias = tmp_path / "alias.json"
    alias.symlink_to(historical)
    for path in (historical, alias):
        with pytest.raises(FileExistsError):
            write_result(path, {"status": "PASS"})
    assert historical.read_text() == "historical evidence\n"

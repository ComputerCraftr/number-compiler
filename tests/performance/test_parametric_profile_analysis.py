"""Partial execution must not masquerade as cheap completed work."""

from typing import TypedDict

from devtools.benchmarks.parametric_profile_analysis import (
    analyze,
    phase_analysis,
    sampled,
)


class MetricReport(TypedDict):
    resource_work_counters: dict[str, int]
    resource_workspace_peaks: dict[str, int]
    resource_inventory: list[dict[str, object]]


class AuditResult(TypedDict):
    status: str
    result: MetricReport


class PhaseRow(TypedDict):
    name: str
    status: str
    exact: bool
    work_delta: dict[str, int]
    audit: AuditResult
    retained_entries: int
    retained_nodes: int
    retained_entry_delta: int
    retained_node_delta: int


class ProfileRow(TypedDict):
    family: str
    steps: int
    requested_source_width: int | None
    status: str
    phases: list[PhaseRow]


def row(n: int, status: str = "ok", work: int = 1) -> ProfileRow:
    report: MetricReport = {
        "resource_work_counters": {"unexpected_new_dag_visits": work},
        "resource_workspace_peaks": {},
        "resource_inventory": [],
    }
    phase: PhaseRow = {
        "name": "point_0_repeat",
        "status": status,
        "exact": True,
        "work_delta": {"unexpected_new_dag_visits": work},
        "audit": {"status": "ok", "result": report},
        "retained_entries": work,
        "retained_nodes": 1,
        "retained_entry_delta": work,
        "retained_node_delta": 1,
    }
    return {
        "family": "collatz",
        "steps": n,
        "requested_source_width": None,
        "status": "completed" if status == "ok" else "blocked",
        "phases": [phase],
    }


def test_missing_failure_value_never_becomes_zero_or_a_completed_sample() -> None:
    measured = sampled([16, 32, 64], [4, None, 8])
    assert measured["status"] == "BLOCKED"
    assert measured["values"] == [4, None, 8]
    assert measured["completed_coordinates"] == [16, 64]
    assert measured["completed_subset_assessment"]["values"] == [4, 8]


def test_every_dynamic_work_counter_is_assessed_in_its_actual_phase() -> None:
    rows = [row(16, work=16), row(32, work=32), row(64, work=64)]
    report = phase_analysis(rows, [16, 32, 64], "point_0_repeat")
    measured = report["work"]["unexpected_new_dag_visits"]
    assert measured["values"] == [16, 32, 64]
    assert measured["status"] == "BLOCKED"
    assert measured["doubling_ratios"] == [2, 2]


def test_partial_attempt_work_is_preserved_but_excluded_from_complete_series() -> None:
    rows = [row(16, work=10), row(32, "timeout", 20), row(64, "budget_exceeded", 30)]
    report = phase_analysis(rows, [16, 32, 64], "point_0_repeat")
    assert report["work"]["unexpected_new_dag_visits"]["values"] == [10, None, None]
    assert report["attempted_work_including_incomplete_phases"][
        "unexpected_new_dag_visits"
    ] == [10, 20, 30]
    assert report["attempted_retained_after"][2]["retained_entries"] == 30


def test_a_missing_query_phase_blocks_a_complete_scaling_release() -> None:
    report = analyze([{"rows": [row(16), row(32), row(64)]}])
    assert report["status"] == "BLOCKED"
    group = report["groups"]["collatz.temporal"]
    assert group["phases"]["active_width"]["phase_statuses"] == [None, None, None]
    assert group["phases"]["point_0_cold"]["status"] == "BLOCKED"


def test_reference_only_slots_do_not_invent_unknown_node_ownership() -> None:
    rows = [row(16), row(32), row(64)]
    for item in rows:
        item["phases"][0]["audit"]["result"]["resource_inventory"] = [
            {
                "role": "index_only",
                "nodes": 0,
                "observed_entries": 3,
                "observed_nodes": None,
            }
        ]
    report = phase_analysis(rows, [16, 32, 64], "point_0_repeat")
    assert "index_only.observed_nodes" not in report["role_inventory"]
    assert report["role_inventory"]["index_only.observed_entries"]["values"] == [
        3,
        3,
        3,
    ]


def test_anchor_envelope_failure_is_distinguished_from_observed_log_increments() -> (
    None
):
    report = sampled([16, 32, 64, 128, 256, 512], [1, 2, 3, 4, 5, 6])
    assert report["status"] == "PASS"
    assert report["anchored_envelope_status"] == "BLOCKED"
    assert report["exact_affine_log_series"]
    assert report["observed_increment_per_log2_axis"] == [1, 1, 1, 1, 1]


def test_linear_and_quadratic_resources_do_not_pass_exact_log_rule() -> None:
    axis = [16, 32, 64, 128, 256, 512]
    for values in (axis, [value * value for value in axis]):
        report = sampled(axis, values)
        assert report["status"] == "BLOCKED"
        assert not report["exact_affine_log_series"]
    assert sampled(axis, [7] * len(axis))["status"] == "PASS"


def test_equal_differences_on_linear_axis_do_not_imply_logarithmic_growth() -> None:
    report = sampled([16, 32, 48, 64], [16, 32, 48, 64])
    assert not report["geometrically_spaced_axis"]
    assert not report["exact_affine_log_series"]
    assert report["status"] == "BLOCKED"

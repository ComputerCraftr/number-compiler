"""The behavior probe reports an operation vector without an asymptotic claim."""

from __future__ import annotations

from devtools.benchmarks.behavior_reuse_probe import (
    HORIZONS,
    TOTAL_WORK_COVERAGE,
    _work_vector,
    summarize,
)
from devtools.benchmarks.causal_tile_growth_probe import WORK_FIELDS


def test_behavior_probe_maps_the_complete_causal_work_vector() -> None:
    counters = {
        "tile_causal_task_memo_evaluations": 7,
        "tile_boundary_transfer_descents": 11,
        "future_behavior_binding_requests": 13,
    }
    vector = _work_vector(counters)
    assert set(vector) == set(WORK_FIELDS)
    assert vector["task_memo_evaluations"] == 7
    assert vector["boundary_transfer_descents"] == 11
    assert vector["future_behavior_binding_requests"] == 13
    assert vector["causal_frames"] is None


def test_behavior_probe_does_not_claim_scaling_from_partial_instrumentation() -> None:
    vector = dict.fromkeys(WORK_FIELDS, 1)
    records = [
        {
            "enabled": enabled,
            "steps": HORIZONS[0],
            "trial": trial,
            "status": "complete",
            "row": {
                "cold_seconds": 0.01,
                "query_seconds": 0.001,
                "live_entries": 1,
                "live_nodes": 1,
                "cold_work_vector": vector,
            },
        }
        for enabled in (True, False)
        for trial in range(5)
    ]
    completed = [row for row in summarize(records) if "metrics" in row]
    assert len(completed) == 2
    for row in completed:
        assert row["total_work_coverage"] == TOTAL_WORK_COVERAGE
        assert row["classification"] == (
            "profile-specific operation vector; no total-work scaling claim"
        )

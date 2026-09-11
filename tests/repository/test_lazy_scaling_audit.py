"""Performance gates must reject hidden work even when canonical classes stay tiny."""

from __future__ import annotations

import pytest

from devtools.checks.lazy_scaling_audit import (
    SPACE_METRICS,
    WORK_METRICS,
    MetricSnapshot,
    ScalingSample,
    assess_series,
    sample_deltas,
    scaling_report,
    work_counters,
)


def rows(
    *, quadratic_work: bool = False, warm_replay: bool = False
) -> list[ScalingSample]:
    result: list[ScalingSample] = []
    for n in (16, 32, 64, 128):
        counters = {
            "reverse_offset_dag_visits": n.bit_length(),
            "reverse_evaluator_transitions": n.bit_length(),
            "finite_port_applications": n * n if quadratic_work else n.bit_length(),
        }
        cold: MetricSnapshot = dict.fromkeys((*SPACE_METRICS, *WORK_METRICS), 7)
        cold["bimachine_composition_certified"] = 1
        cold["resource_work_counters"] = counters
        warm: MetricSnapshot = {
            **cold,
            "resource_work_counters": {
                key: value + (n * n if warm_replay else 0)
                for key, value in counters.items()
            },
        }
        result.append(
            {
                "family": "reverse",
                "steps": n,
                "cold": cold,
                "warm": warm,
                "cold_seconds": 0.0,
                "warm_seconds": 0.0,
            }
        )
    return result


def test_logarithmic_and_constant_samples_pass_but_linear_and_quadratic_fail() -> None:
    steps = (16, 32, 64, 128, 256)
    assert assess_series(steps, (5, 6, 7, 8, 9))["status"] == "PASS"
    assert assess_series(steps, (7, 7, 7, 7, 7))["status"] == "PASS"
    assert assess_series(steps, steps)["status"] == "BLOCKED"
    assert (
        assess_series(steps, tuple(n * n for n in steps))["local_exponents"]
        == [2.0] * 4
    )
    with pytest.raises(ValueError):
        assess_series((16, 16), (1, 2))


def test_tiny_class_counts_cannot_hide_quadratic_finite_port_work() -> None:
    baseline = scaling_report(rows())
    assert baseline["sampled_envelope_status"] == "PASS"
    assert baseline["status"] == "PASS"
    assert baseline["release_blockers"] == []
    report = scaling_report(rows(quadratic_work=True))
    assert report["status"] == "BLOCKED"
    assert (
        "work.finite_port_applications"
        in report["families"]["reverse"]["cold_blockers"]
    )
    assert report["bimachine_composition"] == "CERTIFIED"


def test_execution_certification_and_measured_scaling_are_independent() -> None:
    data = rows()
    for row in data:
        del row["cold"]["bimachine_composition_certified"]
    report = scaling_report(data)
    assert report["sampled_envelope_status"] == "PASS"
    assert report["status"] == "BLOCKED"
    assert report["release_blockers"] == ["bimachine_composition_not_certified"]
    for row in data:
        row["cold"]["bimachine_composition_certified"] = 1
        row["cold"]["sequential_generation_advances"] = row["steps"]
    assert (
        "sequential_generation_advances_observed"
        in scaling_report(data)["release_blockers"]
    )


def test_identical_warm_query_work_is_an_independent_release_blocker() -> None:
    data = rows(warm_replay=True)
    report = scaling_report(data)
    assert report["families"]["reverse"]["cold_blockers"] == []
    assert "finite_port_applications" in report["families"]["reverse"]["warm_blockers"]
    assert (
        sample_deltas(data[-1]["cold"], data[-1]["warm"])["work"][
            "finite_port_applications"
        ]
        == 128**2
    )


@pytest.mark.parametrize(
    "counter", ["primitive_transition_evaluations", "primitive_output_evaluations"]
)
def test_constant_primitive_replay_still_blocks_identical_point_reuse(
    counter: str,
) -> None:
    data = rows()
    for row in data:
        row["cold"][counter] = 3
        row["warm"][counter] = 4
    report = scaling_report(data)
    assert report["sampled_envelope_status"] == "PASS"
    assert report["identical_point_primitive_reuse"] == "BLOCKED"
    assert report["release_blockers"] == [
        "repeated_identical_point_evaluates_primitive_kernel"
    ]


def test_new_counter_keys_cannot_silently_escape_the_scaling_gate() -> None:
    data = rows()
    for row in data:
        work_counters(row["cold"])["previously_omitted_dag_visits"] = row["steps"] ** 2
        work_counters(row["warm"])["previously_omitted_dag_visits"] = row["steps"] ** 2
    report = scaling_report(data)
    assert (
        "work.previously_omitted_dag_visits"
        in report["families"]["reverse"]["cold_blockers"]
    )


def test_missing_instrumentation_is_unknown_not_a_successful_zero() -> None:
    data = rows()
    for row in data:
        del work_counters(row["cold"])["reverse_evaluator_transitions"]
        del work_counters(row["warm"])["reverse_evaluator_transitions"]
    report = scaling_report(data)
    assert report["status"] == "BLOCKED"
    assert report["families"]["reverse"]["missing_instrumentation"] == [
        "reverse_evaluator_transitions"
    ]


def test_last_point_register_cannot_hide_replay_after_another_coordinate() -> None:
    data = rows()
    for row in data:
        row["query_phases"] = {
            "revisited": {
                "delta": {"work": {"finite_port_applications": row["steps"] ** 2}}
            }
        }
    report = scaling_report(data)
    assert report["families"]["reverse"]["warm_blockers"] == []
    assert report["families"]["reverse"]["other_query_blockers"] == [
        "revisited.finite_port_applications"
    ]
    assert report["status"] == "BLOCKED"


def test_schema_four_requires_actual_diamond_instruments_not_legacy_counters() -> None:
    from number_compiler.resources.metric_registry import DIAMOND_WORK_COUNTERS

    data = rows()
    for row in data:
        row["cold"]["metrics_schema_version"] = 4
    report = scaling_report(data)
    assert report["status"] == "BLOCKED"
    assert (
        "diamond_requests" in report["families"]["reverse"]["missing_instrumentation"]
    )
    for row in data:
        for snapshot in (row["cold"], row["warm"]):
            work_counters(snapshot).update(dict.fromkeys(DIAMOND_WORK_COUNTERS, 0))
    assert scaling_report(data)["status"] == "PASS"

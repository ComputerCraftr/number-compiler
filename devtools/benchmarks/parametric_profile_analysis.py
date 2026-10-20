"""Per-resource sampled scaling assessment of capped diamond profiles.

Raw profiles are immutable inputs. Failed or missing observations remain null;
attempted work before a cap is shown separately and never treated as completion.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from collections.abc import Mapping, Sequence
from math import log2
from pathlib import Path
from typing import Any

from devtools.benchmarks.report_schema import record, sequence
from devtools.checks.lazy_scaling_audit import SPACE_METRICS, assess_series

PHASES = (
    "construction",
    "point_0_cold",
    "point_0_repeat",
    "point_1",
    "point_0_revisit",
    "active_width",
)
EARLY_HITS = (
    "higher_context_cache_hits",
    "higher_head_cache_hits",
    "primitive_continuation_cache_hits",
    "finite_interface_admission_cache_hits",
    "boundary_expression_substitution_cache_hits",
)
LATE_HITS = (
    "boundary_expression_intern_hits",
    "boundary_expression_staged_interner_hits",
    "boundary_expression_unchanged_children_late_hits",
    "higher_context_program_interner_hits",
    "finite_expression_interner_hits",
    "finite_decision_interner_hits",
)


def sampled(
    axis: Sequence[int], values: Sequence[int | None], *, slack: float = 1.25
) -> dict[str, Any]:
    completed = [
        (coordinate, value)
        for coordinate, value in zip(axis, values, strict=True)
        if value is not None
    ]
    if len(completed) == len(axis) and len(axis) >= 3:
        observed = [int(value) for value in values if value is not None]
        result: dict[str, object] = dict(assess_series(axis, observed, slack=slack))
        increments = [
            (right - left) / log2(b / a)
            for a, b, left, right in zip(
                axis, axis[1:], observed, observed[1:], strict=False
            )
        ]
        result["observed_increment_per_log2_axis"] = increments
        differences = [right - left for left, right in itertools.pairwise(observed)]
        geometric = all(b * axis[0] == axis[1] * a for a, b in itertools.pairwise(axis))
        affine = geometric and len(set(differences)) == 1
        constant = len(set(observed)) == 1
        result["exact_additive_first_differences"] = differences
        result["geometrically_spaced_axis"] = geometric
        result["exact_affine_log_series"] = affine
        result["exact_constant_series"] = constant
        result["anchored_envelope_status"] = result["status"]
        if affine or constant:
            result["status"] = "PASS"
        return result
    return {
        "status": "BLOCKED",
        "reason": "incomplete series or fewer than three completed samples",
        "values": list(values),
        "completed_coordinates": [pair[0] for pair in completed],
        "completed_subset_assessment": (
            assess_series(
                [pair[0] for pair in completed],
                [pair[1] for pair in completed],
                slack=slack,
            )
            if len(completed) >= 2
            else None
        ),
    }


def phase(row: Mapping[str, Any], name: str) -> Mapping[str, object] | None:
    raw_phases: object = row.get("phases")
    if raw_phases is None:
        return None
    for raw_phase in sequence(raw_phases):
        phase_record = record(raw_phase)
        if phase_record.get("name") == name:
            return phase_record
    return None


def _work_delta(value: Mapping[str, object] | None) -> dict[str, object]:
    if value is None:
        return {}
    raw_delta = value.get("work_delta")
    return {} if raw_delta is None else record(raw_delta)


def _counter_value(delta: Mapping[str, object], counter: str) -> int:
    value = delta.get(counter, 0)
    if type(value) is not int:
        raise TypeError(f"work counter {counter!r} must be an exact integer")
    return value


def _optional_counter(value: Mapping[str, object] | None, field: str) -> int | None:
    if value is None:
        return None
    counter = value.get(field)
    if counter is None:
        return None
    if type(counter) is not int:
        raise TypeError(f"report counter {field!r} must be an exact integer or null")
    return counter


def metrics(value: Mapping[str, Any] | None) -> Mapping[str, Any] | None:
    audit = None if value is None else value.get("audit")
    return audit.get("result") if audit and audit["status"] == "ok" else None


def completed(value: Mapping[str, Any] | None) -> bool:
    return value is not None and value["status"] == "ok" and value.get("exact", True)


def phase_analysis(
    rows: Sequence[Mapping[str, Any]], axis: Sequence[int], name: str
) -> dict[str, Any]:
    phases: list[Mapping[str, object] | None] = [phase(row, name) for row in rows]
    reports = [metrics(value) for value in phases]
    names: set[str] = set()
    workspace_names: set[str] = set()
    roles: set[str] = set()
    for value, report in zip(phases, reports, strict=True):
        if value is not None:
            names.update(_work_delta(value))
        if report is not None:
            names.update(report["resource_work_counters"])
            workspace_names.update(report["resource_workspace_peaks"])
            roles.update(row["role"] for row in report["resource_inventory"])
    work, attempted = {}, {}
    for counter in sorted(names):
        if counter.endswith("_peak") or "_peak_" in counter:
            workspace_names.add(counter)
            continue
        values: list[int | None] = [
            _counter_value(_work_delta(value), counter)
            if value is not None and completed(value)
            else None
            for value in phases
        ]
        work[counter] = sampled(axis, values)
        attempted[counter] = [
            (
                _counter_value(_work_delta(value), counter)
                if value is not None and value.get("work_delta") is not None
                else None
            )
            for value in phases
        ]
    retained = {}
    for counter in (*SPACE_METRICS, "resource_ledger_entries", "resource_ledger_nodes"):
        values = [
            report.get(counter)
            if value is not None and completed(value) and report is not None
            else None
            for value, report in zip(phases, reports, strict=True)
        ]
        retained[counter] = sampled(axis, values)
    for counter in ("retained_entry_delta", "retained_node_delta"):
        retained[counter] = sampled(
            axis,
            [
                _optional_counter(value, counter)
                if value is not None and completed(value)
                else None
                for value in phases
            ],
        )
    workspace = {
        counter: sampled(
            axis,
            [
                report["resource_workspace_peaks"].get(counter, 0)
                if value is not None and completed(value) and report is not None
                else None
                for value, report in zip(phases, reports, strict=True)
            ],
        )
        for counter in sorted(workspace_names)
    }
    role_series = {}
    for role in sorted(roles):
        for unit in ("observed_entries", "observed_nodes"):
            if unit == "observed_nodes" and not any(
                item["role"] == role
                and (item["observed_nodes"] is not None or item["nodes"] > 0)
                for report in reports
                if report is not None
                for item in report["resource_inventory"]
            ):
                continue  # Reference-only index slots do not own node records.
            role_values: list[int | None] = []
            for value, report in zip(phases, reports, strict=True):
                records = (
                    []
                    if report is None
                    else [
                        row
                        for row in report["resource_inventory"]
                        if row["role"] == role
                    ]
                )
                if unit == "observed_nodes":
                    records = [
                        row
                        for row in records
                        if row["observed_nodes"] is not None or row["nodes"] > 0
                    ]
                role_values.append(
                    sum(row[unit] for row in records)
                    if value is not None
                    and completed(value)
                    and report is not None
                    and all(row[unit] is not None for row in records)
                    else None
                )
            role_series[f"{role}.{unit}"] = sampled(axis, role_values)
    categories = {
        "work": work,
        "retained": retained,
        "workspace_high_water": workspace,
        "role_inventory": role_series,
    }
    blockers = [
        f"{category}.{counter}"
        for category, entries in categories.items()
        for counter, entry in entries.items()
        if entry["status"] != "PASS"
    ]
    observational = {
        "seconds": [
            value.get("seconds") if value is not None and completed(value) else None
            for value in phases
        ],
        "cpu_seconds": [
            value.get("cpu_seconds") if value is not None and completed(value) else None
            for value in phases
        ],
        "process_peak_rss_bytes": [
            value.get("process_peak_rss_bytes")
            if value is not None and completed(value)
            else None
            for value in phases
        ],
    }
    return {
        "status": "BLOCKED"
        if blockers or not all(completed(value) for value in phases)
        else "PASS",
        "phase_statuses": [
            None if value is None else value["status"] for value in phases
        ],
        **categories,
        "attempted_work_including_incomplete_phases": attempted,
        "attempted_workspace_high_water": {
            counter: [
                report["resource_workspace_peaks"].get(counter, 0)
                if report is not None
                else None
                for report in reports
            ]
            for counter in sorted(workspace_names)
        },
        "attempted_retained_after": [
            {key: value.get(key) for key in ("retained_entries", "retained_nodes")}
            if value is not None
            else None
            for value in phases
        ],
        "phase_errors": [
            None if value is None else value.get("error") for value in phases
        ],
        "observations_excluded_from_deterministic_envelope": observational,
        "blockers": blockers,
        "early_request_cache_hits": {
            key: work[key] for key in EARLY_HITS if key in work
        },
        "late_duplicate_discoveries": {
            key: work[key] for key in LATE_HITS if key in work
        },
    }


def analyze(reports: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    rows: list[Mapping[str, Any]] = [
        row for report in reports for row in report["rows"]
    ]
    groups: dict[str, dict[str, Any]] = {}
    for family in sorted({row["family"] for row in rows}):
        for series in ("temporal", "width"):
            selected = [
                row
                for row in rows
                if row["family"] == family
                and (row.get("requested_source_width") is None)
                == (series == "temporal")
            ]
            if not selected:
                continue
            selected.sort(
                key=lambda row: (
                    row["steps"]
                    if series == "temporal"
                    else row["requested_source_width"]
                )
            )
            axis = [
                row["steps"] if series == "temporal" else row["requested_source_width"]
                for row in selected
            ]
            phases = {name: phase_analysis(selected, axis, name) for name in PHASES}
            primitive_replay: list[bool | None] = []
            for row in selected:
                repeated = phase(row, "point_0_repeat")
                if not completed(repeated):
                    primitive_replay.append(None)
                else:
                    assert repeated is not None
                    delta = _work_delta(repeated)
                    primitive_replay.append(
                        any(
                            _counter_value(delta, name) > 0
                            for name in (
                                "primitive_transition_evaluations",
                                "primitive_output_evaluations",
                            )
                        )
                    )
            statuses = [row["status"] for row in selected]
            valid = all(
                row.get("representation_audits_complete", False)
                and row.get("exact_completed_observations", False)
                and isinstance(row.get("git_source"), dict)
                for row in selected
            )
            groups[f"{family}.{series}"] = {
                "axis_name": "N" if series == "temporal" else "original_source_width",
                "axis": axis,
                "fixed_steps": selected[0]["steps"] if series == "width" else None,
                "source_widths": [row.get("source_width") for row in selected],
                "case_statuses": statuses,
                "phases": phases,
                "construction_scaling_status": phases["construction"]["status"],
                "postconstruction_scaling_status": (
                    "PASS"
                    if all(phases[name]["status"] == "PASS" for name in PHASES[1:])
                    else "BLOCKED"
                ),
                "identical_query_repeats_primitive_work": primitive_replay,
                "identical_query_primitive_reuse_status": "PASS"
                if all(value is False for value in primitive_replay)
                else "BLOCKED",
                "all_available_representation_and_correctness_checks_pass": valid,
                "status": (
                    "PASS"
                    if valid
                    and all(status == "completed" for status in statuses)
                    and all(item["status"] == "PASS" for item in phases.values())
                    and all(value is False for value in primitive_replay)
                    else "BLOCKED"
                ),
            }
    return {
        "analysis_schema": 1,
        "status": "PASS"
        if groups and all(row["status"] == "PASS" for row in groups.values())
        else "BLOCKED",
        "criterion": "Each completed counter series must be exactly constant, have exact constant additive first differences on a geometrically spaced axis, or fit the preserved 1.25 anchored log envelope; at least three samples and no missing phases.",
        "affine_log_rule": "Geometric spacing is checked by integer cross-products and first differences by exact integer equality. No fit tolerance or enlarged slack is used.",
        "scope": "Sampled measured work and retained resources; neither a complexity theorem nor a substitute for the bimachine composition proof.",
        "missing_values": "Failed/skipped phases remain null; attempted partial work is reported separately. Absent counters in successful sparse deltas mean zero emitted events.",
        "work_units": "Each counter is assessed separately; counters, cache slots, nodes, references and workspace peaks are never added across unlike units.",
        "inventory_units": "Reference-only containers declaring zero owned nodes and no node-count callback contribute cache slots, not an unavailable node series. Charged nodes with no observed count remain unknown.",
        "source_input_costs": "Construction work and actual original source widths are included, separately from powered queries.",
        "warm_queries": "Immediate repeat, adjacent point and revisited point have separate per-phase work series; no response register is used.",
        "git_sources": [row.get("git_source") for row in rows],
        "evidence_mode": "development",
        "cacheable": False,
        "groups": groups,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("profiles", nargs="+", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    reports: list[Mapping[str, Any]] = [
        record(json.loads(path.read_text())) for path in args.profiles
    ]
    result = analyze(reports)
    result["inputs"] = [
        {"path": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
        for path in args.profiles
    ]
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output is None:
        print(encoded, end="")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))

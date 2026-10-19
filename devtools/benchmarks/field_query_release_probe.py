"""Fresh-process field observations with leaf acceleration explicitly disabled.

Reports execution, query retention, audits, and RSS separately. It deliberately
makes no logarithmic claim from the number of compiler or image nodes.
"""

from __future__ import annotations

import argparse
import json
import os
import resource
import subprocess
import sys
from collections.abc import Callable, Mapping, Sequence
from pathlib import Path
from time import perf_counter
from typing import TYPE_CHECKING, TypedDict
from unittest.mock import patch

from devtools.checks.validation_policy import PYTHON_COMMAND_SECONDS
from devtools.git_source import git_source, same_git_revision
from devtools.paths import repository_root
from devtools.report_values import string_keyed_mapping
from number_compiler.resources.temporal_diagnostics import METRICS_SCHEMA_VERSION

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
    from number_compiler.projection.point_response import PointResponseRegister


class FamilyProbeReport(TypedDict):
    family: str
    series_complete: bool
    measured_doubling_envelopes: dict[str, bool | None]
    observed_prefix_doubling_envelopes: dict[str, bool | None]
    observed_prefix_horizons: list[object]
    release_blockers: list[str]
    status: str


class FieldProbeReport(TypedDict):
    metrics_schema_version: int
    git_source_before: dict[str, str | bool]
    git_source_after: dict[str, str | bool]
    git_revision_unchanged: bool
    evidence_mode: str
    cacheable: bool
    reusable: bool
    worker_sources_consistent: bool
    collection_complete: bool
    measurement_series_complete: bool
    scope: str
    logarithmic_execution_claim: bool
    status_scope: str
    release_complete: bool
    invocation_limit_seconds: int
    families: dict[str, FamilyProbeReport]
    status: str
    rows: list[dict[str, object]]


ROOT = repository_root()
HORIZONS = (16, 32, 64, 128, 256, 512, 1024)
INVOCATION_LIMIT_SECONDS = PYTHON_COMMAND_SECONDS
METRICS = (
    "metrics_schema_version",
    "new_canonical_field_images_published",
    "field_image_nodes",
    "field_interface_nodes",
    "total_internal_action_work",
    "resource_ledger_entries",
    "resource_ledger_nodes",
    "resource_accounting_mismatch",
    "runtime_query_state_nodes",
    "runtime_query_environment_nodes",
    "runtime_operation_memo_entries",
    "forbidden_future_payloads",
    "sequential_generation_advances",
    "whole_word_sweeps",
    "proof_machine_applications",
    "exact_microblock_entries",
    "retained_point_response_scalars",
    "temporal_parent_compositions",
    "higher_concrete_operation_evaluations",
    "higher_semantic_evaluations",
    "higher_semantic_task_frames",
    "temporal_leaf_diamond_descents",
    "higher_action_continuation_requests",
    "canonical_tile_nodes",
    "canonical_tile_peak",
    "tile_execution_memo_entries",
    "completed_result_entries",
    "powered_interface_entries",
    "spatial_interface_composition_entries",
    "spatial_interface_composition_requests",
    "spatial_interface_composition_early_hits",
    "spatial_interface_composition_publications",
    "fused_interface_entries",
    "fused_interface_requests",
    "fused_interface_early_hits",
    "tile_fused_frames",
    "tile_fused_observation_descents",
    "powered_absorption_requests",
    "powered_absorption_early_hits",
    "powered_absorption_evaluations",
    "powered_absorption_successes",
    "powered_absorption_max_span",
    "tile_scheduler_demand_descents",
)
ENVELOPE_FIELDS = (
    "total_internal_action_work",
    "resource_ledger_nodes",
    "resource_ledger_entries",
    "new_canonical_field_images_published",
    "canonical_tile_nodes",
    "tile_execution_memo_entries",
    "spatial_interface_composition_entries",
    "fused_interface_entries",
)
FORBIDDEN_EXECUTION_FIELDS = (
    "sequential_generation_advances",
    "whole_word_sweeps",
    "proof_machine_applications",
    "higher_action_continuation_requests",
)
ABSORPTION_FIELDS = (
    "powered_absorption_requests",
    "powered_absorption_early_hits",
    "powered_absorption_evaluations",
    "powered_absorption_successes",
    "powered_absorption_max_span",
    "tile_fused_observation_descents",
)


def _direct_response(
    self: PointResponseRegister,
    program: ActionProgramID,
    position: int,
    evaluate: Callable[[int], int],
) -> int:
    self.compiler.resolve(program)
    return evaluate(position)


def _no_microblock(*_args: object, **_kwargs: object) -> None:
    return None


def worker(family: str, horizon: int) -> dict[str, object]:
    from number_compiler.projection.microblock_cache import MicroblockCache
    from number_compiler.projection.point_response import PointResponseRegister
    from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

    source_before = git_source(ROOT)
    with (
        patch.object(MicroblockCache, "get", _no_microblock),
        patch.object(MicroblockCache, "put", _no_microblock),
        patch.object(PointResponseRegister, "query", _direct_response),
    ):
        start = perf_counter()
        term = (
            ReverseAddPoweredTerm(196, horizon)
            if family == "reverse"
            else PoweredCollatzTerm(27, horizon)
        )
        construction = perf_counter() - start
        start = perf_counter()
        value = term.digit(0)
        cold_seconds = perf_counter() - start
        cold = term.resource_ledger.snapshot()
        start = perf_counter()
        repeat = term.digit(0)
        warm_seconds = perf_counter() - start
        warm = term.resource_ledger.snapshot()
        start = perf_counter()
        width = term.width()
        width_seconds = perf_counter() - start
        before_audit = term.resource_ledger.snapshot()
        start = perf_counter()
        metrics = term.metrics()
        audit_seconds = perf_counter() - start
        audit_unchanged = before_audit == term.resource_ledger.snapshot()
        observed = {name: getattr(metrics, name) for name in METRICS}
    return {
        "family": family,
        "horizon": horizon,
        "pid": os.getpid(),
        "git_source_before": source_before.as_dict(),
        "git_source_after": git_source(ROOT).as_dict(),
        "digit": value,
        "repeat_digit": repeat,
        "width": width,
        "construction_seconds": construction,
        "cold_seconds": cold_seconds,
        "warm_seconds": warm_seconds,
        "width_seconds": width_seconds,
        "audit_seconds": audit_seconds,
        "audit_unchanged": audit_unchanged,
        "cold_counters": cold.counters,
        "counters": before_audit.counters,
        "cold_nodes": cold.nodes,
        "cold_entries": cold.entries,
        "warm_delta": {
            key: value - cold.counters.get(key, 0)
            for key, value in warm.counters.items()
            if value != cold.counters.get(key, 0)
        },
        "metrics": observed,
        "response_and_microblocks_disabled": True,
        "peak_rss_bytes": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        * (1 if sys.platform == "darwin" else 1024),
    }


def _worker_failure(
    family: str,
    horizon: int,
    status: str,
    *,
    returncode: int | None = None,
    stdout: str = "",
    stderr: str = "",
    reason: str = "",
) -> dict[str, object]:
    return {
        "family": family,
        "horizon": horizon,
        "status": status,
        "returncode": returncode,
        "stdout": stdout,
        "stderr": stderr,
        "failure_reason": reason,
    }


def _worker_mapping(value: object) -> Mapping[str, object] | None:
    if type(value) is not dict:
        return None
    return string_keyed_mapping(value)


def _family_report(
    family: str,
    rows: Sequence[Mapping[str, object]],
    horizons: tuple[int, ...],
) -> FamilyProbeReport:
    from devtools.benchmarks.reverse_temporal_power_probe import doubling_envelope

    selected = [row for row in rows if row.get("family") == family]
    passed = [row for row in selected if row.get("status") == "passed"]
    complete = (
        len(selected) == len(horizons)
        and [row.get("horizon") for row in selected] == list(horizons)
        and len(passed) == len(horizons)
        and all(_valid_worker_metrics(row.get("metrics")) for row in passed)
    )
    measurements: list[dict[str, object]] = []
    for row in passed:
        metrics = _worker_mapping(row.get("metrics"))
        if metrics is not None and _valid_worker_metrics(metrics):
            measurements.append({**metrics, "generation": row["horizon"]})
    prefix: list[dict[str, object]] = []
    for horizon, row in zip(horizons, measurements, strict=False):
        if row["generation"] != horizon:
            break
        prefix.append(row)
    observed = {
        field: doubling_envelope(prefix, field) if len(prefix) >= 2 else None
        for field in ENVELOPE_FIELDS
    }
    envelopes = {
        field: observed[field] if complete else None for field in ENVELOPE_FIELDS
    }
    blockers = []
    if not complete:
        blockers.append("measurement_series_incomplete")
    if len(prefix) < 2:
        blockers.append("doubling_evidence_insufficient")
    blockers.extend(
        field + "_exceeds_doubling_envelope"
        for field, accepted in observed.items()
        if accepted is False
    )
    for field in FORBIDDEN_EXECUTION_FIELDS:
        if any(_metric_observed(row, field) for row in passed):
            blockers.append(field + "_observed")
    if any(not _runtime_executed(row) for row in passed):
        blockers.append("powered_tile_execution_not_demonstrated")
    return {
        "family": family,
        "series_complete": complete,
        "measured_doubling_envelopes": envelopes,
        "observed_prefix_doubling_envelopes": observed,
        "observed_prefix_horizons": [row["generation"] for row in prefix],
        "release_blockers": blockers,
        "status": "GREEN" if not blockers else "RED",
    }


def _valid_worker_metrics(value: object) -> bool:
    metrics = _worker_mapping(value)
    if metrics is None:
        return False
    required = (*ENVELOPE_FIELDS, *FORBIDDEN_EXECUTION_FIELDS, *ABSORPTION_FIELDS)
    return all(
        type(metric := metrics.get(field)) is int and metric >= 0 for field in required
    )


def _runtime_executed(row: Mapping[str, object]) -> bool:
    """A small compiler and source tile population cannot prove execution.

    Successful demand must be measured independently from action compilation.
    Full completed roots are intentionally not required for a point probe.
    """
    metrics = _worker_mapping(row.get("metrics"))
    horizon = row.get("horizon")
    if type(horizon) is not int or horizon < 1 or metrics is None:
        return False
    required_span = horizon - 1 if row.get("family") == "reverse" else horizon
    positive_fields = (
        "canonical_tile_nodes",
        "tile_execution_memo_entries",
        "powered_absorption_successes",
        "powered_absorption_max_span",
        "tile_fused_observation_descents",
    )
    values = tuple(metrics.get(field) for field in positive_fields)
    if not all(type(value) is int and value > 0 for value in values):
        return False
    max_span = metrics.get("powered_absorption_max_span")
    return type(max_span) is int and max_span >= required_span


def _metric_observed(row: Mapping[str, object], field: str) -> bool:
    metrics = _worker_mapping(row.get("metrics"))
    return metrics is not None and metrics.get(field, 0) != 0


def run_probe() -> FieldProbeReport:
    before = git_source(ROOT)
    rows: list[dict[str, object]] = []
    for family in ("reverse", "collatz"):
        for horizon in HORIZONS:
            command = [
                sys.executable,
                "-m",
                "devtools.benchmarks.field_query_release_probe",
                "--worker",
                family,
                "--horizon",
                str(horizon),
            ]
            try:
                run = subprocess.run(
                    command,
                    cwd=ROOT,
                    capture_output=True,
                    text=True,
                    check=False,
                )
            except OSError as error:
                row = _worker_failure(
                    family,
                    horizon,
                    "failed",
                    reason=f"worker could not start: {error}",
                )
            else:
                if run.returncode:
                    row = _worker_failure(
                        family,
                        horizon,
                        "failed",
                        returncode=run.returncode,
                        stdout=run.stdout,
                        stderr=run.stderr,
                        reason="worker exited unsuccessfully",
                    )
                else:
                    try:
                        parsed = json.loads(run.stdout)
                    except (json.JSONDecodeError, TypeError) as error:
                        row = _worker_failure(
                            family,
                            horizon,
                            "failed",
                            returncode=run.returncode,
                            stdout=run.stdout,
                            stderr=run.stderr,
                            reason=f"invalid worker JSON: {error}",
                        )
                    else:
                        parsed_fields = _worker_mapping(parsed)
                        if (
                            parsed_fields is None
                            or parsed_fields.get("family") != family
                            or parsed_fields.get("horizon") != horizon
                        ):
                            row = _worker_failure(
                                family,
                                horizon,
                                "failed",
                                returncode=run.returncode,
                                stdout=run.stdout,
                                stderr=run.stderr,
                                reason="worker identified another sample",
                            )
                        elif not _valid_worker_metrics(parsed_fields.get("metrics")):
                            row = _worker_failure(
                                family,
                                horizon,
                                "failed",
                                returncode=run.returncode,
                                stdout=run.stdout,
                                stderr=run.stderr,
                                reason="worker returned missing or invalid metrics",
                            )
                        else:
                            row = dict(parsed_fields)
                            row["status"] = "passed"
            rows.append(row)
            timing = row.get("cold_seconds")
            detail = f"{timing:.4f}s" if type(timing) is float else str(row["status"])
            print(f"{family} N={horizon}: {detail}", flush=True)
    after = git_source(ROOT)
    revision_unchanged = same_git_revision(before, after)
    worker_sources_consistent = all(
        row.get("git_source_before") == row.get("git_source_after") == before.as_dict()
        for row in rows
        if row.get("status") == "passed"
    )
    family_reports = {
        family: _family_report(family, rows, HORIZONS)
        for family in ("reverse", "collatz")
    }
    series_complete = all(
        report["series_complete"] is True for report in family_reports.values()
    )
    observations_valid = all(
        row.get("audit_unchanged") is True
        and row.get("digit") == row.get("repeat_digit")
        for row in rows
        if row.get("status") == "passed"
    )
    accepted = (
        revision_unchanged
        and worker_sources_consistent
        and series_complete
        and observations_valid
        and all(report["status"] == "GREEN" for report in family_reports.values())
    )
    return {
        "metrics_schema_version": METRICS_SCHEMA_VERSION,
        "git_source_before": before.as_dict(),
        "git_source_after": after.as_dict(),
        "git_revision_unchanged": revision_unchanged,
        "evidence_mode": os.environ.get("NUMBER_COMPILER_EVIDENCE_MODE", "development"),
        "cacheable": False,
        "reusable": False,
        "worker_sources_consistent": worker_sources_consistent,
        "collection_complete": len(rows) == 2 * len(HORIZONS),
        "measurement_series_complete": series_complete,
        "scope": "fresh-process point, warm point, then width; audits separately timed",
        "logarithmic_execution_claim": False,
        "status_scope": "measurement-only; not a release completion decision",
        "release_complete": False,
        "invocation_limit_seconds": PYTHON_COMMAND_SECONDS,
        "families": family_reports,
        "status": "GREEN" if accepted else "RED",
        "rows": rows,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--worker", choices=("reverse", "collatz"))
    parser.add_argument("--horizon", type=int)
    args = parser.parse_args()
    if args.worker:
        if args.horizon is None or args.horizon < 1:
            parser.error("a worker requires a positive horizon")
        print(json.dumps(worker(args.worker, args.horizon)))
        return 0
    if args.output is None:
        from devtools.paths import report_output

        args.output = report_output(
            "devtools.benchmarks.field_query_release_probe", "report.json"
        )
    if args.output.exists() or args.output.is_symlink():
        parser.error("historical results must not be overwritten")
    result = run_probe()
    with args.output.open("x") as target:
        json.dump(result, target, indent=2)
        target.write("\n")
    return 0 if result["status"] == "GREEN" else 1


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))

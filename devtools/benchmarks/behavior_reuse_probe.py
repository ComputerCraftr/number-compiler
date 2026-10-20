"""A/B evidence for the certified quiescent profile, not the 196 trajectory.

Both modes use TileScheduler.  Disabling behavioral discharge leaves its exact
causal fallback intact; it does not select a different execution algorithm.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import statistics
import subprocess
import sys
from collections.abc import Mapping, Sequence
from contextlib import ExitStack
from pathlib import Path
from time import perf_counter
from typing import cast
from unittest.mock import patch

from devtools.benchmarks.causal_tile_growth_probe import WORK_FIELDS, runtime
from devtools.git_source import git_source
from devtools.paths import repository_root

ROOT = repository_root()
HORIZONS = (16, 32, 64, 128, 256, 512, 1024)
TOTAL_WORK_COVERAGE = "incomplete instrumented operation vector; not all Python work"

_WORK_COUNTER_SOURCES = {
    **{
        name: name
        for name in WORK_FIELDS
        if name.startswith(
            (
                "future_behavior_",
                "behavior_",
                "exact_causal_",
                "tile_region_",
            )
        )
    },
    "causal_frames": "tile_causal_frames",
    "task_memo_evaluations": "tile_causal_task_memo_evaluations",
    "task_memo_hits": "tile_causal_task_memo_hits",
    "primitive_emits": "tile_causal_primitive_emits",
    "finite_pair_transfers": "tile_causal_finite_pair_transfers",
    "finite_transfer_parent_observations": (
        "tile_causal_finite_transfer_parent_observations"
    ),
    "result_evaluations": "tile_causal_result_evaluations",
    "result_hits": "tile_causal_result_hits",
    "midpoint_reuse": "tile_causal_midpoint_reuse",
    "demand_descents": "tile_scheduler_demand_descents",
    **{
        name: "tile_causal_" + name
        for name in WORK_FIELDS
        if name.startswith(("boundary_output_", "spatial_buffer_"))
    },
    **{
        name: "tile_" + name
        for name in WORK_FIELDS
        if name.startswith(
            (
                "boundary_transfer_",
                "directed_transfer_",
                "causal_frame_",
            )
        )
    },
    "completed_result_port_validation_requests": (
        "completed_result_port_validation_requests"
    ),
    "completed_result_port_validation_visits": (
        "completed_result_port_validation_visits"
    ),
}
if set(_WORK_COUNTER_SOURCES) != set(WORK_FIELDS):
    raise AssertionError("behavior probe work mapping drifted from causal accounting")


def work_vector(counters: dict[str, int]) -> dict[str, int | None]:
    return {
        name: counters.get(source) for name, source in _WORK_COUNTER_SOURCES.items()
    }


def _sample_metric(sample: object, name: str) -> float | None:
    row = cast(dict[str, object], sample)
    if name in WORK_FIELDS:
        vector = cast(dict[str, int | None], row["cold_work_vector"])
        value = vector.get(name)
        return None if value is None else float(value)
    return float(cast(float | int, row[name]))


def _counter_delta(before: int | None, after: int | None) -> int | None:
    return None if before is None or after is None else after - before


def worker(steps: int, width: int, enabled: bool) -> dict[str, object]:
    if type(steps) is not int or steps < 1:
        raise ValueError("behavior probe requires positive exact temporal depth")
    if type(width) is not int or width < 2 or width & (width - 1):
        raise ValueError("behavior probe requires a dyadic width of at least two")
    git_provenance = git_source(ROOT).as_dict()
    start = perf_counter()
    ledger, tiles, adapter, primitive, scheduler = runtime(10)
    alphabet = adapter.alphabet(primitive)
    blank = tiles.alphabet(alphabet).blank
    source = tiles.leaf(alphabet, blank)
    try:
        for _ in range(width.bit_length() - 1):
            following = tiles.join(source.tile, source.tile)
            source.close()
            source = following
        action = adapter.power(primitive, steps)
        with ExitStack() as stack:
            if not enabled:
                for module in ("tile_causal", "tile_causal_api"):
                    stack.enter_context(
                        patch(
                            "number_compiler.hashlife."
                            + module
                            + ".quiescent_boundary",
                            return_value=None,
                        )
                    )
            application = stack.enter_context(
                scheduler.application(
                    action,
                    source.tile,
                    adapter.initial_ports(action),
                    adapter.wiring(action),
                )
            )
            query_start = perf_counter()
            assert application.point(width // 2) == blank
            query_end = perf_counter()
            cold = ledger.snapshot()
            warm_start = perf_counter()
            assert application.point(width - 1) == blank
            assert application.width() == 0
            warm_end = perf_counter()
            after = ledger.snapshot()
            cold_work = work_vector(cold.counters)
            after_work = work_vector(after.counters)
            row: dict[str, object] = {
                "profile": "homogeneous-reverse-blank-output-v1",
                "scope": "private tile runtime, uniform blank original source",
                "public_196_cutover_evidence": False,
                "enabled": enabled,
                "steps": steps,
                "width": width,
                "pid": os.getpid(),
                "git_source": git_provenance,
                "evidence_mode": "development",
                "cacheable": False,
                "cold_seconds": query_end - start,
                "query_seconds": query_end - query_start,
                "warm_point_and_width_seconds": warm_end - warm_start,
                "cold_counters": dict(cold.counters),
                "cold_work_vector": cold_work,
                "warm_work_vector": {
                    name: _counter_delta(value, after_work[name])
                    for name, value in cold_work.items()
                },
                "total_work_coverage": TOTAL_WORK_COVERAGE,
                "live_entries": cold.entries,
                "live_nodes": cold.nodes,
                "peak_entries": cold.peak_entries,
                "peak_nodes": cold.peak_nodes,
            }
    finally:
        source.close()
    return row


def fresh_series(output: Path, width: int) -> None:
    records: list[dict[str, object]] = []
    git_provenance = git_source(ROOT).as_dict()
    for enabled in (True, False):
        for steps in HORIZONS:
            for trial in range(5):
                command = [
                    sys.executable,
                    "-m",
                    "devtools.benchmarks.behavior_reuse_probe",
                    "--worker",
                    "--steps",
                    str(steps),
                    "--width",
                    str(width),
                ]
                if not enabled:
                    command.append("--disabled")
                try:
                    result = subprocess.run(
                        command,
                        cwd=ROOT,
                        capture_output=True,
                        text=True,
                        check=True,
                    )
                    row = json.loads(result.stdout)
                    status = (
                        "complete"
                        if row["git_source"] == git_provenance
                        else "git_state_changed"
                    )
                except (subprocess.SubprocessError, ValueError, KeyError) as error:
                    row, status = {"error": str(error)}, "incomplete"
                records.append(
                    {
                        "enabled": enabled,
                        "steps": steps,
                        "trial": trial,
                        "status": status,
                        "row": row,
                    }
                )
                # Interrupted series retain every completed sample as evidence.
                output.write_text(
                    json.dumps(
                        {
                            "git_source": git_provenance,
                            "evidence_mode": "development",
                            "cacheable": False,
                            "records": records,
                            "summary": summarize(records),
                        },
                        indent=2,
                    )
                    + "\n"
                )


def summarize(records: Sequence[Mapping[str, object]]) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for enabled in (True, False):
        previous: dict[str, float] = {}
        for steps in HORIZONS:
            samples = [
                item["row"]
                for item in records
                if item["enabled"] == enabled
                and item["steps"] == steps
                and item["status"] == "complete"
            ]
            if len(samples) != 5:
                rows.append(
                    {
                        "enabled": enabled,
                        "steps": steps,
                        "classification": "insufficient evidence",
                    }
                )
                previous = {}
                continue
            assert all(isinstance(item, dict) for item in samples)
            metrics: dict[str, dict[str, float | str | None]] = {}
            for name in (
                "cold_seconds",
                "query_seconds",
                "live_entries",
                "live_nodes",
                *WORK_FIELDS,
            ):
                values = [_sample_metric(item, name) for item in samples]
                available = [value for value in values if value is not None]
                if len(available) != len(values):
                    metrics[name] = {
                        "status": "unavailable",
                        "median": None,
                        "minimum": None,
                        "maximum": None,
                        "increment": None,
                        "doubling_ratio": None,
                        "effective_exponent": None,
                    }
                    previous.pop(name, None)
                    continue
                median = statistics.median(available)
                old = previous.get(name)
                metrics[name] = {
                    "median": median,
                    "minimum": min(available),
                    "maximum": max(available),
                    "increment": None if old is None else median - old,
                    "doubling_ratio": None if not old else median / old,
                    "effective_exponent": None
                    if not old or median <= 0
                    else math.log2(median / old),
                }
                previous[name] = median
            rows.append(
                {
                    "enabled": enabled,
                    "steps": steps,
                    "metrics": metrics,
                    "total_work_coverage": TOTAL_WORK_COVERAGE,
                    "classification": (
                        "profile-specific operation vector; no total-work scaling claim"
                    ),
                }
            )
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worker", action="store_true")
    parser.add_argument("--disabled", action="store_true")
    parser.add_argument("--steps", type=int, default=16)
    parser.add_argument("--width", type=int, default=16)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.worker:
        print(json.dumps(worker(args.steps, args.width, not args.disabled)))
    elif args.output is not None:
        fresh_series(args.output, args.width)
    else:
        parser.error("choose --worker or --output")


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))

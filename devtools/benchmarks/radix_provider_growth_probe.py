"""Fresh-process general radix work, bypassing microblocks and response registers."""

from __future__ import annotations

import argparse
import json
import resource
import subprocess
import sys
from pathlib import Path
from time import perf_counter
from typing import Any

from devtools.checks.test_run_evidence import source_fingerprint
from devtools.paths import repository_root
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm

ROOT = repository_root()


def cold_row(coordinate: int) -> dict[str, Any]:
    exact = 140137
    for _ in range(11):
        exact = 3 * exact + 1 if exact & 1 else exact // 2
    term = PoweredCollatzTerm(140137, 11)
    start = perf_counter()
    try:
        value: int | None = term.radix_digit(3, coordinate)
    except IndexError:
        value = None
    elapsed = perf_counter() - start
    quotient = exact // 3**coordinate  # Independent explicit test oracle.
    expected = quotient % 3 if quotient else None
    if value != expected:
        raise AssertionError((coordinate, value, expected))
    audit_start = perf_counter()
    metrics = term.metrics()
    audit_elapsed = perf_counter() - audit_start
    work, snapshot = term._ledger.counters, term._ledger.snapshot()
    peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    row = {
        "coordinate": coordinate,
        "digit": value,
        "observation_seconds": elapsed,
        "metrics_and_audit_seconds": audit_elapsed,
        "process_peak_rss_bytes": peak * (1 if sys.platform == "darwin" else 1024),
        "scheduler_frames": work.get("tile_causal_frames", 0),
        "completed_result_requests": work.get("completed_result_requests", 0),
        "completed_result_hits": work.get("completed_result_early_hits", 0),
        "causal_boundary_requests": work.get("tile_causal_boundary_output_requests", 0),
        "causal_boundary_publications": work.get(
            "tile_causal_boundary_output_completions", 0
        ),
        "radix_interface_observations": work.get(
            "tile_radix_interface_observations", 0
        ),
        "radix_action_applications": work.get("tile_radix_observation_publications", 0),
        "all_work_counters": dict(work),
        "retained_nodes": snapshot.nodes,
        "retained_entries": snapshot.entries,
        "forbidden_future_payloads": metrics.forbidden_future_payloads,
        "accounting_mismatch": metrics.resource_accounting_mismatch,
    }
    if metrics.forbidden_future_payloads or metrics.resource_accounting_mismatch:
        raise AssertionError(row)
    return row


def run_probe() -> dict[str, Any]:
    fingerprint = source_fingerprint(ROOT)
    rows = []
    for coordinate in (0, 5, 10, 15):
        process = subprocess.run(
            [
                sys.executable,
                "-m",
                "devtools.benchmarks.radix_provider_growth_probe",
                "--worker",
                str(coordinate),
            ],
            check=True,
            capture_output=True,
            text=True,
            timeout=35,
        )
        rows.append(json.loads(process.stdout))
    after = source_fingerprint(ROOT)
    return {
        "schema": 6,
        "source_before": fingerprint,
        "source_after": after,
        "source_unchanged": fingerprint == after,
        "seed": 140137,
        "physical_ticks": 11,
        "radix": 3,
        "response_register_enabled": False,
        "microblocks_enabled": False,
        "universal_sublinear_execution_proved": False,
        "fresh_process_per_coordinate": True,
        "rows": rows,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--worker", type=int, choices=(0, 5, 10, 15))
    args = parser.parse_args()
    if args.worker is not None:
        print(json.dumps(cold_row(args.worker)))
        return
    if args.output is None:
        parser.error("--output is required")
    if args.output.exists():
        parser.error("preserve historical results: choose a new output path")
    result = run_probe()
    args.output.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))

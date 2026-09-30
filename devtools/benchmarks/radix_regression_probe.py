"""Five isolated trials of the fixed original-source ternary regression.

Run: python -m devtools.benchmarks.radix_regression_probe --output NEW.json
The .25s cold and .01s repeat limits are fixed, including phase watchdogs.
Construction and read-only inventory audit have separate clocks. This route
uses the original-input ternary identity for odd physical C1, not a full
HashLife executor. Existing evidence files are never overwritten.
"""

from __future__ import annotations

import argparse
import json
import logging
import os
import resource
import signal
import statistics
import subprocess
import sys
from collections.abc import Callable
from dataclasses import fields
from datetime import UTC, datetime
from pathlib import Path
from time import perf_counter, process_time
from typing import Any

from devtools.checks.test_run_evidence import source_fingerprint
from devtools.paths import report_output, repository_root
from number_compiler.projection.lazy_radix import collatz_radix_digit
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm

ROOT = repository_root()
SEED = (1 << 95) + 0x123456789ABCDEF12345
TRIALS = 5
COLD_LIMIT = 0.25
REPEAT_LIMIT = 0.01
_LOGGER = logging.getLogger(__name__)


class PhaseTimeout(TimeoutError):
    pass


def measured(
    operation: Callable[[], Any], limit: float | None = None
) -> tuple[Any, dict[str, Any]]:
    def expired(signum: object, frame: object) -> None:
        raise PhaseTimeout(f"query exceeded its fixed {limit}s acceptance limit")

    old_handler = signal.signal(signal.SIGALRM, expired) if limit is not None else None
    start, cpu = perf_counter(), process_time()
    try:
        if limit is not None:
            signal.setitimer(signal.ITIMER_REAL, limit)
        value = operation()
        status, error = "ok", None
    except Exception as exc:
        _LOGGER.debug("radix regression trial failed", exc_info=True)
        value = None
        status = "timeout" if isinstance(exc, PhaseTimeout) else "error"
        error = f"{type(exc).__name__}: {exc}"
    finally:
        seconds, cpu_seconds = perf_counter() - start, process_time() - cpu
        if limit is not None:
            signal.setitimer(signal.ITIMER_REAL, 0)
            signal.signal(signal.SIGALRM, old_handler)
    return value, {
        "status": status,
        "seconds": seconds,
        "cpu_seconds": cpu_seconds,
        "limit_seconds": limit,
        "error": error,
    }


def snapshot(term: PoweredCollatzTerm) -> dict[str, Any]:
    actual = term._ledger.snapshot()
    inventory = [
        {
            item.name: getattr(row, item.name)
            for item in fields(row)
            if item.name != "roots"
        }
        | {
            "accounting_delta": row.accounting_delta,
            "roots": [
                {
                    "kind": ref.kind,
                    "local_id": ref.local_id,
                    "owner_label": ref.owner.label,
                }
                for ref in row.roots
            ],
        }
        for row in actual.inventory
    ]
    return {
        "entries": actual.entries,
        "nodes": actual.nodes,
        "peak_entries": actual.peak_entries,
        "peak_nodes": actual.peak_nodes,
        "observed_entries": sum(row.observed_entries or 0 for row in actual.inventory),
        "observed_nodes": sum(row.observed_nodes or 0 for row in actual.inventory),
        "counters": actual.counters,
        "inventory": inventory,
    }


def query(
    term: PoweredCollatzTerm, limit: float, before: dict[str, Any]
) -> dict[str, Any]:
    value, result = measured(lambda: collatz_radix_digit(term, 3, 3), limit)
    after = snapshot(term)
    result.update(
        value=value,
        snapshot=after,
        counter_delta={
            name: count - before["counters"].get(name, 0)
            for name, count in after["counters"].items()
            if count != before["counters"].get(name, 0)
        },
    )
    return result


def trial_passes(row: dict[str, Any]) -> bool:
    if (
        not row.get("source_unchanged")
        or row.get("construction", {}).get("status") != "ok"
    ):
        return False
    for phase, limit in (("cold", COLD_LIMIT), ("repeat", REPEAT_LIMIT)):
        observed = row.get(phase, {})
        if (
            observed.get("status") != "ok"
            or observed.get("value") != 2
            or type(observed.get("seconds")) not in (int, float)
            or not 0 <= observed["seconds"] <= limit
        ):
            return False
    audit = row.get("audit", {})
    return (
        audit.get("status") == "ok"
        and audit.get("ledger_unchanged") is True
        and audit.get("resource_audit_complete") == 1
        and audit.get("representation_boundary_complete") == 1
        and audit.get("forbidden_future_payloads") == 0
        and row.get("no_response_or_microblock_assistance") is True
    )


def worker() -> dict[str, Any]:
    fingerprint = source_fingerprint(ROOT)
    term, construction = measured(
        lambda: PoweredCollatzTerm(
            SEED, 1, max_context_nodes=5000, max_cache_entries=10000
        )
    )
    row: dict[str, Any] = {
        "pid": os.getpid(),
        "source_before": fingerprint,
        "construction": construction,
    }
    if term is not None:
        construction["snapshot"] = snapshot(term)
        row["cold"] = query(term, COLD_LIMIT, construction["snapshot"])
        if row["cold"]["status"] == "ok":
            row["repeat"] = query(term, REPEAT_LIMIT, row["cold"]["snapshot"])
        else:
            row["repeat"] = {
                "status": "unavailable",
                "seconds": None,
                "value": None,
                "reason": "cold query did not complete",
            }
        before_audit = term._ledger.snapshot()
        report, audit = measured(lambda: collect_ledger_metrics(term._ledger))
        audit["ledger_unchanged"] = term._ledger.snapshot() == before_audit
        if report is not None:
            for name in (
                "resource_audit_complete",
                "representation_boundary_complete",
                "forbidden_future_payloads",
                "resource_unregistered_containers",
                "resource_accounting_mismatch",
                "exact_endpoint_nodes",
                "explicitly_lowered_digits",
                "retained_point_response_scalars",
                "exact_microblock_entries",
            ):
                audit[name] = getattr(report, name)
        row["audit"] = audit
        projection = term._radix_projections.get(3)
        counters = term._ledger.counters
        row["no_response_or_microblock_assistance"] = bool(
            projection is not None
            and projection._native_source is not None
            and projection._fused is None
            and not any(
                count
                for name, count in counters.items()
                if name.startswith("point_response_") or "microblock" in name
            )
            and report is not None
            and report.retained_point_response_scalars == 0
            and report.exact_microblock_entries == 0
        )
    row["source_after"] = source_fingerprint(ROOT)
    row["source_unchanged"] = row["source_after"] == fingerprint
    row["process_peak_rss_bytes"] = resource.getrusage(
        resource.RUSAGE_SELF
    ).ru_maxrss * (1 if sys.platform == "darwin" else 1024)
    row["status"] = "PASS" if trial_passes(row) else "FAIL"
    return row


def run_trials() -> dict[str, Any]:
    before = source_fingerprint(ROOT)
    rows = []
    environment = dict(os.environ)
    environment.pop("PYTHONPATH", None)
    environment.pop("MYPYPATH", None)
    for index in range(TRIALS):
        completed = subprocess.run(
            [
                sys.executable,
                "-m",
                "devtools.benchmarks.radix_regression_probe",
                "--worker",
            ],
            cwd=ROOT,
            env=environment,
            capture_output=True,
            text=True,
            check=False,
        )
        try:
            row = json.loads(completed.stdout)
        except (ValueError, TypeError):
            row = {
                "status": "FAIL",
                "error": "worker produced no valid measurement record",
                "stdout": completed.stdout,
            }
        row.update(
            trial=index + 1,
            process_returncode=completed.returncode,
            stderr=completed.stderr,
        )
        rows.append(row)
    after = source_fingerprint(ROOT)
    unchanged = before == after and all(
        row.get("source_before") == before and row.get("source_after") == before
        for row in rows
    )
    accepted = unchanged and all(
        row["process_returncode"] == 0 and trial_passes(row) for row in rows
    )
    medians = {}
    for phase in ("construction", "cold", "repeat", "audit"):
        values = [row.get(phase, {}).get("seconds") for row in rows]
        medians[phase] = (
            statistics.median(values)
            if all(type(value) in (int, float) for value in values)
            else None
        )
    return {
        "schema_version": 1,
        "status": "PASS" if accepted else "FAIL",
        "scope": "fixed regression only; original-source ternary law for odd physical C1",
        "full_hashlife_cutover_evidence": False,
        "historical_evidence": "results/radix_original_source_v1.json",
        "created_utc": datetime.now(UTC).isoformat(),
        "fixture": {
            "seed_expression": "(1<<95)+0x123456789ABCDEF12345",
            "seed": str(SEED),
            "steps": 1,
            "radix": 3,
            "digit": 3,
            "max_context_nodes": 5000,
            "max_cache_entries": 10000,
        },
        "fresh_process_trials": TRIALS,
        "cold_limit_seconds": COLD_LIMIT,
        "repeat_limit_seconds": REPEAT_LIMIT,
        "timing_method": "perf_counter and process_time; imports, fingerprints and audits outside query timers",
        "counter_units": "runtime operation counts and named high-water marks; deltas of maxima are not additive work",
        "source_before": before,
        "source_after": after,
        "source_unchanged": unchanged,
        "median_seconds": medians,
        "rows": rows,
    }


def write_result(path: Path, result: dict[str, Any]) -> None:
    # Exclusive creation protects historical evidence even through symlinks.
    with path.open("x") as target:
        json.dump(result, target, indent=2)
        target.write("\n")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--worker", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.worker:
        row = worker()
        print(json.dumps(row))
        return 0 if row["status"] == "PASS" else 1
    if args.output is None:
        args.output = report_output(
            "devtools.benchmarks.radix_regression_probe",
            "radix_regression_probe_v1.json",
        )
    if args.output.exists() or args.output.is_symlink():
        parser.error("refusing to overwrite existing or historical evidence")
    result = run_trials()
    write_result(args.output, result)
    print(
        json.dumps(
            {
                "status": result["status"],
                "output": str(args.output),
                "median_seconds": result["median_seconds"],
            }
        )
    )
    return 0 if result["status"] == "PASS" else 1


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))

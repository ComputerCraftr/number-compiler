"""Capped fresh-process profiles of the candidate higher diamond evaluator.

This measures direct parametric queries, with no point-response register or
cycle adapter. A failed phase has no fabricated result, work, or timing value.
All representation snapshots happen after the corresponding query timer stops.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import logging
import os
import resource
import subprocess
import sys
from collections.abc import Callable
from dataclasses import asdict, fields
from pathlib import Path
from time import perf_counter, process_time
from typing import Any

from devtools.checks.validation_policy import (
    PYTHON_COMMAND_SECONDS,
    PYTHON_MEMORY_BYTES,
)
from devtools.git_source import git_source
from devtools.paths import repository_root
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.hashlife.observation.diamond_parametric_query import (
    parametric_point,
    parametric_width,
)
from number_compiler.hashlife.observation.diamond_query import DiamondApplication
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

ROOT = repository_root()
CACHE_ENTRIES = 180_000
STEPS = (16, 32, 64, 128, 256)
WIDTHS = (16, 32, 64, 128, 256, 512)
_LOGGER = logging.getLogger(__name__)


def rss_bytes() -> int:
    return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * (
        1 if sys.platform == "darwin" else 1024
    )


def measured(operation: Callable[[], object]) -> dict[str, Any]:
    start, cpu = perf_counter(), process_time()
    try:
        value = operation()
        status, error = "ok", None
    except (TimeoutError, BlockContextBudgetExceeded) as exc:
        value = None
        status = "timeout" if isinstance(exc, TimeoutError) else "budget_exceeded"
        error = f"{type(exc).__name__}: {exc}"
    except Exception as exc:
        _LOGGER.debug("benchmark phase failed", exc_info=True)
        value, status, error = None, "error", f"{type(exc).__name__}: {exc}"
    elapsed, consumed = perf_counter() - start, process_time() - cpu
    return {
        "status": status,
        "result": value,
        "seconds": elapsed,
        "cpu_seconds": consumed,
        "error": error,
        "process_peak_rss_bytes": rss_bytes(),
    }


def inventory(ledger: ResourceLedger) -> dict[str, Any]:
    report = collect_ledger_metrics(ledger)
    result = {
        field.name: getattr(report, field.name)
        for field in fields(report)
        if field.name != "resource_inventory"
    }
    result["temporal_diagnostics"] = asdict(report.temporal_diagnostics)
    result["resource_inventory"] = [
        {
            field.name: getattr(row, field.name)
            for field in fields(row)
            if field.name != "roots"
        }
        | {
            "roots": [
                {
                    "kind": root.kind,
                    "local_id": root.local_id,
                    "owner_label": root.owner.label,
                }
                for root in row.roots
            ]
        }
        for row in report.resource_inventory
    ]
    return result


def source_seed(family: str, width: int | None) -> int:
    if family == "collatz":
        return (1 << (513 if width is None else width)) - 1
    if width is None:
        return 196
    return int("".join(str(1 + (7 * index) % 9) for index in range(width)))


def construct(
    family: str,
    steps: int,
    seed: int,
    ledger: ResourceLedger,
) -> tuple[ReverseAddPoweredTerm | DiamondApplication, int, ResourceLedger]:
    if family == "reverse":
        from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

        application = ReverseAddPoweredTerm(
            seed, steps, max_cache_entries=CACHE_ENTRIES
        )
        return application, application.maximum_width, application._ledger
    from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
    from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
    from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )
    from number_compiler.hashlife.observation.diamond_query import DiamondApplication
    from number_compiler.sequences.collatz.compilation import (
        compile_physical_diamond,
    )

    compiler = LazyCompiler(ledger)
    digits = tuple((seed >> index) & 1 for index in range(seed.bit_length()))
    extent = len(digits) + steps + 8
    source = SourceGeometry(
        ledger, ExactSource(digits, 2, blank=2, extent=extent, alphabet_size=2)
    )
    source.span(digits, 2, extent)
    runtime = DiamondRuntime(compiler, source)
    root = compile_physical_diamond(compiler, runtime.actions, steps)
    # DiamondApplication owns the actual composition certificate, but its point
    # method/cycle shortcut is not called by this benchmark.
    app = DiamondApplication(runtime, root)
    return app, extent, ledger


def oracle(family: str, seed: int, steps: int) -> tuple[int, int, int]:
    """Scalar proof computation only after every measured production query."""
    value = seed
    for _ in range(steps):
        value = (
            value + int(str(value)[::-1])
            if family == "reverse"
            else value // 2
            if value % 2 == 0
            else 3 * value + 1
        )
    base = 10 if family == "reverse" else 2
    width = len(str(value)) if family == "reverse" else max(1, value.bit_length())
    return value % base, value // base % base, width


def worker(family: str, steps: int, width: int | None = None) -> dict[str, Any]:
    source = git_source(ROOT)
    seed = source_seed(family, width)
    ledger = ResourceLedger(max_cache_entries=CACHE_ENTRIES)
    phases: list[dict[str, Any]] = []
    built: list[
        tuple[ReverseAddPoweredTerm | DiamondApplication, int, ResourceLedger]
    ] = []

    def build() -> None:
        nonlocal ledger
        application, extent, application_ledger = construct(family, steps, seed, ledger)
        built.append((application, extent, application_ledger))
        ledger = application_ledger

    def phase(name: str, operation: Callable[[], object]) -> bool:
        before = dict(ledger.counters)
        previous_entries, previous_nodes = ledger.entries, ledger.nodes
        row = measured(operation)
        row["name"] = name
        row["work_delta"] = {
            key: value - before.get(key, 0)
            for key, value in ledger.counters.items()
            if value != before.get(key, 0)
        }
        row["retained_entries"] = ledger.entries
        row["retained_nodes"] = ledger.nodes
        row["retained_entry_delta"] = ledger.entries - previous_entries
        row["retained_node_delta"] = ledger.nodes - previous_nodes
        row["audit"] = measured(lambda: inventory(ledger))
        phases.append(row)
        return bool(row["status"] == "ok")

    ready = phase("construction", build)
    for name, position in (
        ("point_0_cold", 0),
        ("point_0_repeat", 0),
        ("point_1", 1),
        ("point_0_revisit", 0),
        ("active_width", None),
    ):
        if ready:
            application, extent, _ = built[0]

            def operation(
                application: ReverseAddPoweredTerm | DiamondApplication = application,
                position: int | None = position,
                extent: int = extent,
            ) -> int:
                if family == "reverse":
                    assert isinstance(application, ReverseAddPoweredTerm)
                    return (
                        application.width()
                        if position is None
                        else application.digit(position)
                    )
                assert isinstance(application, DiamondApplication)
                if position is None:
                    return parametric_width(
                        application.runtime,
                        application.root,
                        application.observer,
                        extent,
                    )
                return parametric_point(application.runtime, application.root, position)

            ready = phase(name, operation)
        else:
            phases.append(
                {
                    "name": name,
                    "status": "skipped",
                    "result": None,
                    "seconds": None,
                    "cpu_seconds": None,
                    "work_delta": None,
                    "audit": None,
                    "reason": "an earlier phase failed",
                }
            )
    expected_first, expected_second, expected_width = oracle(family, seed, steps)
    for row in phases:
        if row["status"] == "ok" and row["name"] != "construction":
            expected = (
                expected_width
                if row["name"] == "active_width"
                else expected_second
                if row["name"] == "point_1"
                else expected_first
            )
            row["expected"] = expected
            row["exact"] = row["result"] == expected
    audits = [row["audit"] for row in phases if row.get("audit") is not None]
    audit_complete = all(
        audit["status"] == "ok"
        and audit["result"]["representation_boundary_complete"] == 1
        for audit in audits
    )
    exact = all(row.get("exact", True) for row in phases)
    blockers = ["execution_phase_failed"] if not ready else []
    blockers += [] if audit_complete else ["representation_audit_failed_or_incomplete"]
    blockers += [] if exact else ["incorrect_observation"]
    return {
        "family": family,
        "steps": steps,
        "requested_source_width": width,
        "source_width": len(str(seed)) if family == "reverse" else seed.bit_length(),
        "source_sha256": hashlib.sha256(str(seed).encode()).hexdigest(),
        "status": "blocked" if blockers else "completed",
        "blockers": blockers,
        "execution_completed": ready,
        "exact_completed_observations": exact,
        "representation_audits_complete": audit_complete,
        "extent": built[0][1] if built else None,
        "phases": phases,
        "pid": os.getpid(),
        "git_source": source.as_dict(),
        "evidence_mode": "development",
        "cacheable": False,
    }


def fresh_case(family: str, steps: int, width: int | None) -> dict[str, Any]:
    command = [
        sys.executable,
        "-m",
        "devtools.benchmarks.diamond_parametric_profile",
        "--worker",
        "--family",
        family,
        "--steps",
        str(steps),
    ]
    if width is not None:
        command.extend(("--width", str(width)))
    environment = dict(os.environ)
    completed = subprocess.run(
        command,
        cwd=ROOT,
        env=environment,
        text=True,
        capture_output=True,
        check=False,
    )
    if completed.returncode:
        return {
            "family": family,
            "steps": steps,
            "requested_source_width": width,
            "status": "worker_error",
            "phases": None,
            "result": None,
            "exit_code": completed.returncode,
            "stderr": completed.stderr[-4000:],
        }
    decoded: object = json.loads(completed.stdout)
    if not isinstance(decoded, dict) or any(
        not isinstance(key, str) for key in decoded
    ):
        raise ValueError("worker report must be a JSON object with string keys")
    return decoded


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--family", choices=("reverse", "collatz", "all"), default="all"
    )
    parser.add_argument("--series", choices=("temporal", "width", "all"), default="all")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--worker", action="store_true")
    parser.add_argument("--steps", type=int, default=4)
    parser.add_argument("--width", type=int)
    args = parser.parse_args()
    if args.worker:
        if args.family == "all":
            parser.error("worker requires one family")
        print(json.dumps(worker(args.family, args.steps, args.width), sort_keys=True))
        return
    rows = []
    for family in ("reverse", "collatz") if args.family == "all" else (args.family,):
        cases: list[tuple[int, int | None]] = []
        if args.series in ("temporal", "all"):
            cases.extend((steps, None) for steps in STEPS)
        if args.series in ("width", "all"):
            cases.extend((4, width) for width in WIDTHS)
        for steps, width in cases:
            row = fresh_case(family, steps, width)
            rows.append(row)
            print(
                f"{family} N={steps} width={width}: {row['status']}",
                file=sys.stderr,
                flush=True,
            )
    report = {
        "profile_schema": 1,
        "candidate": "direct higher parametric diamond queries",
        "limits": {
            "command_seconds": PYTHON_COMMAND_SECONDS,
            "memory_bytes": PYTHON_MEMORY_BYTES,
            "cache_entries": CACHE_ENTRIES,
        },
        "timing_scope": "query only; audits excluded; concurrent external validation may affect wall time",
        "rss_scope": "fresh worker lifetime, including preceding audits; not additive workspace bytes",
        "response_register": False,
        "scalar_oracle_scope": "after all measured production queries",
        "performance_release_status": (
            "BLOCKED"
            if any(row["status"] != "completed" for row in rows)
            else "MEASURED_WITHIN_FIXED_CAPS"
        ),
        "rows": rows,
    }
    encoded = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output is None:
        print(encoded, end="")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded)


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))

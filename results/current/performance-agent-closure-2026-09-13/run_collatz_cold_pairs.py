from pathlib import Path
from dataclasses import asdict
import json
import sys
import statistics

sys.path.insert(0, str(Path.cwd()))
from devtools.checks.process_guard import run_guarded
from devtools.checks.test_run_evidence import source_fingerprint

out = Path("results/current/performance-agent-closure-2026-09-13")
py = sys.executable
base = "/tmp/prime-source-wheels-owned/number_compiler-0.59.9-py3-none-any.whl"
candidate = "/tmp/performance-agent-final-wheel/number_compiler-0.59.9-py3-none-any.whl"
before = source_fingerprint(Path.cwd())
rows = []
for trial in range(1, 6):
    name = f"cold-collatz-pair-{trial}"
    command = [
        py,
        "-m",
        "devtools.benchmarks.cli_startup",
        base,
        candidate,
        "--samples",
        "1",
        "--case",
        "collatz",
    ]
    result = run_guarded(
        tuple(command), output=out / (name + ".log"), timeout=35, memory_bytes=1024**3
    )
    report = asdict(result)
    report.update(
        command=command,
        source_before=before,
        source_after=source_fingerprint(Path.cwd()),
    )
    (out / (name + ".guard.json")).write_text(json.dumps(report, indent=2) + "\n")
    print(
        json.dumps(
            {
                "check": name,
                "outcome": result.outcome,
                "elapsed": result.elapsed_seconds,
            }
        ),
        flush=True,
    )
    if report["source_after"] != before:
        raise RuntimeError("source changed")
    if result.outcome == "completed":
        rows.append(json.loads((out / (name + ".log")).read_text())["rows"][0])
summary = {
    "collection_complete": len(rows) == 5,
    "source_fingerprint": before,
    "trials": rows,
    "scope": "five independently guarded fresh-process pairs; original combined 35-second probe still timed out",
}
if rows:
    summary["baseline_median_seconds"] = statistics.median(
        r["baseline_median_seconds"] for r in rows
    )
    summary["candidate_median_seconds"] = statistics.median(
        r["candidate_median_seconds"] for r in rows
    )
(out / "cold-collatz-pairs.json").write_text(json.dumps(summary, indent=2) + "\n")

from pathlib import Path
from dataclasses import asdict
import json
import sys

sys.path.insert(0, str(Path.cwd()))
from devtools.checks.process_guard import run_guarded
from devtools.checks.test_run_evidence import source_fingerprint

out = Path("results/current/performance-agent-closure-2026-09-13")
py = sys.executable
base = "/tmp/prime-source-wheels-owned/number_compiler-0.59.9-py3-none-any.whl"
candidate = "/tmp/performance-agent-final-wheel/number_compiler-0.59.9-py3-none-any.whl"
checks = [
    (
        f"cold-{family}",
        [
            py,
            "-m",
            "devtools.benchmarks.cli_startup",
            base,
            candidate,
            "--samples",
            "5",
            "--case",
            family,
        ],
        35,
        1024,
    )
    for family in ("196", "collatz", "antihydra")
]
checks += [
    (
        f"isabelle-{session}",
        [
            "/Applications/Isabelle2025-2.app/bin/isabelle",
            "build",
            "-d",
            "devtools/proofs/isabelle",
            "-o",
            "threads=1",
            session,
        ],
        35,
        4096,
    )
    for session in (
        "Reverse_Residuals",
        "Temporal_Clock_Jumps",
        "Etale_Primary_Carry",
        "Antihydra",
    )
]
checks += [
    ("whole-tree-mypy", [py, "-m", "mypy", "."], 35, 1024),
    ("whole-tree-ruff", [py, "-m", "ruff", "check", "."], 35, 1024),
]
before = source_fingerprint(Path.cwd())
for name, command, seconds, memory in checks:
    result = run_guarded(
        tuple(command),
        output=out / (name + ".log"),
        timeout=seconds,
        memory_bytes=memory * 1024**2,
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
                "returncode": result.child_returncode,
                "elapsed": result.elapsed_seconds,
            }
        ),
        flush=True,
    )
    if report["source_after"] != before:
        raise RuntimeError("source changed")

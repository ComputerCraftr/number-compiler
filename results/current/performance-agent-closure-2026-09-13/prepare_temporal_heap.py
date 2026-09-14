import json
import sys
from dataclasses import asdict
from pathlib import Path

sys.path.insert(0, str(Path.cwd()))
from devtools.checks.process_guard import run_guarded
from devtools.checks.test_run_evidence import source_fingerprint

out = Path("results/current/performance-agent-closure-2026-09-13")
before = source_fingerprint(Path.cwd())
for name, extra, session in [
    ("isabelle-reverse-heap", ["-b"], "Reverse_Residuals"),
    ("isabelle-temporal-prebuilt", [], "Temporal_Clock_Jumps"),
]:
    command = [
        "/Applications/Isabelle2025-2.app/bin/isabelle",
        "build",
        *extra,
        "-d",
        "devtools/proofs/isabelle",
        "-o",
        "threads=1",
        session,
    ]
    r = run_guarded(
        tuple(command),
        output=out / (name + ".log"),
        timeout=35,
        memory_bytes=4 * 1024**3,
    )
    data = asdict(r)
    data.update(
        command=command,
        source_before=before,
        source_after=source_fingerprint(Path.cwd()),
    )
    (out / (name + ".guard.json")).write_text(json.dumps(data, indent=2) + "\n")
    print(
        json.dumps({"check": name, "outcome": r.outcome, "elapsed": r.elapsed_seconds}),
        flush=True,
    )
    if r.outcome != "completed":
        break

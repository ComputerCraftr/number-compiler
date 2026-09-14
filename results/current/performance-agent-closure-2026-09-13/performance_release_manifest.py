"""Run the unchanged causal release manifest with each worker resource guarded."""

from pathlib import Path
import json
import subprocess
import sys
from dataclasses import asdict
from types import SimpleNamespace

sys.path.insert(0, str(Path.cwd()))
from devtools.benchmarks import causal_tile_growth_runner as runner
from devtools.checks.process_guard import run_guarded

destination = Path(sys.argv[1]).resolve()
destination.mkdir(parents=True, exist_ok=False)
sequence = 0


def guarded_run(command, *, cwd, env, capture_output, text, check, timeout):
    global sequence
    sequence += 1
    stem = destination / f"trial-{sequence:03}"
    guard = run_guarded(
        tuple(command),
        output=stem.with_suffix(".log"),
        timeout=timeout,
        memory_bytes=1024**3,
    )
    stem.with_suffix(".guard.json").write_text(
        json.dumps(asdict(guard), indent=2) + "\n"
    )
    output = stem.with_suffix(".log").read_text()
    print(
        json.dumps(
            {
                "sample": sequence,
                "command": command[3:],
                "guard": guard.outcome,
                "seconds": guard.elapsed_seconds,
            }
        ),
        flush=True,
    )
    if guard.outcome == "timeout":
        raise subprocess.TimeoutExpired(
            command, timeout, output=output, stderr="guard timeout"
        )
    status = (
        guard.child_returncode
        if guard.outcome == "completed"
        else (guard.child_returncode or 1)
    )
    return subprocess.CompletedProcess(
        command, status, output, "" if guard.outcome == "completed" else guard.outcome
    )


# Only the benchmark runner's invocation is adapted; process_guard's own
# process inventory continues to use the ordinary subprocess module.
runner.subprocess = SimpleNamespace(
    run=guarded_run, TimeoutExpired=subprocess.TimeoutExpired
)
report = runner.run_fresh_process_probe()
report["worker_memory_limit_bytes"] = 1024**3
report["guarded_samples"] = sequence
(destination / "report.json").write_text(json.dumps(report, indent=2) + "\n")
print(
    json.dumps(
        {
            "status": report["status"],
            "samples": sequence,
            "complete": report["collection_complete"],
        }
    ),
    flush=True,
)

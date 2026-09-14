import json
import sys
from dataclasses import asdict
from pathlib import Path

sys.path.insert(0, str(Path.cwd()))
from devtools.checks.process_guard import run_guarded
from devtools.checks.test_run_evidence import source_fingerprint

out = Path("results/current/performance-agent-closure-2026-09-13")
py = sys.executable
base = "/tmp/prime-source-wheels-owned/number_compiler-0.59.9-py3-none-any.whl"
history = "/tmp/adversarial-release-wheels/number_compiler-0.59.9-py3-none-any.whl"
candidate = "/tmp/performance-agent-final-wheel/number_compiler-0.59.9-py3-none-any.whl"
checks = [
    (
        "cold-current",
        [
            py,
            "-m",
            "devtools.benchmarks.cli_startup",
            base,
            candidate,
            "--samples",
            "5",
            "--case",
            "prime",
            "--case",
            "prime-start",
        ],
    ),
    (
        "warm-current",
        [py, "-m", "devtools.benchmarks.prime_rank", base, candidate, "--samples", "5"],
    ),
    (
        "cold-historical",
        [
            py,
            "-m",
            "devtools.benchmarks.cli_startup",
            history,
            candidate,
            "--samples",
            "5",
            "--case",
            "prime",
            "--case",
            "prime-start",
        ],
    ),
    (
        "warm-historical",
        [
            py,
            "-m",
            "devtools.benchmarks.prime_rank",
            history,
            candidate,
            "--samples",
            "5",
        ],
    ),
    (
        "cold-families",
        [
            py,
            "-m",
            "devtools.benchmarks.cli_startup",
            base,
            candidate,
            "--samples",
            "5",
            "--case",
            "196",
            "--case",
            "collatz",
            "--case",
            "antihydra",
        ],
    ),
    (
        "cold-special",
        [
            py,
            "-m",
            "devtools.benchmarks.cli_startup",
            base,
            candidate,
            "--samples",
            "5",
            "--case",
            "fermat",
            "--case",
            "mersenne",
        ],
    ),
    ("authored-mypy", [py, "-m", "mypy", "src", "tests", "devtools"]),
    ("authored-ruff", [py, "-m", "ruff", "check", "src", "tests", "devtools"]),
    (
        "policy",
        [
            py,
            "-m",
            "pytest",
            "-q",
            "tests/repository/test_repository_policy.py",
            "tests/repository/test_package_contracts.py",
            "tests/resources/test_resource_ownership.py",
        ],
    ),
]
before = source_fingerprint(Path.cwd())
for name, command in checks:
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
                "returncode": result.child_returncode,
                "elapsed": result.elapsed_seconds,
            }
        ),
        flush=True,
    )
    if report["source_after"] != before:
        raise RuntimeError("source changed during frozen validation")

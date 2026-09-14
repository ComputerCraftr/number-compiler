from pathlib import Path
from dataclasses import asdict
import json
import sys

sys.path.insert(0, str(Path.cwd()))
from devtools.checks.process_guard import run_guarded
from devtools.checks.test_run_evidence import source_fingerprint

out = Path("results/current/performance-agent-closure-2026-09-13")
py = sys.executable
checks = [
    ("full-unit", [py, "-m", "pytest", "-q", "--durations=20"], 300),
    (
        "explicit-p0",
        [
            py,
            "-m",
            "pytest",
            "-q",
            "-m",
            "",
            "tests/validation/proofs/test_antihydra_release.py",
            "tests/validation/proofs/test_shadow_jet_primality_release.py",
            "tests/validation/proofs/test_temporal_cutover_reporting.py",
            "tests/projection/test_idempotent_output.py::test_source_compiler_is_theorem_free_and_cheap_shapes_resolve_impossible_sheets_first",
            "tests/sequences/reverse_add/test_dyadic_hashlife.py::test_certified_reverse_uses_source_publisher_and_reports_concrete_work",
            "tests/projection/test_resource_metric_units.py::test_reverse_diamond_does_not_report_proof_states_as_runtime_classes",
        ],
        35,
    ),
]
before = source_fingerprint(Path.cwd())
for name, command, seconds in checks:
    result = run_guarded(
        tuple(command),
        output=out / (name + ".log"),
        timeout=seconds,
        memory_bytes=1024**3,
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

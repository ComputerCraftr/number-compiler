import hashlib
import json
import os
import subprocess
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

from devtools.checks.test_run_evidence import source_fingerprint

root = Path.cwd()
out = root / "results/current/production-p0-2026-09-11/release-audit"
out.mkdir(exist_ok=True)
frozen = source_fingerprint(root)
manifest = {"source_fingerprint": frozen, "release_ready": False, "jobs": []}
manifest["theories"] = {
    str(path.relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest()
    for path in sorted(
        (root / "devtools/proofs/isabelle/temporal_clocks").glob("*.thy")
    )
}
pytest = [sys.executable, "-m", "pytest", "-q"]
all_pytest = pytest + ["-m", "validation or not validation"]
jobs = [
    ("mypy", [sys.executable, "-m", "mypy", "src", "devtools", "tests"]),
    (
        "api",
        all_pytest
        + [
            "tests/sequences/power_numbers/test_special_certificate.py",
            "tests/api/test_sequence_compiler_identity.py",
            "tests/api/test_sequence_compiler.py",
            "tests/api/test_cli_classify.py",
            "tests/api/test_number_api.py",
            "tests/api/test_cli_adversarial.py",
            "tests/api/test_powered_term_cache.py",
            "tests/api/test_fast_path_cutover.py",
        ],
    ),
    (
        "collatz-scheduler",
        pytest
        + [
            "tests/hashlife/execution/test_collatz_certified_runtime.py",
            "tests/hashlife/execution/test_tile_causal_interfaces.py",
        ],
    ),
    (
        "reverse-scheduler",
        pytest
        + [
            "tests/hashlife/tiles/test_reverse_threshold_summary.py",
            "tests/hashlife/interfaces/test_reverse_sector_functions.py",
        ],
    ),
    (
        "power-shape",
        all_pytest
        + [
            "tests/arithmetic/polynomials/test_two_primary_filtration.py",
            "tests/validation/proofs/test_special_binary_jump.py",
        ],
    ),
    (
        "primitive-behavior",
        pytest + ["tests/arithmetic/contracts/test_primitive_behavior.py"],
    ),
    (
        "isabelle",
        [
            "/Applications/Isabelle2025-2.app/bin/isabelle",
            "build",
            "-v",
            "-c",
            "-d",
            "devtools/proofs/isabelle",
            "Temporal_Clock_Jumps",
        ],
    ),
]
for family in ("196", "collatz"):
    for mode in ("cold", "repeat"):
        jobs.append(
            (
                f"{family}-{mode}",
                [
                    sys.executable,
                    "-m",
                    "devtools.benchmarks.production_p0_probe",
                    "--family",
                    family,
                    "--mode",
                    mode,
                ],
            )
        )
    for horizon in (32, 64):
        extra = ["--seed", "27"] if family == "collatz" else []
        jobs.append(
            (
                f"cli-{family}-{horizon}",
                [
                    sys.executable,
                    "-m",
                    "number_compiler",
                    "nth",
                    family,
                    str(horizon),
                    *extra,
                    "--format",
                    "json",
                ],
            )
        )
jobs.extend(
    [
        (
            "policy-structural",
            all_pytest + ["tests/repository/test_repository_policy.py"],
        ),
        (
            "policy-boundary-static",
            all_pytest
            + [
                "tests/repository/test_proof_production_boundary.py",
                "-k",
                "not test_package_import_and_cold_warm_queries_work_with_proof_imports_blocked",
            ],
        ),
        (
            "policy-boundary-runtime",
            all_pytest
            + [
                "tests/repository/test_proof_production_boundary.py",
                "-k",
                "test_package_import_and_cold_warm_queries_work_with_proof_imports_blocked",
            ],
        ),
        ("ruff", [sys.executable, "-m", "ruff", "check", "src", "devtools", "tests"]),
    ]
)
env = dict(os.environ, ISABELLE_IDENTIFIER="number-compiler-ports-proof")
(out / "source-freeze.json").write_text(json.dumps(manifest, indent=2) + "\n")
for name, command in jobs:
    print(name, flush=True)
    if "pytest" in command:
        command += ["--junitxml", str(out / f"{name}.junit.xml")]
    suffix = (
        "json"
        if name.endswith(("-cold", "-repeat")) or name.startswith("cli-")
        else "log"
    )
    output = out / f"{name}.{suffix}"
    guard = out / f"{name}.guard.json"
    subprocess.run(
        [
            sys.executable,
            "-m",
            "devtools.checks.process_guard",
            "--output",
            str(output),
            "--report",
            str(guard),
            "--",
            *command,
        ],
        env=env,
        check=True,
    )
    assert source_fingerprint(root) == frozen
    row = {"name": name, "command": command, "guard": json.loads(guard.read_text())}
    if "pytest" in command:
        cases = ET.parse(out / f"{name}.junit.xml").findall(".//testcase")
        assert all(
            case.find("failure") is None
            and case.find("error") is None
            and case.find("skipped") is None
            for case in cases
        )
        row["passed_tests"] = len(cases)
    manifest["jobs"].append(row)
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
print("All frozen guarded jobs verified.", flush=True)

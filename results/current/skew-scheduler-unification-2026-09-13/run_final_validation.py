from pathlib import Path
from dataclasses import asdict
import json
import sys
import hashlib

sys.path.insert(0, str(Path.cwd()))
from devtools.checks.process_guard import run_guarded
from devtools.checks.test_run_evidence import source_fingerprint

out = Path("results/current/skew-scheduler-unification-2026-09-13")
py = sys.executable
wheel = "/tmp/skew-unification-final-wheel-5/number_compiler-0.59.9-py3-none-any.whl"
acceptance = json.loads((out / "acceptance-inputs.json").read_text())
group = sys.argv[1]
checks = []
if group == "focused":
    checks = [
        (
            "final-focused",
            [
                py,
                "-m",
                "pytest",
                "-q",
                "tests/hashlife/execution/test_source_bound_images.py",
                "tests/hashlife/execution/test_source_image_seals.py",
                "tests/sequences/prime",
                "tests/api/test_shared_skew_cli.py",
                "tests/api/test_prime_rank_cli.py",
                "tests/api/test_antihydra.py",
                "tests/api/test_antihydra_support_cache.py",
                "tests/api/test_antihydra_arithmetic.py",
                "tests/performance/test_cli_startup.py",
            ],
            35,
            1,
        ),
        ("final-policy", [py, "-m", "devtools.checks.repository_policy"], 35, 1),
        ("final-authored-mypy", [py, "-m", "mypy", "src", "tests", "devtools"], 35, 1),
        (
            "final-authored-ruff",
            [py, "-m", "ruff", "check", "src", "tests", "devtools"],
            35,
            1,
        ),
    ]
elif group == "wheel":
    checks = [
        (
            "final-wheel-build",
            [
                py,
                "-m",
                "pip",
                "wheel",
                ".",
                "--no-deps",
                "-w",
                "/tmp/skew-unification-final-wheel-5",
            ],
            35,
            1,
        ),
        (
            "final-wheel-inventory",
            [py, "-m", "devtools.checks.installed_distribution", wheel],
            35,
            1,
        ),
    ]
elif group == "prime":
    for label, record in acceptance["baselines"].items():
        base = record["path"]
        checks += [
            (
                f"final-prime-warm-{label}",
                [
                    py,
                    "-m",
                    "devtools.benchmarks.prime_rank",
                    base,
                    wheel,
                    "--samples",
                    "5",
                ],
                35,
                1,
            ),
            (
                f"final-prime-cold-{label}",
                [
                    py,
                    "-m",
                    "devtools.benchmarks.cli_startup",
                    base,
                    wheel,
                    "--samples",
                    "5",
                    "--case",
                    "prime",
                    "--case",
                    "prime-start",
                ],
                35,
                1,
            ),
        ]
elif group == "proof":
    for session in [
        "Prime_Wheel_Bridge",
        "Reverse_Residuals",
        "Temporal_Clock_Jumps",
        "Etale_Primary_Carry",
        "Antihydra",
    ]:
        checks.append(
            (
                f"final-isabelle-{session}",
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
                4,
            )
        )
elif group == "cli":
    base = acceptance["baselines"]["last_frozen"]["path"]
    for family in ["196", "collatz", "antihydra", "fermat", "mersenne"]:
        checks.append(
            (
                f"final-cold-{family}",
                [
                    py,
                    "-m",
                    "devtools.benchmarks.cli_startup",
                    base,
                    wheel,
                    "--samples",
                    "5",
                    "--case",
                    family,
                ],
                35,
                1,
            )
        )
    checks += [
        (
            "final-antihydra-projection",
            [py, str(out / "antihydra_installed_projection_probe.py")],
            35,
            1,
        )
    ]
elif group == "unit":
    checks = [
        ("final-full-unit", [py, "-m", "pytest", "-q", "--durations=20"], 300, 1),
        (
            "final-explicit-p0",
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
            1,
        ),
        ("final-whole-tree-mypy", [py, "-m", "mypy", "."], 35, 1),
        ("final-whole-tree-ruff", [py, "-m", "ruff", "check", "."], 35, 1),
    ]
elif group == "antihydra-growth":
    checks = [("final-antihydra-growth", [py, str(out / "antihydra_growth_probe.py")], 35, 1)]
else:
    raise ValueError(group)
before = source_fingerprint(Path.cwd())
freeze = out / "final-freeze.json"
if freeze.exists():
    if json.loads(freeze.read_text())["source_fingerprint"] != before:
        raise RuntimeError("source does not match frozen fingerprint")
else:
    freeze.write_text(json.dumps({"source_fingerprint": before}, indent=2) + "\n")
for name, command, seconds, gib in checks:
    print(json.dumps({"starting": name}), flush=True)
    result = run_guarded(
        tuple(command),
        output=out / (name + ".log"),
        timeout=seconds,
        memory_bytes=gib * 1024**3,
    )
    report = asdict(result) | {
        "command": command,
        "source_before": before,
        "source_after": source_fingerprint(Path.cwd()),
    }
    (out / (name + ".guard.json")).write_text(json.dumps(report, indent=2) + "\n")
    print(
        json.dumps(
            {
                "check": name,
                "outcome": result.outcome,
                "returncode": result.child_returncode,
                "seconds": result.elapsed_seconds,
            }
        ),
        flush=True,
    )
    if report["source_after"] != before:
        raise RuntimeError("source changed")
if group == "wheel" and Path(wheel).exists():
    (out / "final-wheel.json").write_text(
        json.dumps(
            {
                "path": wheel,
                "sha256": hashlib.sha256(Path(wheel).read_bytes()).hexdigest(),
                "source_fingerprint": before,
            },
            indent=2,
        )
        + "\n"
    )

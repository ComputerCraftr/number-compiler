"""Serialize reproducible release suites; a hygiene pass never authorizes release.

Each guarded command has its own unchanged time/memory ceiling. The all suite
uses one unfiltered pytest run, whose evidence also covers the P0 selection.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import signal
import sys
from dataclasses import asdict
from pathlib import Path
from types import FrameType
from uuid import uuid4

from devtools.checks.process_guard import (
    PROOF_GENERATION_ENV,
    run_guarded,
    source_revision,
)
from devtools.checks.test_run_evidence import (
    parse_collection,
    pytest_environment,
    source_fingerprint,
    validate_evidence,
    validate_serial_release,
)
from devtools.paths import isabelle_root
from devtools.runs import EvidenceRun

# Exact seven-module selection retained from the pre-migration P0 manifest.
P0 = (
    "tests/sequences/collatz/test_linear_bisimulation_checkpoint.py",
    "tests/validation/proofs/test_antihydra_release.py",
    "tests/validation/proofs/test_family_digit_cylinder_cutover.py",
    "tests/validation/proofs/test_reverse_generic_range_constructor.py",
    "tests/validation/proofs/test_reverse_temporal_publisher_cutover.py",
    "tests/validation/proofs/test_shadow_jet_primality_release.py",
    "tests/validation/proofs/test_temporal_runtime_reporting.py",
)


def execute(
    run: EvidenceRun,
    name: str,
    command: tuple[str, ...],
    timeout: int = 35,
    memory_mib: int = 1024,
) -> bool:
    before = source_fingerprint(run.root)
    revision = source_revision(run.root)
    environment = pytest_environment()
    environment[PROOF_GENERATION_ENV] = f"{uuid4().hex}:{before}"
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    result = run_guarded(
        command,
        output=run.path / f"{name}.log",
        cwd=run.root,
        timeout=timeout,
        memory_bytes=memory_mib * 1024**2,
        environment=environment,
    )
    after = source_fingerprint(run.root)
    unchanged = before == after and revision == source_revision(run.root)
    record: dict[str, object] = {
        **asdict(result),
        "name": name,
        "command": list(command),
        "timeout_seconds": timeout,
        "memory_mib": memory_mib,
        "source_fingerprint_before": before,
        "source_fingerprint_after": after,
        "source_unchanged": unchanged,
    }
    if not unchanged:
        record["outcome"] = "source_changed"
    (run.path / f"{name}.json").write_text(json.dumps(record, indent=2) + "\n")
    run.record(record)
    print(f"{name}: {record['outcome']}", flush=True)
    return unchanged and result.outcome == "completed"


def quality(run: EvidenceRun) -> bool:
    commands = (
        ("mypy", (sys.executable, "-m", "mypy", "--python-executable", sys.executable)),
        ("ruff", ("ruff", "check", ".")),
        ("format", ("ruff", "format", "--check", ".")),
        *(
            (name, (sys.executable, "-m", f"devtools.checks.{module}"))
            for name, module in (
                ("policy", "repository_policy"),
                ("docs", "docs_index"),
                ("proof-index", "isabelle_proof_index"),
            )
        ),
    )
    passed = True
    for name, command in commands:
        passed = execute(run, name, command) and passed
    passed = (
        execute(
            run,
            "package",
            (
                sys.executable,
                "-m",
                "devtools.checks.package_release",
                "--output-dir",
                str(run.path / "package"),
            ),
        )
        and passed
    )
    return passed


def pytest_suite(run: EvidenceRun, suite: str) -> bool:
    selectors = P0 if suite == "p0" else ("tests",)
    mark = "not validation" if suite == "unit" else ""
    common = ("-o", "addopts=", "--strict-markers", "-m", mark, *selectors)
    command = (sys.executable, "-m", "pytest", "--collect-only", "-q", *common)
    if not execute(run, f"{suite}-collect", command):
        return False
    required = parse_collection((run.path / f"{suite}-collect.log").read_text())
    xml = run.path / f"{suite}.xml"
    command = (
        sys.executable,
        "-m",
        "pytest",
        "-q",
        "--tb=short",
        *common,
        f"--junitxml={xml}",
    )
    passed = execute(run, suite, command, 300)
    if not passed:
        return False
    try:
        if suite == "all":
            report = validate_serial_release(xml, run.root, required)
            if not report["serial_time_gate_passed"]:
                raise ValueError(
                    "unfiltered suite exceeds the 300-second release limit"
                )
        else:
            validate_evidence(xml, run.root, required)
    except (ValueError, OSError) as error:
        run.record(
            {"name": f"{suite}-evidence", "outcome": "rejected", "detail": str(error)}
        )
        return False
    return True


def proofs(run: EvidenceRun, executable: str, sessions: tuple[str, ...]) -> bool:
    selection = (
        ("-d", str(isabelle_root(run.root)), *sessions)
        if sessions
        else ("-D", str(isabelle_root(run.root)))
    )
    command = (
        executable,
        "build",
        "-b",
        "-j",
        "1",
        "-o",
        "threads=1",
        "-o",
        "parallel_proofs=0",
        *selection,
    )
    return execute(run, "proofs", command, 60, 4096)


def interrupted(number: int, frame: FrameType | None) -> None:
    raise KeyboardInterrupt(f"received signal {number}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--suite", choices=("quality", "unit", "proofs", "p0", "all"), required=True
    )
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument(
        "--isabelle",
        default=os.environ.get(
            "ISABELLE",
            shutil.which("isabelle") or "/Applications/Isabelle2025-2.app/bin/isabelle",
        ),
    )
    parser.add_argument("--session", action="append", default=[])
    options = parser.parse_args()
    if options.session and options.suite != "proofs":
        parser.error(
            "--session is only for focused --suite proofs; all remains aggregate"
        )
    previous = signal.signal(signal.SIGTERM, interrupted)
    try:
        with EvidenceRun(
            output_dir=options.output_dir,
            limits={
                "probe_seconds": 35,
                "probe_mib": 1024,
                "proof_seconds": 60,
                "proof_mib": 4096,
                "unit_seconds": 300,
                "unit_mib": 1024,
            },
        ) as run:
            passed = True
            if options.suite in ("quality", "all"):
                passed = quality(run) and passed
            if options.suite in ("unit", "p0", "all"):
                passed = pytest_suite(run, options.suite) and passed
            if options.suite in ("proofs", "all"):
                passed = (
                    proofs(run, options.isabelle, tuple(options.session)) and passed
                )
            run.finish("completed" if passed else "failed")
            print(run.path)
            return 0 if passed and run.manifest["outcome"] == "completed" else 1
    finally:
        signal.signal(signal.SIGTERM, previous)


if __name__ == "__main__":
    raise SystemExit(main())

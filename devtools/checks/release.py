"""Run repository validation under one shared, guarded execution policy."""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import signal
import sys
import time
from collections.abc import Mapping
from dataclasses import asdict
from datetime import UTC, datetime
from pathlib import Path
from types import FrameType
from uuid import uuid4

from devtools.checks.process_guard import (
    DEADLINE_ENV,
    MEMORY_BUDGET_ENV,
    PROOF_GENERATION_ENV,
    run_guarded,
)
from devtools.checks.pytest_policy import (
    ACTIVE_TEST_ENV,
    forbidden_environment_overrides,
)
from devtools.checks.test_run_evidence import (
    PROVENANCE_MODE_ENV,
    minimal_selectors,
    pytest_environment,
    validate_evidence,
    validate_serial_release,
)
from devtools.checks.validation_policy import (
    ISABELLE_JAVA_OPTIONS,
    ISABELLE_JOBS,
    ISABELLE_MEMORY_BYTES,
    ISABELLE_ML_OPTIONS,
    ISABELLE_OPTIONS,
    ISABELLE_PARALLEL_PROOFS,
    ISABELLE_SESSION_SECONDS,
    ISABELLE_THREADS,
    POLICY_VERSION,
    PYTEST_RUNNER_ENV,
    PYTHON_COMMAND,
    PYTHON_COMMAND_SECONDS,
    PYTHON_MEMORY_BYTES,
    PYTHON_SUITE,
    PYTHON_SUITE_SECONDS,
    PYTHON_TEST,
    PYTHON_TEST_SECONDS,
    ExecutionPolicy,
    isabelle_policy,
)
from devtools.git_source import acceptance_checkout, git_source
from devtools.paths import isabelle_root, repository_root
from devtools.runs import EvidenceRun

# Canonical P0 owners. Runtime gates live with their family or shared runtime,
# while theorem/release obligations retain their proof-owner modules.
P0 = (
    "tests/sequences/collatz/test_source_image_runtime.py",
    "tests/sequences/reverse_add/test_source_image_runtime.py",
    "tests/validation/runtime/test_cross_family_runtime_reporting.py",
    "tests/hashlife/observation/test_runtime_reporting.py",
    "tests/validation/proofs/test_antihydra_release.py",
    "tests/validation/proofs/test_family_digit_cylinder_cutover.py",
    "tests/validation/proofs/test_reverse_generic_range_constructor.py",
    "tests/validation/proofs/test_reverse_temporal_publisher_cutover.py",
    "tests/validation/proofs/test_shadow_jet_primality_release.py",
)
ACCEPTANCE_ROOT_ENV = "NUMBER_COMPILER_ACCEPTANCE_ROOT"
_SESSION_NAME = re.compile(r"^[A-Za-z0-9_][A-Za-z0-9_.+-]*$")
_SESSION_STATUS = re.compile(
    r"^\s*(Running|Building|Finished|Failed|FAILED|Unfinished)\s+"
    r"([A-Za-z0-9_][A-Za-z0-9_.+-]*)(?:\s|\(|$)"
)
_UNFINISHED_LIST = re.compile(r"^\s*Unfinished session\(s\):\s*(.+)$")
_SESSION_DURATION = re.compile(r"\((\d+:\d{2}:\d{2}(?:\.\d+)?) elapsed time")


def _git_revision_stable(
    before: dict[str, str | bool], after: dict[str, str | bool]
) -> bool:
    return all(
        before[key] == after[key]
        for key in ("git_commit", "git_tree", "git_object_format")
    )


def _git_stable_for_mode(
    before: dict[str, str | bool],
    after: dict[str, str | bool],
    *,
    acceptance: bool,
) -> bool:
    revision_stable = _git_revision_stable(before, after)
    return revision_stable and (
        not acceptance or (before["git_dirty"] is False and after["git_dirty"] is False)
    )


def _phase_summary(path: Path) -> dict[str, object]:
    """Summarize timing records, retaining incomplete evidence after a kill."""
    phases: dict[str, list[float]] = {}
    per_node: dict[str, float] = {}
    failure_reports: list[dict[str, object]] = []
    failure_report_count = 0
    failure_summary_truncated = False
    finished = False
    exitstatus: int | None = None
    selected_items: int | None = None
    truncated = False
    if path.is_file():
        for line in path.read_text(encoding="utf-8").splitlines():
            try:
                row = json.loads(line)
            except json.JSONDecodeError:
                continue
            phase = row.get("phase")
            seconds = row.get("seconds")
            if row.get("outcome") == "failed":
                failure_report_count += 1
                failure_longrepr = row.get("failure_longrepr")
                excerpt_truncated = row.get("failure_longrepr_truncated") is True
                if isinstance(failure_longrepr, str):
                    encoded_excerpt = failure_longrepr.encode("utf-8")
                    if len(encoded_excerpt) > 2048:
                        failure_longrepr = encoded_excerpt[:2048].decode(
                            "utf-8", errors="ignore"
                        )
                        excerpt_truncated = True
                else:
                    failure_longrepr = None
                if len(failure_reports) < 20:
                    failure_reports.append(
                        {
                            "nodeid": row.get("nodeid"),
                            "phase": phase,
                            "outcome": "failed",
                            "failure_longrepr_excerpt": failure_longrepr,
                            "failure_longrepr_truncated": excerpt_truncated,
                        }
                    )
                else:
                    failure_summary_truncated = True
                failure_summary_truncated |= excerpt_truncated
            if isinstance(phase, str) and type(seconds) in (int, float):
                phases.setdefault(phase, []).append(float(seconds))
                if phase == "collection":
                    count = row.get("selected_items")
                    selected_items = count if type(count) is int else None
                nodeid = row.get("nodeid")
                if isinstance(nodeid, str):
                    per_node[nodeid] = per_node.get(nodeid, 0.0) + float(seconds)
            if row.get("status") == "finished":
                finished = True
                status = row.get("exitstatus")
                exitstatus = status if type(status) is int else None
            if row.get("status") == "truncated":
                truncated = True
    summary = {
        name: {
            "count": len(values),
            "total_seconds": sum(values),
            "max_seconds": max(values, default=0.0),
        }
        for name, values in phases.items()
    }
    test_phases = {
        name: data
        for name, data in summary.items()
        if name in {"setup", "call", "teardown"}
    }
    return {
        "phases": summary,
        "test_phase_totals": test_phases,
        "slowest_test_nodes": [
            {"nodeid": nodeid, "seconds": seconds}
            for nodeid, seconds in sorted(
                per_node.items(), key=lambda item: (-item[1], item[0])
            )[:20]
        ],
        "failure_report_count": failure_report_count,
        "failure_reports": failure_reports,
        "failure_reports_truncated": failure_summary_truncated,
        "truncated": truncated,
        "complete": finished and not truncated and "collection" in phases,
        "selected_items": selected_items,
        "pytest_exitstatus": exitstatus,
    }


def _acceptance_environment(root: Path, environment: dict[str, str]) -> None:
    """Make acceptance subprocesses import Python sources from the worktree."""
    source = (root / "src").resolve()
    environment["PYTHONPATH"] = str(source)
    environment[ACCEPTANCE_ROOT_ENV] = str(root.resolve())
    environment[PROVENANCE_MODE_ENV] = "acceptance"


def _parse_session_inventory(
    text: str, required_sessions: tuple[str, ...]
) -> tuple[str, ...]:
    """Parse Isabelle's authoritative topological `sessions -b` output."""
    names = tuple(
        line.strip()
        for line in text.splitlines()
        if _SESSION_NAME.fullmatch(line.strip())
    )
    if not names or len(names) != len(set(names)):
        raise ValueError("Isabelle session inventory is empty or contains duplicates")
    missing = sorted(set(required_sessions) - set(names))
    if missing:
        raise ValueError(
            "native Isabelle inventory omitted requested sessions: "
            + ", ".join(missing)
        )
    return names


def _isabelle_environment_command(
    executable: str,
    assignments: tuple[str, ...],
    arguments: tuple[str, ...],
) -> tuple[str, ...]:
    """Run an Isabelle tool after setting its environment in Isabelle's env."""
    return (executable, "env", *assignments, executable, *arguments)


def _session_build_summary(
    text: str, inventory: tuple[str, ...], *, succeeded: bool
) -> dict[str, object]:
    """Separate rebuilt, reused and unclassified heaps from native build logs."""
    started: set[str] = set()
    finished: set[str] = set()
    failed: set[str] = set()
    durations: dict[str, float] = {}
    for line in text.splitlines():
        unfinished_match = _UNFINISHED_LIST.match(line)
        if unfinished_match:
            failed.update(
                name.strip()
                for name in unfinished_match.group(1).split(",")
                if name.strip()
            )
            continue
        match = _SESSION_STATUS.match(line)
        if match is None:
            continue
        status, name = match.groups()
        if status in {"Running", "Building"}:
            started.add(name)
        elif status == "Finished":
            finished.add(name)
            duration_match = _SESSION_DURATION.search(line)
            if duration_match:
                hours, minutes, seconds = duration_match.group(1).split(":")
                durations[name] = int(hours) * 3600 + int(minutes) * 60 + float(seconds)
        else:
            failed.add(name)
    rebuilt = started | finished
    unknown = sorted(set(inventory) - rebuilt - failed)
    unmatched = sorted((started | finished | failed) - set(inventory))
    if succeeded and not failed:
        reused: list[str] | None = sorted(set(inventory) - rebuilt)
        inferred = "successful native build; inventory minus reported built sessions"
        not_attempted: list[str] = []
    else:
        reused = None
        inferred = None
        not_attempted = unknown
    return {
        "inventory_sessions": list(inventory),
        "inventory_count": len(inventory),
        "started_sessions": sorted(started),
        "rebuilt_sessions": sorted(rebuilt),
        "finished_sessions": sorted(finished),
        "failed_sessions": sorted(failed),
        "unmatched_native_session_statuses": unmatched,
        "reused_sessions": reused,
        "reused_inference": inferred,
        "not_attempted_or_unclassified_sessions": not_attempted,
        "finished_session_elapsed_seconds": durations or None,
    }


def execute(
    run: EvidenceRun,
    name: str,
    command: tuple[str, ...],
    policy: ExecutionPolicy = PYTHON_COMMAND,
    *,
    acceptance: bool = False,
    pytest_run: bool = False,
    record_fields: Mapping[str, object] | None = None,
) -> bool:
    before = git_source(run.root).as_dict()
    generation = uuid4().hex
    environment = pytest_environment()
    environment[PROOF_GENERATION_ENV] = generation
    deadline = time.monotonic() + policy.timeout_seconds
    parent_deadline = os.environ.get(DEADLINE_ENV)
    if parent_deadline is not None:
        deadline = min(deadline, float(parent_deadline))
    environment[DEADLINE_ENV] = str(deadline)
    parent_memory = os.environ.get(MEMORY_BUDGET_ENV)
    memory_bytes = policy.memory_bytes
    if parent_memory is not None:
        memory_bytes = min(memory_bytes, int(parent_memory))
    environment[MEMORY_BUDGET_ENV] = str(memory_bytes)
    environment[PROVENANCE_MODE_ENV] = "acceptance" if acceptance else "development"
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    active_path = run.path / f"{name}.active-test"
    timing_path = run.path / f"{name}.phases.jsonl"
    if pytest_run:
        environment[PYTEST_RUNNER_ENV] = generation
        environment[ACTIVE_TEST_ENV] = str(active_path)
    if acceptance:
        _acceptance_environment(run.root, environment)
    result = run_guarded(
        command,
        output=run.path / f"{name}.log",
        cwd=run.root,
        timeout=policy.timeout_seconds,
        memory_bytes=memory_bytes,
        environment=environment,
        active_test_path=active_path if pytest_run else None,
        active_test_timeout=PYTHON_TEST_SECONDS if pytest_run else None,
    )
    after = git_source(run.root).as_dict()
    git_revision_stable = _git_revision_stable(before, after)
    git_stable = _git_stable_for_mode(before, after, acceptance=acceptance)
    record: dict[str, object] = {
        **asdict(result),
        "process_outcome": result.outcome,
        "name": name,
        "command": list(command),
        "policy_version": POLICY_VERSION,
        "timeout_seconds": policy.timeout_seconds,
        "memory_bytes": policy.memory_bytes,
        "git_source_before": before,
        "git_source_after": after,
        "git_revision_stable": git_revision_stable,
        "git_state_stable_for_mode": git_stable,
        "evidence_mode": "acceptance" if acceptance else "development",
        "proof_generation": generation,
        **(record_fields or {}),
    }
    if active_path.is_file():
        try:
            record["active_test_at_termination"] = json.loads(
                active_path.read_text(encoding="utf-8")
            )
        except (OSError, json.JSONDecodeError):
            record["active_test_at_termination"] = {"status": "unreadable"}
        active_path.unlink()
    else:
        record["active_test_at_termination"] = None
    if pytest_run:
        record["pytest_timing"] = _phase_summary(timing_path)
        record["pytest_timing_path"] = str(timing_path)
    instrumentation_ok = True
    if pytest_run:
        timing = record["pytest_timing"]
        assert isinstance(timing, dict)
        instrumentation_ok = bool(timing["complete"])
        record["instrumentation_complete"] = instrumentation_ok
        if result.outcome == "completed" and not instrumentation_ok:
            record["outcome"] = "instrumentation_failed"
            record["detail"] = "pytest phase evidence is incomplete or truncated"
    (run.path / f"{name}.json").write_text(json.dumps(record, indent=2) + "\n")
    run.record(record)
    print(f"{name}: {record['outcome']}", flush=True)
    return (
        (not acceptance or git_stable)
        and result.outcome == "completed"
        and instrumentation_ok
    )


def quality(run: EvidenceRun, *, acceptance: bool = False) -> bool:
    commands = (
        ("mypy", (sys.executable, "-m", "mypy", "--python-executable", sys.executable)),
        ("ruff", (sys.executable, "-m", "ruff", "check", ".")),
        ("format", (sys.executable, "-m", "ruff", "format", "--check", ".")),
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
        passed = execute(run, name, command, acceptance=acceptance) and passed
    package = (
        sys.executable,
        "-m",
        "devtools.checks.package_release",
        "--output-dir",
        str(run.path / "package"),
    )
    return execute(run, "package", package, acceptance=acceptance) and passed


def _pytest_selection(
    suite: str, selectors: tuple[str, ...]
) -> tuple[tuple[str, ...], str]:
    if selectors:
        if suite == "all":
            raise ValueError("--select cannot narrow the full --suite all run")
        if suite == "p0":
            allowed = set(P0)
            if any(selector.split("::", 1)[0] not in allowed for selector in selectors):
                raise ValueError(
                    "P0 selections must remain within the canonical P0 files"
                )
        return minimal_selectors(selectors), ""
    if suite == "p0":
        return P0, ""
    return ("tests",), "not validation" if suite == "unit" else ""


def _pytest_command(
    output_directory: Path,
    suite: str,
    selectors: tuple[str, ...],
    mark: str,
    *,
    profile: bool = False,
) -> tuple[str, ...]:
    xml = output_directory / f"{suite}.xml"
    timing = output_directory / f"{suite}.phases.jsonl"
    command = [
        sys.executable,
        "-m",
        "pytest",
        "-p",
        "pytest_timeout",
        "-p",
        "devtools.checks.pytest_policy",
        "-p",
        "devtools.benchmarks.pytest_timing",
        "--timeout",
        str(PYTHON_TEST_SECONDS),
        "--timeout-method",
        "thread",
        "--timeout-disable-debugger-detection",
        "--timing-output",
        str(timing),
        "-q",
        "--tb=short",
        "--strict-markers",
        "-o",
        "addopts=",
    ]
    if mark:
        command.extend(("-m", mark))
    if profile:
        command.extend(("--profile-output", str(output_directory / f"{suite}.pstats")))
    command.extend((*selectors, f"--junitxml={xml}"))
    return tuple(command)


def pytest_suite(
    run: EvidenceRun,
    suite: str,
    selectors: tuple[str, ...] = (),
    *,
    acceptance: bool = False,
    profile: bool = False,
) -> bool:
    try:
        selected, mark = _pytest_selection(suite, selectors)
    except ValueError as error:
        run.record(
            {"name": f"{suite}-selection", "outcome": "rejected", "detail": str(error)}
        )
        return False
    policy = PYTHON_TEST if len(selected) == 1 and "::" in selected[0] else PYTHON_SUITE
    command = _pytest_command(run.path, suite, selected, mark, profile=profile)
    if not execute(
        run,
        suite,
        command,
        policy,
        acceptance=acceptance,
        pytest_run=True,
    ):
        return False
    xml = run.path / f"{suite}.xml"
    try:
        if suite == "all":
            report = validate_serial_release(
                xml,
                run.root,
                require_clean=acceptance,
                require_acceptance=acceptance,
                require_acceptance_verified=False,
            )
            if not report["serial_time_gate_passed"]:
                raise ValueError("full suite exceeds the 300-second limit")
        else:
            validate_evidence(
                xml,
                run.root,
                require_clean=acceptance,
                require_acceptance=acceptance,
                require_acceptance_verified=False,
            )
        run.record(
            {
                "name": f"{suite}-evidence",
                "outcome": "validated",
                "detail": report
                if suite == "all"
                else "JUnit manifest and outcomes match",
            }
        )
    except (ValueError, OSError) as error:
        run.record(
            {"name": f"{suite}-evidence", "outcome": "rejected", "detail": str(error)}
        )
        return False
    return True


def proofs(
    run: EvidenceRun,
    executable: str,
    sessions: tuple[str, ...],
    *,
    acceptance: bool = False,
) -> bool:
    from devtools.checks.isabelle_syntax import (
        parse_sessions,
        session_dependency_closure,
    )

    if not execute(
        run,
        "isabelle-version",
        (executable, "version"),
        ExecutionPolicy(ISABELLE_SESSION_SECONDS, ISABELLE_MEMORY_BYTES),
        acceptance=acceptance,
        record_fields={"tool": "isabelle"},
    ):
        return False
    try:
        version_text = (
            (run.path / "isabelle-version.log").read_text(encoding="utf-8").strip()
        )
    except OSError as error:
        run.record(
            {
                "name": "isabelle-version-observation",
                "outcome": "unavailable",
                "detail": str(error),
            }
        )
        return False
    if not version_text:
        run.record(
            {
                "name": "isabelle-version-observation",
                "outcome": "unavailable",
                "detail": "selected executable returned no version text",
            }
        )
        return False
    run.record(
        {
            "name": "isabelle-version-observation",
            "outcome": "observed",
            "tool_versions": {"isabelle": version_text},
        }
    )

    theory_root = isabelle_root(run.root)
    declared = parse_sessions((theory_root / "ROOT").read_text(encoding="utf-8"))
    requested = tuple(dict.fromkeys(sessions))
    closure = (
        session_dependency_closure(declared, requested)
        if requested
        else tuple(session.name for session in declared)
    )
    local_names = {session.name for session in declared}
    selection = (
        ("-d", str(theory_root), *requested) if requested else ("-D", str(theory_root))
    )
    tool_environment = (
        "env",
        f"ISABELLE_TOOL_JAVA_OPTIONS={ISABELLE_JAVA_OPTIONS}",
        f"ML_OPTIONS={ISABELLE_ML_OPTIONS}",
    )
    inventory_command = _isabelle_environment_command(
        executable,
        tool_environment[1:],
        ("sessions", "-b", *selection),
    )
    if not execute(
        run,
        "proof-session-inventory",
        inventory_command,
        ExecutionPolicy(ISABELLE_SESSION_SECONDS, ISABELLE_MEMORY_BYTES),
        acceptance=acceptance,
        record_fields={"inventory_request": list(selection)},
    ):
        return False
    inventory_log = run.path / "proof-session-inventory.log"
    try:
        inventory_roots = requested or tuple(session.name for session in declared)
        inventory = _parse_session_inventory(
            inventory_log.read_text(encoding="utf-8"), inventory_roots
        )
    except (OSError, ValueError) as error:
        run.record(
            {
                "name": "proof-session-inventory-parse",
                "outcome": "rejected",
                "detail": str(error),
            }
        )
        return False
    build = [executable, "build", "-b", "-j", str(ISABELLE_JOBS)]
    for option in ISABELLE_OPTIONS:
        build.extend(("-o", option))
    build.extend(selection)
    command = _isabelle_environment_command(
        executable, tool_environment[1:], tuple(build[1:])
    )
    completed = execute(
        run,
        "proofs",
        command,
        isabelle_policy(len(inventory)),
        acceptance=acceptance,
        record_fields={
            "session_inventory_count": len(inventory),
            "session_inventory": list(inventory),
            "project_dependency_session_count": len(closure),
        },
    )
    build_log = run.path / "proofs.log"
    try:
        summary = _session_build_summary(
            build_log.read_text(encoding="utf-8"), inventory, succeeded=completed
        )
        summary["local_dependency_session_count"] = len(closure)
        summary["external_session_dependencies"] = [
            name for name in inventory if name not in local_names
        ]
        run.record(
            {
                "name": "proof-build-session-summary",
                "outcome": "observed" if completed else "partial",
                **summary,
            }
        )
    except OSError as error:
        run.record(
            {
                "name": "proof-build-session-summary",
                "outcome": "unavailable",
                "detail": str(error),
                "reused_sessions": None,
            }
        )
        return False
    return completed


def _output_path(
    repository: Path, requested: Path | None, acceptance: bool
) -> Path | None:
    if not acceptance:
        return requested
    if requested is not None:
        return requested.resolve()
    stamp = datetime.now(UTC).strftime("%Y%m%dT%H%M%SZ")
    return repository / "results" / "runs" / f"{stamp}-{uuid4().hex}"


def _run(
    root: Path,
    repository: Path,
    options: argparse.Namespace,
    acceptance: bool,
) -> tuple[int, EvidenceRun]:
    output_dir = _output_path(repository, options.output_dir, acceptance)
    if acceptance and output_dir is not None and output_dir.is_relative_to(root):
        raise ValueError("acceptance output must be outside its temporary worktree")
    limits = {
        "policy_version": POLICY_VERSION,
        "python_test_seconds": PYTHON_TEST_SECONDS,
        "python_suite_seconds": PYTHON_SUITE_SECONDS,
        "python_command_seconds": PYTHON_COMMAND_SECONDS,
        "python_memory_bytes": PYTHON_MEMORY_BYTES,
        "isabelle_session_seconds": ISABELLE_SESSION_SECONDS,
        "isabelle_memory_bytes": ISABELLE_MEMORY_BYTES,
        "isabelle_threads": ISABELLE_THREADS,
        "isabelle_parallel_proofs": ISABELLE_PARALLEL_PROOFS,
        "isabelle_jobs": ISABELLE_JOBS,
    }
    with EvidenceRun(
        root=root,
        output_dir=output_dir,
        command=tuple(sys.orig_argv),
        limits=limits,
        evidence_mode="acceptance" if acceptance else "development",
    ) as run:
        passed = True
        if options.suite in ("quality", "all"):
            passed = quality(run, acceptance=acceptance) and passed
        if options.suite in ("unit", "p0", "all"):
            passed = (
                pytest_suite(
                    run,
                    options.suite,
                    tuple(options.select),
                    acceptance=acceptance,
                    profile=getattr(options, "profile", False),
                )
                and passed
            )
        if options.suite in ("proofs", "all"):
            passed = (
                proofs(
                    run,
                    options.isabelle,
                    tuple(options.session),
                    acceptance=acceptance,
                )
                and passed
            )
        run.finish("completed" if passed else "failed")
        print(run.path)
        status = 0 if passed and run.manifest["outcome"] == "completed" else 1
    return status, run


def interrupted(number: int, frame: FrameType | None) -> None:
    raise KeyboardInterrupt(f"received signal {number}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--suite", choices=("quality", "unit", "proofs", "p0", "all"), required=True
    )
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--select", action="append", default=[])
    parser.add_argument("--acceptance", action="store_true")
    parser.add_argument(
        "--profile",
        action="store_true",
        help="Profile Python calls under unchanged validation limits",
    )
    parser.add_argument(
        "--isabelle",
        default=os.environ.get(
            "ISABELLE",
            shutil.which("isabelle") or "/Applications/Isabelle2025-2.app/bin/isabelle",
        ),
    )
    parser.add_argument("--session", action="append", default=[])
    options = parser.parse_args()
    if options.profile and (options.acceptance or options.suite not in ("unit", "p0")):
        parser.error("--profile is for development Python selections only")
    if options.suite in ("unit", "p0", "all"):
        forbidden = forbidden_environment_overrides(os.environ)
        if forbidden:
            parser.error(
                "pytest environment overrides are disabled: " + ", ".join(forbidden)
            )
    if options.session and options.suite not in ("proofs", "all"):
        parser.error("--session is only valid with --suite proofs or all")
    if options.select and options.suite in ("proofs", "quality", "all"):
        parser.error("--select applies only to unit or P0 pytest suites")
    if options.session and options.suite == "all":
        parser.error("--session cannot narrow the aggregate --suite all proof build")
    previous = signal.signal(signal.SIGTERM, interrupted)
    repository = repository_root().resolve()
    acceptance_run: EvidenceRun | None = None
    try:
        if options.acceptance:
            with acceptance_checkout(repository) as checkout:
                status, acceptance_run = _run(checkout, repository, options, True)
            assert acceptance_run is not None
            if status == 0:
                acceptance_run.mark_acceptance_complete()
            return status
        status, _run_evidence = _run(repository, repository, options, False)
        return status
    except (RuntimeError, ValueError, OSError) as error:
        if options.acceptance and acceptance_run is not None:
            acceptance_run.mark_acceptance_failed(str(error))
        print(f"validation failed: {error}", file=sys.stderr)
        return 1
    finally:
        signal.signal(signal.SIGTERM, previous)


if __name__ == "__main__":
    raise SystemExit(main())

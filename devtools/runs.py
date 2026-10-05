"""Fresh, source-bound developer evidence with explicit completion status."""

from __future__ import annotations

import atexit
import contextlib
import io
import json
import os
import platform
import sys
import time
from collections.abc import Callable, Mapping
from datetime import UTC, datetime
from importlib.metadata import PackageNotFoundError, version
from pathlib import Path
from types import TracebackType
from typing import Literal, Self, TextIO
from uuid import uuid4

from devtools.paths import repository_root

EVIDENCE_SCHEMA_VERSION = 2


def utc_now() -> str:
    return datetime.now(UTC).isoformat()


def tool_versions() -> dict[str, str]:
    """Report Python-side tools without probing unrelated executables.

    Isabelle's version belongs to proof execution provenance. The release proof
    runner records the selected executable when a proof suite actually runs;
    creating an ordinary Python evidence run must not spawn it.
    """
    result = {"python": platform.python_version()}
    for name in ("pytest", "pytest-timeout", "mypy", "ruff", "setuptools"):
        try:
            result[name] = version(name)
        except PackageNotFoundError:
            result[name] = "unavailable"
    return result


class EvidenceRun:
    """One exclusive output directory; unfinished work never becomes a pass."""

    def __init__(
        self,
        *,
        root: Path | None = None,
        output_dir: Path | None = None,
        command: tuple[str, ...] | None = None,
        limits: Mapping[str, int | float] | None = None,
        evidence_mode: Literal["development", "acceptance"] = "development",
    ) -> None:
        from devtools.checks.validation_policy import POLICY_VERSION
        from devtools.git_source import git_source
        from number_compiler.resources.temporal_diagnostics import (
            METRICS_SCHEMA_VERSION,
        )

        self.root = (root or repository_root()).resolve()
        if evidence_mode not in {"development", "acceptance"}:
            raise ValueError("evidence mode must be development or acceptance")
        self._git_before = git_source(self.root)
        if evidence_mode == "acceptance" and self._git_before.dirty:
            raise ValueError("acceptance evidence requires a clean committed tree")
        self.evidence_mode = evidence_mode
        stamp = datetime.now(UTC).strftime("%Y%m%dT%H%M%SZ")
        self.path = (
            output_dir or self.root / "results" / "runs" / f"{stamp}-{uuid4().hex}"
        )
        self.path = self.path.resolve()
        # mkdir itself is the atomic claim, including under timestamp collisions.
        self.path.mkdir(parents=True, exist_ok=False)
        self.closed = False
        self._entered = False
        self.manifest: dict[str, object] = {
            "schema_version": EVIDENCE_SCHEMA_VERSION,
            "validation_policy_version": POLICY_VERSION,
            "execution_metrics_schema": METRICS_SCHEMA_VERSION,
            "command": list(command or tuple(sys.orig_argv)),
            "cwd": str(Path.cwd()),
            "source_root": str(self.root),
            "tool_versions": tool_versions(),
            "limits": dict(limits) if limits is not None else {"enforced": False},
            "git_source_before": self._git_before.as_dict(),
            "evidence_mode": evidence_mode,
            "cacheable": False,
            "reusable": False,
            "acceptance_verified": False,
            "started_at": utc_now(),
            "outcome": "running",
            "steps": [],
        }
        self._write()
        atexit.register(self._unfinished)

    def _write(self) -> None:
        temporary = self.path / f".manifest-{uuid4().hex}.tmp"
        temporary.write_text(json.dumps(self.manifest, indent=2) + "\n")
        os.replace(temporary, self.path / "manifest.json")

    def record(self, record: Mapping[str, object]) -> None:
        if self.closed:
            raise ValueError("cannot append to completed evidence")
        rows = self.manifest["steps"]
        assert isinstance(rows, list)
        rows.append(dict(record))
        self._write()

    def finish(self, outcome: str) -> None:
        if self.closed:
            raise ValueError("evidence already completed")
        from devtools.git_source import git_source

        after = git_source(self.root)
        same_identity = (
            after.commit == self._git_before.commit
            and after.tree == self._git_before.tree
            and after.object_format == self._git_before.object_format
        )
        self.manifest.update(
            git_source_after=after.as_dict(),
            cacheable=False,
            reusable=False,
            git_identity_unchanged=same_identity,
            finished_at=utc_now(),
            outcome=outcome if same_identity else "git_identity_changed",
        )
        self._write()
        self.closed = True
        atexit.unregister(self._unfinished)

    def mark_acceptance_complete(self) -> None:
        """Certify clean acceptance only after its checkout context succeeds."""
        if not self.closed:
            raise ValueError("acceptance evidence must finish before certification")
        if self.evidence_mode != "acceptance":
            raise ValueError("development evidence cannot certify acceptance")
        if self.manifest.get("outcome") != "completed":
            raise ValueError("only completed acceptance evidence can be certified")
        before = self.manifest.get("git_source_before")
        after = self.manifest.get("git_source_after")
        if before is None or after is None:
            raise ValueError("acceptance evidence is missing Git identities")
        if not isinstance(before, dict) or not isinstance(after, dict):
            raise TypeError("acceptance Git identities must be mappings")
        keys = ("git_commit", "git_tree", "git_object_format")
        if (
            before.get("git_dirty") is not False
            or after.get("git_dirty") is not False
            or any(before.get(key) != after.get(key) for key in keys)
        ):
            raise ValueError("acceptance Git identity is not clean and unchanged")
        self.manifest.update(
            acceptance_verified=True,
            cacheable=True,
            reusable=True,
            acceptance_verified_at=utc_now(),
        )
        self._write()
        self.closed = True
        atexit.unregister(self._unfinished)

    def mark_acceptance_failed(self, detail: str) -> None:
        """Revoke reuse if detached-checkout verification or cleanup failed."""
        if not self.closed:
            raise ValueError("acceptance evidence must finish before invalidation")
        if self.evidence_mode != "acceptance":
            raise ValueError("development evidence has no acceptance claim")
        from devtools.git_source import git_source

        try:
            after = git_source(self.root).as_dict()
        except (OSError, RuntimeError) as error:
            after = None
            detail = f"{detail}; final Git inspection failed: {error}"
        self.manifest.update(
            git_source_after_acceptance_checkout=after,
            acceptance_verification_error=detail,
            acceptance_verified=False,
            cacheable=False,
            reusable=False,
            outcome="acceptance_verification_failed",
            finished_at=utc_now(),
        )
        self._write()

    def _unfinished(self) -> None:
        if not self.closed:
            self.finish("interrupted")

    def __enter__(self) -> Self:
        if self.closed or self._entered:
            raise ValueError("evidence context cannot be entered more than once")
        self._entered = True
        self._bytecode_before = sys.dont_write_bytecode
        sys.dont_write_bytecode = True
        return self

    def __exit__(
        self,
        kind: type[BaseException] | None,
        error: BaseException | None,
        traceback: TracebackType | None,
    ) -> None:
        try:
            if error is not None:
                self.manifest["error"] = {
                    "type": type(error).__name__,
                    "detail": str(error)[:1024],
                }
            if not self.closed:
                self.finish(
                    "completed"
                    if kind is None
                    else "interrupted"
                    if isinstance(error, (KeyboardInterrupt, SystemExit))
                    else "failed"
                )
        finally:
            sys.dont_write_bytecode = self._bytecode_before


_REPORT_RUNS: dict[tuple[Path, Path | None], EvidenceRun] = {}
_ACTIVE_RUN: EvidenceRun | None = None


def report_run(root: Path | None = None) -> EvidenceRun:
    """Share one invocation's evidence across its JSON, CSV and Markdown outputs."""
    import argparse

    root = (root or repository_root()).resolve()
    if _ACTIVE_RUN is not None and _ACTIVE_RUN.root == root and not _ACTIVE_RUN.closed:
        return _ACTIVE_RUN
    parser = argparse.ArgumentParser(add_help=False, allow_abbrev=False)
    parser.add_argument("--output-dir", type=Path)
    options, _ = parser.parse_known_args()
    root = (root or repository_root()).resolve()
    destination = options.output_dir.resolve() if options.output_dir else None
    key = (root, destination)
    run = _REPORT_RUNS.get(key)
    if run is None or run.closed:
        run = EvidenceRun(root=root, output_dir=destination)
        _REPORT_RUNS[key] = run
    return run


class _ReportStream(io.TextIOBase):
    """Tee a probe's existing stdout into its owned run, with bounded retention."""

    def __init__(self, original: TextIO, log: TextIO) -> None:
        self.original = original
        self.log = log
        self.remaining = 8 * 1024**2

    def write(self, text: str) -> int:
        size = len(text.encode("utf-8"))
        if size > self.remaining:
            raise ValueError("probe stdout exceeds the 8-MiB retained-log limit")
        self.remaining -= size
        self.log.write(text)
        return self.original.write(text)

    def flush(self) -> None:
        if not self.log.closed:
            self.log.flush()
        if not self.original.closed:
            self.original.flush()


def run_reported(main: Callable[[], int | None]) -> int:
    """Common --output-dir interface for existing probe entry points."""
    guarded = _guard_standalone_command()
    if guarded is not None:
        return guarded
    import argparse

    parser = argparse.ArgumentParser(add_help=False, allow_abbrev=False)
    parser.add_argument("--output-dir", type=Path)
    _, remaining = parser.parse_known_args()
    if "--worker" in remaining:
        result = main()
        return 0 if result is None else result
    global _ACTIVE_RUN
    previous_run = _ACTIVE_RUN
    run = report_run()
    _ACTIVE_RUN = run
    original = sys.argv
    sys.argv = [sys.argv[0], *remaining]
    try:
        with run, (run.path / "stdout.log").open("x") as log:
            with contextlib.redirect_stdout(_ReportStream(sys.stdout, log)):
                result = main()
            code = 0 if result is None else result
            run.finish("completed" if code == 0 else "failed")
            return code if run.manifest["outcome"] != "git_identity_changed" else 1
    finally:
        _ACTIVE_RUN = previous_run
        sys.argv = original


def _guard_standalone_command() -> int | None:
    """Re-exec a direct developer command through the shared process guard."""
    if _trusted_guard_context():
        return None
    from devtools.checks.process_guard import run_guarded
    from devtools.checks.test_run_evidence import PROVENANCE_MODE_ENV
    from devtools.checks.validation_policy import PYTHON_COMMAND

    original_arguments = tuple(sys.orig_argv[1:])
    if not original_arguments:
        raise RuntimeError("cannot recover argv for guarded developer command")
    command = (sys.executable, *original_arguments)
    from devtools.git_source import git_source

    cwd = Path.cwd().resolve()
    source_before = git_source(cwd)
    root = repository_root()
    requested = None
    for index, argument in enumerate(command):
        if argument == "--output-dir" and index + 1 < len(command):
            requested = Path(command[index + 1]).resolve()
            break
    stamp = datetime.now(UTC).strftime("%Y%m%dT%H%M%SZ")
    run_path = root / "results" / "runs" / f"{stamp}-{uuid4().hex}"
    run_path.mkdir(parents=True, exist_ok=False)
    probe_output = run_path / "probe"
    child_command = command
    is_worker = "--worker" in command
    if not is_worker and requested is None:
        child_command = (*command, "--output-dir", str(probe_output))
    guard_output = run_path / "guard.log"
    try:
        child_environment = dict(os.environ)
        child_environment[PROVENANCE_MODE_ENV] = "development"
        child_environment.pop("NUMBER_COMPILER_ACCEPTANCE_ROOT", None)
        source_path = str((root / "src").resolve())
        existing_path = child_environment.get("PYTHONPATH")
        child_environment["PYTHONPATH"] = (
            source_path
            if not existing_path
            else os.pathsep.join((source_path, existing_path))
        )
        result = run_guarded(
            tuple(child_command),
            cwd=cwd,
            output=guard_output,
            timeout=PYTHON_COMMAND.timeout_seconds,
            memory_bytes=PYTHON_COMMAND.memory_bytes,
            environment=child_environment,
        )
    except (OSError, RuntimeError, ValueError) as error:
        payload = {
            "schema_version": EVIDENCE_SCHEMA_VERSION,
            "outcome": "incomplete",
            "detail": str(error),
            "git_source_before": source_before.as_dict(),
            "evidence_mode": "development",
            "cacheable": False,
            "reusable": False,
        }
        (run_path / "guard.json").write_text(json.dumps(payload, indent=2) + "\n")
        print(f"guarded command incomplete: {error}", file=sys.stderr)
        return 1
    content = guard_output.read_text(errors="replace") if guard_output.exists() else ""
    if content:
        sys.stdout.write(content)
        sys.stdout.flush()
    source_after = git_source(cwd)
    outcome = result.outcome
    payload = {
        "schema_version": EVIDENCE_SCHEMA_VERSION,
        "outcome": outcome,
        "detail": result.detail,
        "child_returncode": result.child_returncode,
        "elapsed_seconds": result.elapsed_seconds,
        "sampled_peak_bytes": result.sampled_peak_bytes,
        "memory_limit_bytes": result.memory_limit_bytes,
        "memory_measurement": result.memory_measurement,
        "cleanup_confirmed": result.cleanup_confirmed,
        "git_source_before": source_before.as_dict(),
        "git_source_after": source_after.as_dict(),
        "evidence_mode": "development",
        "cacheable": False,
        "reusable": False,
    }
    (run_path / "guard.json").write_text(json.dumps(payload, indent=2) + "\n")
    nested_manifest = probe_output / "manifest.json"
    if outcome != "completed" and nested_manifest.is_file():
        try:
            nested = json.loads(nested_manifest.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            nested = None
        if isinstance(nested, dict) and nested.get("outcome") == "running":
            nested.update(
                outcome="incomplete",
                cacheable=False,
                reusable=False,
                guarded_command_outcome=outcome,
                guarded_command_detail=result.detail,
                finished_at=utc_now(),
            )
            nested_manifest.write_text(json.dumps(nested, indent=2) + "\n")
    if outcome != "completed":
        print(
            f"guarded command {outcome}: {result.detail}; evidence: {run_path}",
            file=sys.stderr,
        )
        return 1
    return result.child_returncode


def _trusted_guard_context() -> bool:
    """Reuse a live lease only when it already enforces Python command limits."""
    from devtools.checks.process_guard import (
        DEADLINE_ENV,
        MEMORY_BUDGET_ENV,
        guard_context_is_live,
    )
    from devtools.checks.validation_policy import (
        PYTHON_COMMAND_SECONDS,
        PYTHON_MEMORY_BYTES,
    )

    if not guard_context_is_live(os.environ):
        return False
    try:
        remaining = float(os.environ[DEADLINE_ENV]) - time.monotonic()
        memory_bytes = int(os.environ[MEMORY_BUDGET_ENV])
    except (KeyError, ValueError):
        return False
    return (
        0 < remaining <= PYTHON_COMMAND_SECONDS and memory_bytes <= PYTHON_MEMORY_BYTES
    )

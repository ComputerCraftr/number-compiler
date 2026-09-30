"""Fresh, source-bound developer evidence with explicit completion status."""

from __future__ import annotations

import atexit
import contextlib
import io
import json
import os
import platform
import shutil
import subprocess
import sys
from collections.abc import Callable, Mapping
from datetime import UTC, datetime
from importlib.metadata import PackageNotFoundError, version
from pathlib import Path
from types import TracebackType
from typing import Self, TextIO
from uuid import uuid4

from devtools.paths import repository_root


def utc_now() -> str:
    return datetime.now(UTC).isoformat()


def tool_versions() -> dict[str, str]:
    result = {"python": platform.python_version()}
    for name in ("pytest", "mypy", "ruff", "setuptools"):
        try:
            result[name] = version(name)
        except PackageNotFoundError:
            result[name] = "unavailable"
    for name, arguments in (("ruff", ("--version",)), ("isabelle", ("version",))):
        executable = shutil.which(name)
        if name == "isabelle":
            executable = os.environ.get("ISABELLE", executable)
            if (
                executable is None
                and Path("/Applications/Isabelle2025-2.app/bin/isabelle").is_file()
            ):
                executable = "/Applications/Isabelle2025-2.app/bin/isabelle"
        if executable is not None:
            try:
                probe = subprocess.run(
                    (executable, *arguments),
                    capture_output=True,
                    text=True,
                    timeout=2,
                    check=False,
                )
                result[name] = (
                    probe.stdout.strip() if probe.returncode == 0 else "unavailable"
                )
            except (OSError, subprocess.TimeoutExpired):
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
    ) -> None:
        from devtools.checks.test_run_evidence import (
            FINGERPRINT_VERSION,
            source_fingerprint,
        )
        from number_compiler.resources.temporal_diagnostics import (
            METRICS_SCHEMA_VERSION,
        )

        self.root = (root or repository_root()).resolve()
        stamp = datetime.now(UTC).strftime("%Y%m%dT%H%M%SZ")
        self.path = (
            output_dir or self.root / "results" / "runs" / f"{stamp}-{uuid4().hex}"
        )
        self.path = self.path.resolve()
        # mkdir itself is the atomic claim, including under timestamp collisions.
        self.path.mkdir(parents=True, exist_ok=False)
        from devtools.checks.process_guard import source_revision

        self._revision = source_revision(self.root)
        self.closed = False
        self.manifest: dict[str, object] = {
            "schema_version": 1,
            "fingerprint_version": FINGERPRINT_VERSION,
            "execution_metrics_schema": METRICS_SCHEMA_VERSION,
            "command": list(command or tuple(sys.orig_argv)),
            "cwd": str(Path.cwd()),
            "source_root": str(self.root),
            "tool_versions": tool_versions(),
            "limits": dict(limits) if limits is not None else {"enforced": False},
            "source_fingerprint_before": source_fingerprint(self.root),
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
        from devtools.checks.test_run_evidence import source_fingerprint

        if self.closed:
            raise ValueError("evidence already completed")
        from devtools.checks.process_guard import source_revision

        after = source_fingerprint(self.root)
        revision_unchanged = self._revision == source_revision(self.root)
        unchanged = (
            after == self.manifest["source_fingerprint_before"] and revision_unchanged
        )
        self.manifest.update(
            source_fingerprint_after=after,
            source_unchanged=unchanged,
            source_revision_unchanged=revision_unchanged,
            finished_at=utc_now(),
            outcome=outcome if unchanged else "source_changed",
        )
        self._write()
        self.closed = True
        atexit.unregister(self._unfinished)

    def _unfinished(self) -> None:
        if not self.closed:
            self.finish("interrupted")

    def __enter__(self) -> Self:
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
            return code if run.manifest["outcome"] != "source_changed" else 1
    finally:
        _ACTIVE_RUN = previous_run
        sys.argv = original

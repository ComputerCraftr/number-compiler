"""Opt-in bounded phase timing for interrupted serial pytest diagnostics.

The shared release runner loads this plugin and selects a fresh output path.
No runtime is cached; timings are observations, not alternate timeout settings.
"""

from __future__ import annotations

import cProfile
import json
from pathlib import Path
from time import perf_counter
from typing import TextIO

import pytest

# Absolute ceiling. The effective record allowance is narrowed to the collected
# selection when pytest finishes collection.
_RECORD_SAFETY_LIMIT = 65536
_BYTE_LIMIT = 8 * 1024 * 1024
_FAILURE_TEXT_LIMIT = 8192


def _bounded_longrepr(value: object, limit: int) -> tuple[str, bool]:
    """Keep a useful UTF-8-safe exception excerpt within one record budget."""
    text = str(value)
    encoded = text.encode("utf-8")
    if len(encoded) <= limit:
        return text, False
    suffix = b"\n...[longrepr truncated]"
    if limit < len(suffix):
        return suffix[:limit].decode("ascii"), True
    prefix = encoded[: limit - len(suffix)].decode("utf-8", errors="ignore")
    return prefix + suffix.decode("ascii"), True


class PhaseTiming:
    def __init__(
        self,
        path: Path,
        profile_path: Path | None = None,
        *,
        record_safety_limit: int = _RECORD_SAFETY_LIMIT,
        byte_limit: int = _BYTE_LIMIT,
        failure_text_limit: int = _FAILURE_TEXT_LIMIT,
    ) -> None:
        for name, value in (
            ("record safety limit", record_safety_limit),
            ("byte limit", byte_limit),
            ("failure text limit", failure_text_limit),
        ):
            if type(value) is not int or value < 1:
                raise ValueError(f"{name} must be a positive exact integer")
        self.stream: TextIO = path.open("x", encoding="utf-8")
        self.records = 0
        self.bytes = 0
        self.truncated = False
        self.closed = False
        self.collection_started = 0.0
        self.record_safety_limit = record_safety_limit
        self.record_limit = self.record_safety_limit
        self.byte_limit = byte_limit
        self.failure_text_limit = failure_text_limit
        self.profile_path = profile_path
        self.profiler = None if profile_path is None else cProfile.Profile()
        if self.profiler is not None:
            self.profiler.enable()

    def _write(self, record: dict[str, object]) -> None:
        encoded = json.dumps(record, separators=(",", ":")) + "\n"
        self.stream.write(encoded)
        self.stream.flush()
        self.bytes += len(encoded.encode("utf-8"))

    def pytest_collection(self) -> None:
        self.collection_started = perf_counter()

    def pytest_collection_finish(self, session: pytest.Session) -> None:
        # A normal pytest item emits setup, call, and teardown reports. Keep
        # room for the collection and session-finish records plus the existing
        # truncation marker reserve, while retaining an absolute safety ceiling
        # for retries or unusual reporters.
        selection_allowance = 3 * len(session.items) + 3
        self.record_limit = min(self.record_safety_limit, selection_allowance)
        self._write(
            {
                "phase": "collection",
                "seconds": perf_counter() - self.collection_started,
                "selected_items": len(session.items),
            }
        )
        self.records += 1

    def pytest_runtest_logreport(self, report: pytest.TestReport) -> None:
        if self.truncated:
            return
        record: dict[str, object] = {
            "nodeid": report.nodeid,
            "phase": report.when,
            "outcome": report.outcome,
            "seconds": report.duration,
        }
        if report.outcome == "failed":
            longrepr, truncated = _bounded_longrepr(
                report.longrepr, self.failure_text_limit
            )
            record["failure_longrepr"] = longrepr
            record["failure_longrepr_truncated"] = truncated
        size = len(json.dumps(record, separators=(",", ":")).encode("utf-8")) + 1
        if (
            self.records >= self.record_limit - 2
            or self.bytes + size + 256 > self.byte_limit
        ):
            self.truncated = True
            self._write({"status": "truncated", "records": self.records})
            return
        self._write(record)
        self.records += 1

    def pytest_sessionfinish(self, exitstatus: int) -> None:
        self._write(
            {
                "status": "finished",
                "exitstatus": int(exitstatus),
                "records": self.records,
                "truncated": self.truncated,
            }
        )

    def pytest_unconfigure(self) -> None:
        if not self.closed:
            if self.profiler is not None:
                self.profiler.disable()
                assert self.profile_path is not None
                self.profiler.dump_stats(str(self.profile_path))
            self.stream.close()
            self.closed = True


def pytest_addoption(parser: pytest.Parser) -> None:
    parser.addoption("--timing-output", help="New bounded diagnostic JSONL file")
    parser.addoption("--profile-output", help="Optional cProfile diagnostic output")


def pytest_configure(config: pytest.Config) -> None:
    path = config.getoption("timing_output")
    if path is None:
        return
    if type(path) is not str:
        raise TypeError("timing output requires a filesystem path")
    profile = config.getoption("profile_output")
    config.pluginmanager.register(
        PhaseTiming(Path(path), None if profile is None else Path(profile)),
        "bounded-phase-timing",
    )

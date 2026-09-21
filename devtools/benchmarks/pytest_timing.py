"""Opt-in bounded phase timing for interrupted serial pytest diagnostics.

Use ``pytest -p devtools.benchmarks.pytest_timing --timing-output NEW.jsonl``.
The ordinary release run does not load this plugin. No runtime is cached.
"""

from __future__ import annotations

import json
from pathlib import Path
from time import perf_counter
from typing import TextIO

import pytest

_RECORD_LIMIT = 32768
_BYTE_LIMIT = 8 * 1024 * 1024


class PhaseTiming:
    def __init__(self, path: Path) -> None:
        self.stream: TextIO = path.open("x", encoding="utf-8")
        self.records = 0
        self.bytes = 0
        self.truncated = False
        self.closed = False
        self.collection_started = 0.0

    def _write(self, record: dict[str, object]) -> None:
        encoded = json.dumps(record, separators=(",", ":")) + "\n"
        self.stream.write(encoded)
        self.stream.flush()
        self.bytes += len(encoded.encode("utf-8"))

    def pytest_collection(self) -> None:
        self.collection_started = perf_counter()

    def pytest_collection_finish(self, session: pytest.Session) -> None:
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
        size = len(json.dumps(record, separators=(",", ":")).encode("utf-8")) + 1
        if self.records >= _RECORD_LIMIT - 2 or self.bytes + size + 256 > _BYTE_LIMIT:
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
            self.stream.close()
            self.closed = True


def pytest_addoption(parser: pytest.Parser) -> None:
    parser.addoption("--timing-output", help="New bounded diagnostic JSONL file")


def pytest_configure(config: pytest.Config) -> None:
    path = config.getoption("timing_output")
    if path is None:
        return
    if type(path) is not str:
        raise TypeError("timing output requires a filesystem path")
    config.pluginmanager.register(PhaseTiming(Path(path)), "bounded-phase-timing")

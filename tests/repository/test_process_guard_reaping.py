"""A late worker must be identified before its leader is reaped."""

from __future__ import annotations

import os
import subprocess
from pathlib import Path

import pytest

from devtools.checks import process_guard
from tests.support.process_guard import zero_memory_reader


def test_worker_spawned_after_live_sample_is_bound_before_poll(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    live = process_guard.ProcessIdentity(123, 1, 123, "S", "leader")
    exited = process_guard.ProcessIdentity(123, 1, 123, "Z", "leader")
    worker = process_guard.ProcessIdentity(124, 1, 123, "S", "worker")
    snapshots = iter(({123: live}, {123: exited, 124: worker}, {124: worker}))
    snapshot_calls = 0
    read_fd, write_fd = os.pipe()
    os.close(write_fd)

    class Child:
        pid = 123
        returncode: int | None = None
        stdout = os.fdopen(read_fd, "rb", buffering=0)

        def poll(self) -> int:
            assert snapshot_calls >= 2, "leader reaped before its exit snapshot"
            self.returncode = 0
            return 0

    child = Child()

    def snapshot() -> dict[int, process_guard.ProcessIdentity]:
        nonlocal snapshot_calls
        snapshot_calls += 1
        return next(snapshots)

    def launch(*args: object, **kwargs: object) -> Child:
        return child

    def retire(*args: object, **kwargs: object) -> int:
        tracked = args[1]
        assert isinstance(tracked, dict) and worker.pid in tracked
        return 0

    monkeypatch.setattr(subprocess, "Popen", launch)
    monkeypatch.setattr(process_guard, "process_snapshot", snapshot)
    monkeypatch.setattr(process_guard, "memory_reader", zero_memory_reader)
    monkeypatch.setattr(process_guard, "retire_process", retire)
    result = process_guard.run_guarded(
        ("late-exit-test",),
        output=tmp_path / "worker.log",
        timeout=1,
        interval=0.001,
        lock_path=tmp_path / "lock",
    )
    assert result.outcome == "descendants_retired"
    assert snapshot_calls == 3
    assert child.stdout.closed

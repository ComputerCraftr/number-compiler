"""Linux procfs memory-read race regressions for the developer watchdog."""

from __future__ import annotations

import errno
import sys
import time
from collections.abc import Callable
from pathlib import Path
from typing import cast

import pytest

from devtools.checks import process_guard


def _linux_memory_reader_for_status(
    monkeypatch: pytest.MonkeyPatch, status: str
) -> Callable[[int], int]:
    monkeypatch.setattr(sys, "platform", "linux")

    def read_status(_path: Path) -> str:
        return status

    monkeypatch.setattr(Path, "read_text", read_status)
    return process_guard.memory_reader()[1]


@pytest.mark.parametrize("state", ["Z (zombie)", "X (dead)", "x (dead)"])
def test_linux_memory_reader_treats_exited_process_without_rss_as_zero(
    monkeypatch: pytest.MonkeyPatch, state: str
) -> None:
    read_memory = _linux_memory_reader_for_status(
        monkeypatch, f"Name:\tworker\nState:\t{state}\n"
    )

    assert read_memory(123) == 0


def test_linux_memory_reader_marks_missing_live_rss_as_retryable(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    read_memory = _linux_memory_reader_for_status(
        monkeypatch, "Name:\tworker\nState:\tS (sleeping)\n"
    )

    with pytest.raises(OSError) as error:
        read_memory(123)

    assert error.value.errno == errno.EAGAIN


def test_linux_memory_reader_retries_missing_rss_during_child_startup(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(sys, "platform", "linux")
    statuses = iter(
        (
            "Name:\tworker\nState:\tR (running)\n",
            "Name:\tworker\nState:\tS (sleeping)\nVmRSS:\t4 kB\n",
        )
    )
    sleeps: list[float] = []

    def read_status(_path: Path) -> str:
        return next(statuses)

    monkeypatch.setattr(Path, "read_text", read_status)
    monkeypatch.setattr(time, "sleep", sleeps.append)

    read_memory = process_guard.memory_reader()[1]

    assert read_memory(123) == 4 * 1024
    assert sleeps == [
        cast(
            float, object.__getattribute__(process_guard, "_LINUX_STATUS_RETRY_SECONDS")
        )
    ]


def test_transient_memory_read_race_rechecks_identity_and_fails_closed_for_live_process(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    member = process_guard.ProcessIdentity(123, 1, 123, "S", "original")
    snapshot_calls = 0
    read_calls = 0

    def snapshot() -> dict[int, process_guard.ProcessIdentity]:
        nonlocal snapshot_calls
        snapshot_calls += 1
        return {member.pid: member}

    def temporarily_unavailable(pid: int) -> int:
        nonlocal read_calls
        read_calls += 1
        raise OSError(errno.EAGAIN, "procfs status changed during read", pid)

    monkeypatch.setattr(process_guard, "process_snapshot", snapshot)

    with pytest.raises(OSError) as error:
        process_guard.read_member_footprint(member, temporarily_unavailable)

    assert error.value.errno == errno.EAGAIN
    assert snapshot_calls == 2
    assert read_calls == 2


def test_transient_memory_read_race_discards_exited_identity(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    member = process_guard.ProcessIdentity(123, 1, 123, "X", "original")

    def temporarily_unavailable(pid: int) -> int:
        raise OSError(errno.EAGAIN, "procfs status changed during read", pid)

    monkeypatch.setattr(process_guard, "process_snapshot", lambda: {member.pid: member})

    assert process_guard.read_member_footprint(member, temporarily_unavailable) == 0

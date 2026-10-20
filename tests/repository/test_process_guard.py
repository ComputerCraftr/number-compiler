"""Small worker probes for the developer watchdog; no algorithm stress fixtures."""

from __future__ import annotations

import errno
import fcntl
import json
import os
import signal
import subprocess
import sys
import time
from collections.abc import Callable, Iterator, Mapping
from functools import partial
from pathlib import Path
from typing import BinaryIO, Literal
from uuid import uuid4

import pytest

from devtools.checks import process_guard
from devtools.checks.validation_policy import (
    POLICY_VERSION,
    PYTHON_COMMAND_SECONDS,
    PYTHON_MEMORY_BYTES,
)
from devtools.paths import repository_root
from tests.support.process_guard import zero_memory_reader


class _FinishedChild:
    pid = 123
    returncode: int | None = 0

    def wait(self, timeout: float | None = None) -> int:
        return 0


class _FinishedPipeChild(_FinishedChild):
    def __init__(self, pid: int, stdout: BinaryIO) -> None:
        self.pid = pid
        self.stdout = stdout

    def poll(self) -> int:
        return 0


class _InitiallyUnboundPipeChild(_FinishedPipeChild):
    def __init__(self, pid: int, stdout: BinaryIO) -> None:
        super().__init__(pid, stdout)
        self.returncode = None
        self.poll_calls = 0

    def poll(self) -> int:
        self.poll_calls += 1
        self.returncode = 0
        return 0

    def wait(self, timeout: float | None = None) -> int:
        self.returncode = 0
        return 0


def _record_killpg(signals: list[tuple[int, int]], group: int, number: int) -> None:
    signals.append((group, number))


def _fixed_memory_reader(value: int) -> tuple[str, Callable[[int], int]]:
    def read(_pid: int) -> int:
        return value

    return "test", read


def _no_retirement(*args: object, **kwargs: object) -> int:
    del args, kwargs
    return 0


def _ignore_tracked_signal(
    tracked: Mapping[int, process_guard.ProcessIdentity], number: int
) -> None:
    del tracked, number


def _record_tracked_signal(
    signalled: list[tuple[int, ...]],
    tracked: Mapping[int, process_guard.ProcessIdentity],
    number: int,
) -> None:
    del number
    signalled.append(tuple(sorted(tracked)))


def _unbound_signal_probe(
    monkeypatch: pytest.MonkeyPatch,
) -> tuple[_InitiallyUnboundPipeChild, list[tuple[int, int]]]:
    read_fd, write_fd = os.pipe()
    os.close(write_fd)
    child = _InitiallyUnboundPipeChild(123, os.fdopen(read_fd, "rb", buffering=0))
    signals: list[tuple[int, int]] = []
    monkeypatch.setattr(
        os,
        "killpg",
        partial(_record_killpg, signals),
    )
    return child, signals


def _run_guarded_with_snapshots(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    child: _FinishedPipeChild,
    snapshot_rows: tuple[dict[int, process_guard.ProcessIdentity] | Exception, ...],
    *,
    timeout: float = 35,
    interval: float = 0.05,
    fake_retirement: bool = True,
    repeat_last_snapshot: bool = False,
) -> tuple[process_guard.GuardResult, int]:
    snapshots: Iterator[dict[int, process_guard.ProcessIdentity] | Exception] = iter(
        snapshot_rows
    )
    snapshot_calls = 0
    last_row: dict[int, process_guard.ProcessIdentity] = {}

    def snapshot() -> dict[int, process_guard.ProcessIdentity]:
        nonlocal last_row, snapshot_calls
        snapshot_calls += 1
        try:
            row = next(snapshots)
        except StopIteration as error:
            if repeat_last_snapshot:
                return last_row
            raise RuntimeError("process snapshot fixture exhausted") from error
        if isinstance(row, Exception):
            raise row
        last_row = row
        return row

    def fake_popen(*args: object, **kwargs: object) -> _FinishedPipeChild:
        del args, kwargs
        return child

    monkeypatch.setattr(subprocess, "Popen", fake_popen)
    monkeypatch.setattr(process_guard, "process_snapshot", snapshot)
    monkeypatch.setattr(process_guard, "memory_reader", zero_memory_reader)
    if fake_retirement:
        monkeypatch.setattr(process_guard, "retire_process", _no_retirement)

    result = process_guard.run_guarded(
        ("snapshot-test-child",),
        output=tmp_path / "worker.log",
        timeout=timeout,
        interval=interval,
        lock_path=tmp_path / "lock",
    )
    return result, snapshot_calls


@pytest.mark.parametrize("child_outcome", ["completed", "child_failed"])
def test_guarded_cli_uses_run_local_proof_generation(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    child_outcome: str,
) -> None:
    monkeypatch.setenv(process_guard.PROOF_GENERATION_ENV, "foreign-generation")
    report = tmp_path / "report.json"
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "process_guard",
            "--output",
            str(tmp_path / "output.log"),
            "--report",
            str(report),
            "--",
            "unused-test-command",
        ],
    )

    def run(
        command: tuple[str, ...],
        *,
        output: Path,
        timeout: float,
        memory_bytes: int,
        environment: Mapping[str, str],
    ) -> process_guard.GuardResult:
        assert command == ("unused-test-command",)
        generation = environment[process_guard.PROOF_GENERATION_ENV]
        assert generation != "foreign-generation"
        assert len(generation) == 32
        assert int(generation, 16) >= 0
        return process_guard.GuardResult(
            1,
            child_outcome,
            int(child_outcome != "completed"),
            0.1,
            1,
            memory_bytes,
            "test",
            0.05,
            1,
            0,
            "",
        )

    monkeypatch.setattr(process_guard, "run_guarded", run)
    assert process_guard.main() == int(child_outcome != "completed")
    evidence = json.loads(report.read_text())
    assert len(evidence["proof_generation"]) == 32
    assert int(evidence["proof_generation"], 16) >= 0
    assert not any("fingerprint" in key or "source_revision" in key for key in evidence)
    assert evidence["outcome"] == child_outcome
    assert evidence["child_returncode"] == int(child_outcome != "completed")


def test_completed_child_has_real_footprint_and_log(tmp_path: Path) -> None:
    result = process_guard.run_guarded(
        (sys.executable, "-c", "import time; print('done'); time.sleep(.15)"),
        output=tmp_path / "worker.log",
        lock_path=tmp_path / "lock",
    )
    assert result.outcome == "completed"
    assert result.child_returncode == 0
    assert result.samples > 0
    assert result.sampled_peak_bytes is not None
    assert result.sampled_peak_bytes > 0
    assert (tmp_path / "worker.log").read_text().strip() == "done"


def test_proof_generation_reaches_child_without_writing_bytecode(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    source = tmp_path / "src"
    source.mkdir()
    (source / "sample.py").write_text("value = 1\n")
    output = tmp_path / "results" / "child.log"
    report = output.with_suffix(".json")
    child_lock = tmp_path / "child.lock"
    child_lock.touch()
    monkeypatch.setattr(
        process_guard,
        "run_guarded",
        partial(process_guard.run_guarded, lock_path=child_lock),
    )
    monkeypatch.setenv(process_guard.PROOF_GENERATION_ENV, "foreign-owner")
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "process_guard",
            "--output",
            str(output),
            "--report",
            str(report),
            "--",
            sys.executable,
            "-c",
            (
                "import os, sys; sys.path.insert(0, sys.argv[1]); import sample; "
                "print(os.environ['NUMBER_COMPILER_PROOF_GENERATION'])"
            ),
            str(source),
        ],
    )
    assert process_guard.main() == 0
    evidence = json.loads(report.read_text())
    assert output.read_text().strip() == evidence["proof_generation"]
    assert evidence["proof_generation"] != "foreign-owner"
    assert len(evidence["proof_generation"]) == 32
    assert not (source / "__pycache__").exists()


def test_worker_uses_explicit_working_directory(tmp_path: Path) -> None:
    working = tmp_path / "working"
    working.mkdir()
    result = process_guard.run_guarded(
        (
            sys.executable,
            "-c",
            "import pathlib; print(pathlib.Path.cwd())",
        ),
        output=tmp_path / "worker.log",
        cwd=working,
        lock_path=tmp_path / "lock",
    )
    assert result.outcome == "completed"
    observed = Path((tmp_path / "worker.log").read_text().strip())
    assert observed.resolve() == working.resolve()


def test_nested_guard_cannot_raise_parent_deadline_or_memory(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    parent_deadline = time.monotonic() + 30
    monkeypatch.setenv(process_guard.GUARDED_COMMAND_ENV, uuid4().hex)
    monkeypatch.setenv(process_guard.GUARDED_PARENT_PID_ENV, str(os.getppid()))
    monkeypatch.setenv(process_guard.DEADLINE_ENV, str(parent_deadline))
    monkeypatch.setenv(process_guard.MEMORY_BUDGET_ENV, str(1024**3))
    child_environment = dict(os.environ)
    child_environment[process_guard.DEADLINE_ENV] = str(time.monotonic() + 90)
    child_environment[process_guard.MEMORY_BUDGET_ENV] = str(8 * 1024**3)
    result = process_guard.run_guarded(
        (
            sys.executable,
            "-c",
            "import os; print(os.environ['NUMBER_COMPILER_DEADLINE_MONOTONIC'])",
        ),
        output=tmp_path / "nested.log",
        timeout=120,
        memory_bytes=8 * 1024**3,
        environment=child_environment,
    )
    assert result.outcome == "completed"
    assert result.memory_limit_bytes == 1024**3
    assert float((tmp_path / "nested.log").read_text()) <= parent_deadline


def test_nested_guard_lease_requires_a_valid_supervisor_ancestor() -> None:
    environment = {
        process_guard.GUARDED_COMMAND_ENV: uuid4().hex,
        process_guard.GUARDED_PARENT_PID_ENV: str(os.getppid()),
        process_guard.DEADLINE_ENV: str(time.monotonic() + 30),
        process_guard.MEMORY_BUDGET_ENV: str(1024**3),
    }
    assert process_guard.guard_context_is_live(environment)
    environment[process_guard.GUARDED_PARENT_PID_ENV] = "1"
    assert not process_guard.guard_context_is_live(environment)
    environment[process_guard.GUARDED_PARENT_PID_ENV] = str(os.getppid())
    environment[process_guard.GUARDED_COMMAND_ENV] = "1"
    assert not process_guard.guard_context_is_live(environment)


def test_propagated_guard_lease_allows_authenticated_grandchild(tmp_path: Path) -> None:
    grandchild = (
        "from devtools.checks.process_guard import guard_context_is_live; "
        "import os; print(guard_context_is_live(os.environ))"
    )
    worker = (
        "import subprocess,sys; "
        f"child=subprocess.run([sys.executable,'-c',{grandchild!r}],"
        "check=True,capture_output=True,text=True); "
        "print(child.stdout.strip())"
    )
    output = tmp_path / "guarded-grandchild.log"
    result = process_guard.run_guarded(
        (sys.executable, "-c", worker),
        output=output,
        cwd=repository_root(),
        timeout=10,
    )
    assert result.outcome == "completed"
    assert output.read_text(encoding="utf-8").strip() == "True"


def _assert_timeout_reaped(result: process_guard.GuardResult, log: Path) -> None:
    assert result.outcome == "timeout"
    pid = int(log.read_text().splitlines()[0])
    _assert_processes_retired((pid,))


def _assert_processes_retired(process_ids: tuple[int, ...]) -> None:
    snapshot = process_guard.process_snapshot()
    for pid in process_ids:
        process = snapshot.get(pid)
        assert process is None or process.state.startswith(("Z", "X", "x")), (
            f"process {pid} remains live in state {process.state if process else None!r}"
        )


def test_timeout_reaps_worker(tmp_path: Path) -> None:
    log = tmp_path / "worker.log"
    result = process_guard.run_guarded(
        (
            sys.executable,
            "-c",
            "import os,time; print(os.getpid(), flush=True); time.sleep(30)",
        ),
        output=log,
        timeout=0.5,
        lock_path=tmp_path / "lock",
    )
    _assert_timeout_reaped(result, log)


def test_standalone_guard_report_records_command_and_effective_policy(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    output = tmp_path / "command.log"
    report = tmp_path / "command.json"
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "process_guard",
            "--output",
            str(output),
            "--report",
            str(report),
            "--",
            sys.executable,
            "-c",
            "pass",
        ],
    )
    assert process_guard.main() == 0
    observed = json.loads(report.read_text(encoding="utf-8"))
    assert observed["policy_version"] == POLICY_VERSION
    assert observed["command"] == [sys.executable, "-c", "pass"]
    assert observed["cwd"] == str(Path.cwd())
    assert observed["timeout_seconds"] == PYTHON_COMMAND_SECONDS
    assert (
        0 < observed["effective_remaining_seconds_at_start"] <= PYTHON_COMMAND_SECONDS
    )
    assert observed["effective_memory_bytes"] <= PYTHON_MEMORY_BYTES


def test_active_test_deadline_reaps_stalled_pytest_child(tmp_path: Path) -> None:
    marker = tmp_path / "active-test.json"
    timeout_seconds = 0.25
    started = time.monotonic() - 0.12
    marker.write_text(
        json.dumps(
            {
                "nodeid": "tests/example.py::test_native_stall",
                "started_monotonic": started,
                "deadline_monotonic": started + timeout_seconds,
            }
        )
    )
    log = tmp_path / "worker.log"
    result = process_guard.run_guarded(
        (sys.executable, "-c", "import time; time.sleep(30)"),
        output=log,
        timeout=10,
        active_test_path=marker,
        active_test_timeout=timeout_seconds,
        lock_path=tmp_path / "lock",
    )
    assert result.outcome == "test_timeout"
    assert "test_native_stall" in result.detail
    assert result.cleanup_confirmed


def test_malformed_active_test_marker_fails_closed(tmp_path: Path) -> None:
    marker = tmp_path / "active-test.json"
    marker.write_text("not-json")
    result = process_guard.run_guarded(
        (sys.executable, "-c", "import time; time.sleep(30)"),
        output=tmp_path / "worker.log",
        timeout=10,
        active_test_path=marker,
        active_test_timeout=1,
        lock_path=tmp_path / "lock",
    )
    assert result.outcome == "measurement_failed"
    assert "active-test instrumentation failed" in result.detail
    assert result.cleanup_confirmed


def test_timeout_reaps_descendant_that_detaches_its_session(tmp_path: Path) -> None:
    log = tmp_path / "worker.log"
    result = process_guard.run_guarded(
        (
            sys.executable,
            "-c",
            (
                "import os,subprocess,sys,time; "
                "p=subprocess.Popen([sys.executable,'-c',"
                '"import os,time; os.setsid(); time.sleep(30)"]); '
                "print(p.pid, flush=True); time.sleep(30)"
            ),
        ),
        output=log,
        timeout=0.5,
        lock_path=tmp_path / "lock",
    )
    _assert_timeout_reaped(result, log)


def test_timeout_reaps_late_child_of_detached_descendant(tmp_path: Path) -> None:
    detached_code = (
        "import os,subprocess,sys,time; os.setsid(); time.sleep(.2); "
        f"p=subprocess.Popen({(sys.executable, '-c', 'import time; time.sleep(30)')!r}); "
        "print(p.pid, flush=True); time.sleep(30)"
    )
    worker_code = (
        f"import subprocess,time; p=subprocess.Popen({(sys.executable, '-c', detached_code)!r}); "
        "print(p.pid, flush=True); time.sleep(30)"
    )
    log = tmp_path / "worker.log"
    result = process_guard.run_guarded(
        (sys.executable, "-c", worker_code),
        output=log,
        timeout=0.8,
        lock_path=tmp_path / "lock",
    )
    assert result.outcome == "timeout"
    detached_pids = tuple(int(line) for line in log.read_text().splitlines())
    assert len(detached_pids) == 2
    _assert_processes_retired(detached_pids)


def test_pid_reuse_does_not_retain_a_tracked_process() -> None:
    expected = process_guard.ProcessIdentity(123, 1, 123, "S", "old")
    reused = process_guard.ProcessIdentity(123, 1, 123, "S", "new")
    assert process_guard.live_tracked_processes({123: expected}, {123: reused}) == ()


@pytest.mark.parametrize("snapshot_kind", ["missing", "zombie", "reused"])
def test_permission_race_discards_vanished_or_replaced_identity(
    monkeypatch: pytest.MonkeyPatch,
    snapshot_kind: Literal["missing", "zombie", "reused"],
) -> None:
    member = process_guard.ProcessIdentity(123, 1, 123, "S", "original")
    current: Mapping[int, process_guard.ProcessIdentity] = {
        "missing": {},
        "zombie": {123: process_guard.ProcessIdentity(123, 1, 123, "Z", "original")},
        "reused": {123: process_guard.ProcessIdentity(123, 1, 123, "S", "replacement")},
    }[snapshot_kind]
    read_pids: list[int] = []

    def denied(pid: int) -> int:
        read_pids.append(pid)
        raise PermissionError(errno.EPERM, "process exited during footprint read", pid)

    monkeypatch.setattr(process_guard, "process_snapshot", lambda: current)

    assert process_guard.read_member_footprint(member, denied) == 0
    assert read_pids == [member.pid]


def test_permission_race_rechecks_identity_after_bounded_retry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    member = process_guard.ProcessIdentity(123, 1, 123, "S", "original")
    sequence: tuple[Mapping[int, process_guard.ProcessIdentity], ...] = (
        {member.pid: member},
        {},
    )
    snapshots: Iterator[Mapping[int, process_guard.ProcessIdentity]] = iter(sequence)
    read_pids: list[int] = []

    def denied(pid: int) -> int:
        read_pids.append(pid)
        raise PermissionError(errno.EPERM, "process exited during footprint read", pid)

    monkeypatch.setattr(process_guard, "process_snapshot", lambda: next(snapshots))

    assert process_guard.read_member_footprint(member, denied) == 0
    assert read_pids == [member.pid, member.pid]


def test_permission_failure_for_same_live_identity_remains_fail_closed(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    member = process_guard.ProcessIdentity(123, 1, 123, "S", "original")
    snapshot_calls = 0
    read_calls = 0

    def snapshot() -> dict[int, process_guard.ProcessIdentity]:
        nonlocal snapshot_calls
        snapshot_calls += 1
        return {member.pid: member}

    def denied(pid: int) -> int:
        nonlocal read_calls
        read_calls += 1
        raise PermissionError(
            errno.EPERM, "live process footprint is inaccessible", pid
        )

    monkeypatch.setattr(process_guard, "process_snapshot", snapshot)

    with pytest.raises(PermissionError, match="live process footprint is inaccessible"):
        process_guard.read_member_footprint(member, denied)
    assert snapshot_calls == 2
    assert read_calls == 2


def test_reused_root_does_not_adopt_its_new_descendants() -> None:
    expected = process_guard.ProcessIdentity(123, 1, 123, "S", "old")
    reused = process_guard.ProcessIdentity(123, 1, 123, "S", "new")
    child = process_guard.ProcessIdentity(124, 123, 124, "S", "child")
    tracked: dict[int, process_guard.ProcessIdentity] = {}
    assert (
        process_guard.authorized_descendants(
            expected, tracked, {123: reused, 124: child}
        )
        == ()
    )
    assert tracked == {}


@pytest.mark.parametrize("descendant_survives", [False, True])
def test_child_exit_uses_fresh_descendant_snapshot(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    descendant_survives: bool,
) -> None:
    root = process_guard.ProcessIdentity(123, 1, 123, "S", "root")
    descendant = process_guard.ProcessIdentity(124, 123, 123, "S", "worker")
    read_fd, write_fd = os.pipe()
    os.close(write_fd)
    child = _FinishedPipeChild(root.pid, os.fdopen(read_fd, "rb", buffering=0))
    result, snapshot_calls = _run_guarded_with_snapshots(
        tmp_path,
        monkeypatch,
        child,
        (
            {root.pid: root, descendant.pid: descendant},
            {descendant.pid: descendant} if descendant_survives else {},
        ),
    )

    assert result.outcome == (
        "descendants_retired" if descendant_survives else "completed"
    )
    assert snapshot_calls == 2
    assert child.stdout.closed


def test_guard_binds_fast_child_before_reaping_it(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    root = process_guard.ProcessIdentity(123, 1, 123, "Z", "root")
    descendant = process_guard.ProcessIdentity(124, 123, 123, "S", "worker")
    read_fd, write_fd = os.pipe()
    os.close(write_fd)
    child = _InitiallyUnboundPipeChild(root.pid, os.fdopen(read_fd, "rb", buffering=0))
    result, snapshot_calls = _run_guarded_with_snapshots(
        tmp_path,
        monkeypatch,
        child,
        (
            {},
            {root.pid: root, descendant.pid: descendant},
            {descendant.pid: descendant},
        ),
    )

    assert result.outcome == "descendants_retired"
    assert child.poll_calls == 1
    assert snapshot_calls == 3
    assert child.stdout.closed


def test_unbound_retirement_signals_only_while_child_pins_group_id(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    read_fd, write_fd = os.pipe()
    os.close(write_fd)
    child = _InitiallyUnboundPipeChild(123, os.fdopen(read_fd, "rb", buffering=0))
    events: list[tuple[str, int | None]] = []

    def signal_group(group: int, number: int) -> None:
        assert group == child.pid
        assert child.returncode is None
        events.append(("signal", number))

    def wait(timeout: float | None = None) -> int:
        assert timeout in {0.2, 2}
        events.append(("wait", None))
        child.returncode = 0
        return 0

    monkeypatch.setattr(os, "killpg", signal_group)
    monkeypatch.setattr(process_guard, "process_snapshot", dict)
    monkeypatch.setattr(process_guard, "_signal_tracked", _ignore_tracked_signal)
    monkeypatch.setattr(child, "wait", wait)

    assert process_guard.retire_process(child) == 0
    assert events[:3] == [
        ("signal", signal.SIGTERM),
        ("signal", signal.SIGKILL),
        ("wait", None),
    ]
    child.stdout.close()


def test_unbound_retirement_confirms_group_empty_before_wait(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    read_fd, write_fd = os.pipe()
    os.close(write_fd)
    child = _InitiallyUnboundPipeChild(123, os.fdopen(read_fd, "rb", buffering=0))
    member = process_guard.ProcessIdentity(124, 1, child.pid, "S", "member")
    sequence: tuple[Mapping[int, process_guard.ProcessIdentity], ...] = (
        {member.pid: member},
        {},
    )
    snapshots: Iterator[Mapping[int, process_guard.ProcessIdentity]] = iter(sequence)
    events: list[tuple[str, int | None]] = []

    def signal_group(group: int, number: int) -> None:
        assert group == child.pid
        assert child.returncode is None
        events.append(("signal", number))

    def snapshot() -> Mapping[int, process_guard.ProcessIdentity]:
        return next(snapshots)

    def wait(timeout: float | None = None) -> int:
        assert timeout == 2
        events.append(("wait", None))
        child.returncode = 0
        return 0

    monkeypatch.setattr(os, "killpg", signal_group)
    monkeypatch.setattr(process_guard, "process_snapshot", snapshot)
    monkeypatch.setattr(child, "wait", wait)

    assert process_guard.retire_process(child) == 0
    assert events == [
        ("signal", signal.SIGTERM),
        ("signal", signal.SIGKILL),
        ("signal", signal.SIGKILL),
        ("wait", None),
    ]
    child.stdout.close()


def test_reaped_unbound_child_does_not_authorize_process_group_signal(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    child = _FinishedChild()
    signals: list[tuple[int, int]] = []
    monkeypatch.setattr(
        os,
        "killpg",
        partial(_record_killpg, signals),
    )
    monkeypatch.setattr(process_guard, "process_snapshot", dict)
    monkeypatch.setattr(process_guard, "_signal_tracked", _ignore_tracked_signal)

    assert process_guard.retire_process(child) == 0
    assert signals == []


def test_unbound_child_still_obeys_guard_deadline(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    child, signals = _unbound_signal_probe(monkeypatch)

    result, _snapshot_calls = _run_guarded_with_snapshots(
        tmp_path,
        monkeypatch,
        child,
        ({}, {}),
        timeout=0.01,
        interval=0.001,
        fake_retirement=False,
        repeat_last_snapshot=True,
    )

    assert result.outcome == "timeout"
    assert child.poll_calls == 0
    assert signals == [
        (child.pid, signal.SIGTERM),
        (child.pid, signal.SIGKILL),
    ]
    assert child.stdout.closed


def test_retirement_snapshot_failure_is_reported_and_reaps_child(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    child, signals = _unbound_signal_probe(monkeypatch)

    result, _snapshot_calls = _run_guarded_with_snapshots(
        tmp_path,
        monkeypatch,
        child,
        ({}, RuntimeError("process snapshot unavailable")),
        timeout=0.001,
        interval=0.001,
        fake_retirement=False,
    )

    assert result.outcome == "measurement_failed"
    assert "descendant cleanup was not confirmed" in result.detail
    assert result.child_returncode == 0
    assert child.poll_calls == 0
    assert signals == [
        (child.pid, signal.SIGTERM),
        (child.pid, signal.SIGKILL),
        (child.pid, signal.SIGKILL),
    ]
    assert child.stdout.closed


def test_retirement_does_not_signal_a_reused_root_process_group(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    expected = process_guard.ProcessIdentity(123, 1, 777, "S", "old")
    reused = process_guard.ProcessIdentity(123, 1, 777, "S", "new")
    foreign = process_guard.ProcessIdentity(456, 123, 777, "S", "foreign")
    monkeypatch.setattr(
        process_guard,
        "process_snapshot",
        lambda: {123: reused, 456: foreign},
    )
    groups: list[tuple[int, int]] = []
    monkeypatch.setattr(
        process_guard,
        "_signal_group",
        partial(_record_killpg, groups),
    )
    monkeypatch.setattr(process_guard, "_signal_tracked", _ignore_tracked_signal)
    assert process_guard.retire_process(_FinishedChild(), root_identity=expected) == 0
    assert groups == []


def test_retirement_does_not_adopt_foreign_group_after_anchor_vanishes(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    expected_root = process_guard.ProcessIdentity(123, 1, 777, "S", "old")
    original_member = process_guard.ProcessIdentity(456, 123, 777, "S", "original")
    foreign_member = process_guard.ProcessIdentity(789, 1, 777, "S", "foreign")
    snapshots = iter(
        (
            {456: original_member},
            {789: foreign_member},
            {789: foreign_member},
        )
    )
    monkeypatch.setattr(process_guard, "process_snapshot", lambda: next(snapshots))
    signalled: list[tuple[int, ...]] = []
    monkeypatch.setattr(
        process_guard,
        "_signal_tracked",
        partial(_record_tracked_signal, signalled),
    )

    assert (
        process_guard.retire_process(
            _FinishedChild(),
            tracked={original_member.pid: original_member},
            root_identity=expected_root,
            group_anchors={original_member.pid: original_member},
        )
        == 0
    )
    assert all(foreign_member.pid not in pids for pids in signalled)


def test_detached_descendant_counts_toward_memory_limit(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    owner_pid = os.getpid()

    def footprint(pid: int) -> int:
        return 1 if pid == owner_pid else 900

    monkeypatch.setattr(
        process_guard,
        "memory_reader",
        lambda: ("test", footprint),
    )
    result = process_guard.run_guarded(
        (
            sys.executable,
            "-c",
            (
                "import subprocess,sys,time; "
                "subprocess.Popen([sys.executable,'-c',"
                '"import os,time; os.setsid(); time.sleep(30)"]); time.sleep(30)'
            ),
        ),
        output=tmp_path / "worker.log",
        memory_bytes=1500,
        lock_path=tmp_path / "lock",
    )
    assert result.outcome == "memory_limit"


def test_memory_rejection_does_not_need_a_large_allocation(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        process_guard,
        "memory_reader",
        partial(_fixed_memory_reader, 100),
    )
    result = process_guard.run_guarded(
        (sys.executable, "-c", "import time; time.sleep(30)"),
        output=tmp_path / "worker.log",
        memory_bytes=1,
        lock_path=tmp_path / "lock",
    )
    assert result.outcome == "memory_limit"
    assert result.sampled_peak_bytes is not None
    assert result.sampled_peak_bytes >= 100
    assert result.child_returncode != 0


def test_measurement_failure_terminates_group(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def unavailable(pid: int) -> int:
        if pid == os.getpid():
            return 1
        raise RuntimeError("instrumentation unavailable")

    monkeypatch.setattr(
        process_guard,
        "memory_reader",
        lambda: ("test", unavailable),
    )
    result = process_guard.run_guarded(
        (sys.executable, "-c", "import time; time.sleep(30)"),
        output=tmp_path / "worker.log",
        lock_path=tmp_path / "lock",
    )
    assert result.outcome == "measurement_failed"
    assert result.child_returncode != 0


def test_lock_rejects_another_worker_before_start(tmp_path: Path) -> None:
    lock = tmp_path / "lock"
    with lock.open("a+b") as lease:
        fcntl.flock(lease, fcntl.LOCK_EX | fcntl.LOCK_NB)
        with pytest.raises(BlockingIOError):
            process_guard.run_guarded(
                (sys.executable, "-c", "raise AssertionError('must not start')"),
                output=tmp_path / "worker.log",
                lock_path=lock,
            )
    assert not (tmp_path / "worker.log").exists()


def test_group_retirement_kills_descendant_after_leader_exit(tmp_path: Path) -> None:
    # Directly test retirement to avoid a race between leader exit and sampling.
    child = subprocess.Popen(
        [
            sys.executable,
            "-c",
            (
                "import subprocess,sys,time; "
                "p=subprocess.Popen([sys.executable,'-c','import time; time.sleep(30)'], "
                "stdout=subprocess.DEVNULL); print(p.pid, flush=True); time.sleep(1)"
            ),
        ],
        stdout=subprocess.PIPE,
        start_new_session=True,
    )
    try:
        assert child.stdout is not None
        descendant = int(child.stdout.readline().strip())
        snapshot = process_guard.process_snapshot()
        root_identity = snapshot[child.pid]
        anchors = {
            record.pid: record
            for record in process_guard.group_records(root_identity, snapshot)
        }
        child.communicate(timeout=2)
        assert child.returncode == 0
        assert descendant in process_guard.group_members(child.pid)
        assert (
            process_guard.retire_process(
                child,
                tracked=anchors,
                root_identity=root_identity,
                group_anchors=anchors,
            )
            == 0
        )
        assert child.poll() is not None
        state = subprocess.run(
            ["ps", "-o", "stat=", "-p", str(descendant)],
            capture_output=True,
            text=True,
            check=False,
            timeout=2,
        ).stdout.strip()
        assert not state or state.startswith("Z")
    finally:
        process_guard.retire_process(child)

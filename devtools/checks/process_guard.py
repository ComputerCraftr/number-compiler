"""Run one diagnostic worker with measured memory and process-group cleanup.

The sampled limit is an operational watchdog, not an allocation budget or an
exact peak measurement. A child must not detach from its process group.
"""

from __future__ import annotations

import argparse
import contextlib
import ctypes
import errno
import fcntl
import json
import math
import os
import signal
import subprocess
import sys
import tempfile
import time
from collections.abc import Callable, Mapping
from dataclasses import asdict, dataclass
from pathlib import Path
from types import FrameType
from typing import BinaryIO, Protocol, cast
from uuid import UUID, uuid4

from devtools.checks.validation_policy import (
    POLICY_VERSION,
    PYTHON_COMMAND_SECONDS,
    PYTHON_MEMORY_BYTES,
)

PROOF_GENERATION_ENV = "NUMBER_COMPILER_PROOF_GENERATION"
GUARDED_COMMAND_ENV = "NUMBER_COMPILER_GUARDED_COMMAND"
GUARDED_PARENT_PID_ENV = "NUMBER_COMPILER_GUARDED_PARENT_PID"
DEADLINE_ENV = "NUMBER_COMPILER_DEADLINE_MONOTONIC"
MEMORY_BUDGET_ENV = "NUMBER_COMPILER_MEMORY_BUDGET_BYTES"
_MEMORY_READ_ATTEMPTS = 2


def remaining_deadline_seconds(*, deadline: float | None = None) -> float:
    """Return the standard command budget capped by any enclosing deadline."""
    now = time.monotonic()
    effective_deadline = now + PYTHON_COMMAND_SECONDS
    inherited = os.environ.get(DEADLINE_ENV)
    if inherited is not None:
        try:
            parent_deadline = float(inherited)
        except ValueError as error:
            raise RuntimeError("invalid inherited command deadline") from error
        if not math.isfinite(parent_deadline):
            raise RuntimeError("invalid inherited command deadline")
        effective_deadline = min(effective_deadline, parent_deadline)
    if deadline is not None:
        if not math.isfinite(deadline):
            raise RuntimeError("invalid local command deadline")
        effective_deadline = min(effective_deadline, deadline)
    remaining = effective_deadline - now
    if remaining <= 0:
        raise TimeoutError("enclosing validation deadline has expired")
    return remaining


def guard_context_is_live(environment: Mapping[str, str]) -> bool:
    """Recognize a live guarded ancestor whose lease reached this process."""
    token = environment.get(GUARDED_COMMAND_ENV, "")
    try:
        if len(token) != 32 or UUID(hex=token).hex != token.lower():
            return False
        guard_pid = int(environment.get(GUARDED_PARENT_PID_ENV, ""))
        if guard_pid <= 1:
            return False
        if guard_pid != os.getppid() and not _is_process_ancestor(
            os.getpid(), guard_pid
        ):
            return False
        deadline = float(environment[DEADLINE_ENV])
        memory_bytes = int(environment[MEMORY_BUDGET_ENV])
    except (KeyError, OSError, ValueError, TypeError, subprocess.SubprocessError):
        return False
    return math.isfinite(deadline) and deadline > time.monotonic() and memory_bytes > 0


def _is_process_ancestor(process_id: int, possible_ancestor: int) -> bool:
    """Confirm a propagated lease's supervisor remains in process ancestry."""
    snapshot = _process_snapshot()
    seen: set[int] = set()
    current = snapshot.get(process_id)
    while current is not None and current.ppid > 0 and current.ppid not in seen:
        if current.ppid == possible_ancestor:
            return True
        seen.add(current.ppid)
        current = snapshot.get(current.ppid)
    return False


class _DarwinUsage(ctypes.Structure):
    _fields_ = [
        ("uuid", ctypes.c_uint8 * 16),
        ("user_time", ctypes.c_uint64),
        ("system_time", ctypes.c_uint64),
        ("idle_wakeups", ctypes.c_uint64),
        ("interrupt_wakeups", ctypes.c_uint64),
        ("pageins", ctypes.c_uint64),
        ("wired", ctypes.c_uint64),
        ("resident", ctypes.c_uint64),
        ("footprint", ctypes.c_uint64),
        ("started", ctypes.c_uint64),
        ("exited", ctypes.c_uint64),
    ]


def memory_reader() -> tuple[str, Callable[[int], int]]:
    """Prefer Darwin footprint over RSS, which misses compressed/swapped pages."""
    if sys.platform == "darwin":
        library = ctypes.CDLL("/usr/lib/libproc.dylib", use_errno=True)
        read_usage = library.proc_pid_rusage
        read_usage.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_void_p]
        read_usage.restype = ctypes.c_int

        def darwin(pid: int) -> int:
            usage = _DarwinUsage()
            if read_usage(pid, 0, ctypes.byref(usage)) != 0:
                code = ctypes.get_errno()
                if code == errno.ESRCH:
                    return 0
                if code == errno.EPERM:
                    state = subprocess.run(
                        ["ps", "-p", str(pid), "-o", "stat="],
                        check=False,
                        capture_output=True,
                        text=True,
                        timeout=2,
                    )
                    if state.returncode in (0, 1) and (
                        not state.stdout.strip() or state.stdout.strip().startswith("Z")
                    ):
                        return 0
                raise OSError(code, "cannot measure child footprint", pid)
            return int(usage.footprint)

        return "darwin_proc_pid_rusage_phys_footprint", darwin
    if sys.platform.startswith("linux"):

        def linux(pid: int) -> int:
            try:
                rows = Path(f"/proc/{pid}/status").read_text().splitlines()
            except FileNotFoundError:
                return 0
            values = {
                parts[0]: int(parts[1]) * 1024
                for row in rows
                if (parts := row.split()) and parts[0] in {"VmRSS:", "VmSwap:"}
            }
            if "VmRSS:" not in values:
                if any(row.startswith("State:") and "Z" in row for row in rows):
                    return 0
                raise RuntimeError("child memory measurement unavailable")
            return values["VmRSS:"] + values.get("VmSwap:", 0)

        return "linux_rss_plus_swap", linux
    raise RuntimeError("no supported process-footprint measurement on this platform")


@dataclass(frozen=True)
class _ProcessRecord:
    """Stable identity for a process observed under the guarded worker."""

    pid: int
    ppid: int
    pgid: int
    state: str
    start_time: str


class _WaitableProcess(Protocol):
    """The small process interface required by descendant retirement.

    Keeping this structural lets lifecycle tests use a finished process
    double while the guarded subprocess remains a normal ``Popen`` object.
    """

    pid: int
    returncode: int | None

    def wait(self, timeout: float | None = None) -> int: ...


class ProgressWatchdog(Protocol):
    """Incremental process-output observer with a monotonic deadline check."""

    def observe_output(self, data: bytes, now: float) -> None: ...

    def check(self, now: float) -> str | None: ...

    def finish_output(self, now: float) -> None: ...


def _process_snapshot() -> dict[int, _ProcessRecord]:
    """Return process ancestry and start identities from one system snapshot."""
    listing = subprocess.run(
        ["ps", "-axo", "pid=,ppid=,pgid=,stat=,lstart="],
        check=True,
        capture_output=True,
        text=True,
        timeout=2,
    )
    records: dict[int, _ProcessRecord] = {}
    for row in listing.stdout.splitlines():
        fields = row.split(maxsplit=4)
        if len(fields) != 5:
            continue
        pid, ppid, pgid = (int(value) for value in fields[:3])
        state = fields[3]
        records[pid] = _ProcessRecord(pid, ppid, pgid, state, fields[4])
    return records


def _descendants(
    root: int, snapshot: Mapping[int, _ProcessRecord]
) -> tuple[_ProcessRecord, ...]:
    """Find all observed descendants, including descendants in new sessions."""
    children: dict[int, list[_ProcessRecord]] = {}
    for record in snapshot.values():
        children.setdefault(record.ppid, []).append(record)
    pending = list(children.get(root, ()))
    result: list[_ProcessRecord] = []
    while pending:
        record = pending.pop()
        result.append(record)
        pending.extend(children.get(record.pid, ()))
    return tuple(result)


def _live_tracked(
    tracked: Mapping[int, _ProcessRecord], snapshot: Mapping[int, _ProcessRecord]
) -> tuple[_ProcessRecord, ...]:
    """Retain only non-zombie processes with the observed start token."""
    return tuple(
        current
        for pid, expected in tracked.items()
        if (current := snapshot.get(pid)) is not None
        and current.start_time == expected.start_time
        and not current.state.startswith("Z")
    )


def _same_process(
    expected: _ProcessRecord | None, current: _ProcessRecord | None
) -> bool:
    return (
        expected is not None
        and current is not None
        and expected.pid == current.pid
        and expected.start_time == current.start_time
    )


def _read_member_footprint(
    member: _ProcessRecord, read_memory: Callable[[int], int]
) -> int:
    """Read one sampled identity, retrying only a transient permission race.

    A denied procfs/libproc read is ambiguous: the process may have exited
    after the preceding membership snapshot, or access to a still-live worker
    may genuinely be unavailable. Refresh identity before deciding. A missing,
    zombie, or replaced PID contributes zero for the old identity; a matching
    live identity gets only a small bounded retry and remains fail-closed.
    """
    for attempt in range(_MEMORY_READ_ATTEMPTS):
        try:
            return read_memory(member.pid)
        except OSError as error:
            if error.errno not in {errno.EPERM, errno.EACCES}:
                raise
            current = _process_snapshot().get(member.pid)
            if (
                not _same_process(member, current)
                or current is None
                or current.state.startswith("Z")
            ):
                return 0
            if attempt + 1 == _MEMORY_READ_ATTEMPTS:
                raise
    raise AssertionError("bounded process footprint retries must return or raise")


def _observe_descendants(
    root: _ProcessRecord,
    tracked: dict[int, _ProcessRecord],
    snapshot: Mapping[int, _ProcessRecord],
) -> None:
    """Extend tracking only through an identity-checked root or child."""
    if not _same_process(root, snapshot.get(root.pid)):
        return
    roots = (root, *_live_tracked(tracked, snapshot))
    for parent in roots:
        for record in _descendants(parent.pid, snapshot):
            tracked[record.pid] = record


def _group_records(
    root: _ProcessRecord, snapshot: Mapping[int, _ProcessRecord]
) -> tuple[_ProcessRecord, ...]:
    return tuple(
        record
        for record in snapshot.values()
        if record.pgid == root.pgid and not record.state.startswith("Z")
    )


def _observe_group(
    group: int,
    tracked: dict[int, _ProcessRecord],
    snapshot: Mapping[int, _ProcessRecord],
    anchors: Mapping[int, _ProcessRecord],
) -> None:
    """Adopt same-group processes only while an observed anchor is alive.

    A process-group id is reusable.  Once every member observed while the
    guarded root was authoritative has gone away, a later process with that
    PGID is not evidence that it belongs to this run.  In particular, never
    turn a vanished leader into authority for an unrelated process that
    inherited the numeric PGID.
    """
    if not any(record.pgid == group for record in _live_tracked(anchors, snapshot)):
        return
    for record in snapshot.values():
        if record.pgid == group and not record.state.startswith("Z"):
            tracked[record.pid] = record


def _remember_group_anchors(
    root: _ProcessRecord,
    tracked: Mapping[int, _ProcessRecord],
    anchors: dict[int, _ProcessRecord],
) -> None:
    """Retain identities observed while the original root is still live."""
    anchors[root.pid] = root
    for record in tracked.values():
        if record.pgid == root.pgid:
            anchors[record.pid] = record


def _snapshot_members(
    root_identity: _ProcessRecord | None,
    tracked: dict[int, _ProcessRecord],
    group_anchors: dict[int, _ProcessRecord],
    snapshot: Mapping[int, _ProcessRecord],
) -> tuple[int, ...]:
    """Refresh authorized group and detached members from one snapshot."""
    if root_identity is None:
        return ()
    current_root = snapshot.get(root_identity.pid)
    if _same_process(root_identity, current_root):
        assert current_root is not None
        _observe_descendants(current_root, tracked, snapshot)
        _remember_group_anchors(current_root, tracked, group_anchors)
        group_records = _group_records(current_root, snapshot)
        for record in group_records:
            group_anchors[record.pid] = record
    elif current_root is None:
        _observe_group(root_identity.pgid, tracked, snapshot, group_anchors)
        group_records = ()
    else:
        # A reused root PID is not authority for a new group or descendants.
        group_records = ()
    detached = _live_tracked(tracked, snapshot)
    group_pids = tuple(record.pid for record in group_records)
    detached_pids = tuple(record.pid for record in detached)
    return tuple(dict.fromkeys((*group_pids, *detached_pids)))


def group_members(group: int) -> tuple[int, ...]:
    return tuple(
        record.pid
        for record in _process_snapshot().values()
        if record.pgid == group and not record.state.startswith("Z")
    )


def _signal_group(group: int, number: int) -> None:
    try:
        os.killpg(group, number)
    except ProcessLookupError:
        pass
    except PermissionError:
        # Darwin can return EPERM for a group whose leader has just exited.
        # Never suppress an actual inability to terminate a live worker.
        if group_members(group):
            raise


def _signal_unreaped_owned_group(child: _WaitableProcess, number: int) -> None:
    """Signal the launched session while its unreaped leader pins the PGID.

    ``run_guarded`` always starts the child in a new session, so its PID is
    also the process-group ID.  The unreaped direct child prevents that PID
    from being reused.  This is only a fail-closed cleanup path for the rare
    case where no identity snapshot could bind the leader; never call it once
    the child has been reaped.
    """
    if child.returncode is not None:
        return
    try:
        os.killpg(child.pid, number)
    except ProcessLookupError:
        pass


def _signal_tracked(tracked: Mapping[int, _ProcessRecord], number: int) -> None:
    """Signal only descendants whose start identity is still unchanged."""
    snapshot = _process_snapshot()
    for record in _live_tracked(tracked, snapshot):
        try:
            os.kill(record.pid, number)
        except ProcessLookupError:
            pass


def _retire(
    child: _WaitableProcess,
    tracked: Mapping[int, _ProcessRecord] | None = None,
    root_identity: _ProcessRecord | None = None,
    group_anchors: Mapping[int, _ProcessRecord] | None = None,
) -> int:
    """Also retire surviving descendants when the group leader already exited."""
    tracked = dict(tracked or {})
    anchors = dict(group_anchors or {})
    if group_anchors is None:
        if root_identity is not None:
            anchors[root_identity.pid] = root_identity
        for record in tracked.values():
            anchors.setdefault(record.pid, record)
    unbound_unreaped = root_identity is None and child.returncode is None
    if unbound_unreaped:
        # No ps identity was captured.  The Popen child is still unreaped, so
        # its PID safely anchors the new-session PGID.  Kill that owned group
        # before waitpid can release the numeric identity.  Confirm that no
        # live same-group member remains while that anchor is still pinned.
        _signal_unreaped_owned_group(child, signal.SIGTERM)
        _signal_unreaped_owned_group(child, signal.SIGKILL)
        deadline = time.monotonic() + 2
        while True:
            snapshot = _process_snapshot()
            group_live = any(
                record.pgid == child.pid and not record.state.startswith("Z")
                for record in snapshot.values()
            )
            if not group_live:
                return child.wait(timeout=2)
            if time.monotonic() >= deadline:
                raise RuntimeError("unbound worker group still live after SIGKILL")
            _signal_unreaped_owned_group(child, signal.SIGKILL)
            time.sleep(0.02)
    snapshot = _process_snapshot()
    current_root = snapshot.get(child.pid)
    if _same_process(root_identity, current_root):
        assert current_root is not None
        _observe_descendants(current_root, tracked, snapshot)
        _remember_group_anchors(current_root, tracked, anchors)
        _signal_group(current_root.pgid, signal.SIGTERM)
    elif current_root is None:
        _observe_group(
            root_identity.pgid if root_identity is not None else child.pid,
            tracked,
            snapshot,
            anchors,
        )
    _signal_tracked(tracked, signal.SIGTERM)
    try:
        child.wait(timeout=0.2)
    except subprocess.TimeoutExpired:
        pass
    finally:
        snapshot = _process_snapshot()
        current_root = snapshot.get(child.pid)
        if _same_process(root_identity, current_root):
            assert current_root is not None
            _observe_descendants(current_root, tracked, snapshot)
            _remember_group_anchors(current_root, tracked, anchors)
            _signal_group(current_root.pgid, signal.SIGKILL)
        elif current_root is None:
            _observe_group(
                root_identity.pgid if root_identity is not None else child.pid,
                tracked,
                snapshot,
                anchors,
            )
            for parent in _live_tracked(tracked, snapshot):
                for record in _descendants(parent.pid, snapshot):
                    tracked.setdefault(record.pid, record)
        _signal_tracked(tracked, signal.SIGKILL)
    code = child.wait(timeout=2)
    deadline = time.monotonic() + 2
    while True:
        snapshot = _process_snapshot()
        current_root = snapshot.get(child.pid)
        if _same_process(root_identity, current_root):
            assert current_root is not None
            group_live = bool(_group_records(current_root, snapshot))
        else:
            group_live = False
        if not group_live and not _live_tracked(tracked, snapshot):
            break
        if time.monotonic() >= deadline:
            raise RuntimeError("worker descendants still live after SIGKILL")
        time.sleep(0.02)
    return code


class _OutputSink:
    """Drain bounded pipe chunks; never write beyond the retained log cap."""

    def __init__(self, stream: BinaryIO, limit: int) -> None:
        self.stream = stream
        self.limit = limit
        self.observed = 0
        self.eof = False

    def drain(self, descriptor: int, observer: ProgressWatchdog | None = None) -> bool:
        for _ in range(16):
            try:
                data = os.read(descriptor, min(65536, self.limit - self.observed + 1))
            except BlockingIOError:
                return False
            if not data:
                self.eof = True
                if observer is not None:
                    observer.finish_output(time.monotonic())
                return False
            remaining = self.limit - self.observed
            self.stream.write(data[:remaining])
            self.stream.flush()
            self.observed += len(data)
            if observer is not None:
                observer.observe_output(data, time.monotonic())
            if self.observed > self.limit:
                return True
        return False


@dataclass(frozen=True)
class GuardResult:
    schema: int
    outcome: str
    child_returncode: int
    elapsed_seconds: float
    sampled_peak_bytes: int | None
    memory_limit_bytes: int
    memory_measurement: str
    sample_interval_seconds: float
    samples: int
    output_bytes: int
    detail: str
    cleanup_confirmed: bool = True


def run_guarded(
    command: tuple[str, ...],
    *,
    output: Path,
    cwd: Path | None = None,
    timeout: float = PYTHON_COMMAND_SECONDS,
    memory_bytes: int = PYTHON_MEMORY_BYTES,
    output_bytes: int = 8 * 1024**2,
    interval: float = 0.05,
    lock_path: Path | None = None,
    environment: Mapping[str, str] | None = None,
    active_test_path: Path | None = None,
    active_test_timeout: float | None = None,
    progress_watchdog: ProgressWatchdog | None = None,
) -> GuardResult:
    """Supervise cooperative workers that do not detach from their group."""
    if not command or any(not math.isfinite(n) or n <= 0 for n in (timeout, interval)):
        raise ValueError("a command and positive finite time limits are required")
    if any(type(n) is not int or n <= 0 for n in (memory_bytes, output_bytes)):
        raise ValueError("byte limits must be positive integers")
    if (active_test_path is None) != (active_test_timeout is None):
        raise ValueError("active-test marker and timeout must be configured together")
    if active_test_timeout is not None and (
        not math.isfinite(active_test_timeout) or active_test_timeout <= 0
    ):
        raise ValueError("active-test timeout must be positive and finite")
    guard_started = time.monotonic()
    inherited = dict(os.environ)
    child_environment = dict(inherited if environment is None else environment)
    parent_deadline = inherited.get(DEADLINE_ENV)
    requested_deadline = child_environment.get(DEADLINE_ENV, parent_deadline)
    effective_deadline = time.monotonic() + timeout
    for inherited_value in (parent_deadline, requested_deadline):
        if inherited_value is None:
            continue
        try:
            deadline_value = float(inherited_value)
        except ValueError as error:
            raise ValueError("inherited deadline is invalid") from error
        if not math.isfinite(deadline_value):
            raise ValueError("inherited deadline must be finite")
        effective_deadline = min(effective_deadline, deadline_value)
    timeout = effective_deadline - time.monotonic()
    if timeout <= 0:
        raise ValueError("parent validation deadline has expired")
    inherited_memory = inherited.get(MEMORY_BUDGET_ENV)
    requested_memory = child_environment.get(MEMORY_BUDGET_ENV, inherited_memory)
    for memory_value in (inherited_memory, requested_memory):
        if memory_value is None:
            continue
        try:
            parsed_memory = int(memory_value)
        except ValueError as error:
            raise ValueError("inherited memory budget is invalid") from error
        if parsed_memory <= 0:
            raise ValueError("inherited memory budget must be positive")
        memory_bytes = min(memory_bytes, parsed_memory)
    if memory_bytes <= 0:
        raise ValueError("parent validation memory budget has expired")
    nested = guard_context_is_live(inherited) and lock_path is None
    child_environment[DEADLINE_ENV] = str(effective_deadline)
    child_environment[MEMORY_BUDGET_ENV] = str(memory_bytes)
    child_environment[GUARDED_COMMAND_ENV] = uuid4().hex
    child_environment[GUARDED_PARENT_PID_ENV] = str(os.getpid())
    metric, read_memory = memory_reader()
    # Validate instrumentation before starting potentially expensive work.
    read_memory(os.getpid())
    lock = (
        lock_path
        or Path(tempfile.gettempdir()) / f"number-compiler-worker-{os.getuid()}.lock"
    )
    lock_lease = contextlib.nullcontext() if nested else lock.open("a+b")
    with lock_lease as lease:
        if lease is not None:
            fcntl.flock(lease, fcntl.LOCK_EX | fcntl.LOCK_NB)
        output.parent.mkdir(parents=True, exist_ok=True)
        with output.open("xb") as log:
            started = time.monotonic()
            timeout = effective_deadline - started
            if timeout <= 0:
                detail = "validation deadline expired before worker launch"
                log.write((detail + "\n").encode())
                log.flush()
                return GuardResult(
                    1,
                    "timeout",
                    -1,
                    time.monotonic() - guard_started,
                    None,
                    memory_bytes,
                    metric,
                    interval,
                    0,
                    log.tell(),
                    detail,
                )
            child = subprocess.Popen(
                command,
                cwd=cwd,
                env=child_environment,
                stdin=subprocess.DEVNULL,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                start_new_session=True,
            )
            peak: int | None = None
            samples = 0
            sink = _OutputSink(log, output_bytes)
            tracked: dict[int, _ProcessRecord] = {}
            group_anchors: dict[int, _ProcessRecord] = {}
            root_identity: _ProcessRecord | None = None
            outcome, detail = "completed", ""
            cleanup_confirmed = True
            try:
                assert child.stdout is not None
                descriptor = child.stdout.fileno()
                os.set_blocking(descriptor, False)
                while True:
                    if time.monotonic() - started >= timeout:
                        outcome = "timeout"
                        break
                    snapshot = _process_snapshot()
                    if root_identity is None:
                        root_identity = snapshot.get(child.pid)
                    if sink.drain(descriptor, progress_watchdog):
                        outcome = "output_limit"
                        break
                    if time.monotonic() - started >= timeout:
                        outcome = "timeout"
                        break
                    if progress_watchdog is not None:
                        watchdog_reason = progress_watchdog.check(time.monotonic())
                        if watchdog_reason is not None:
                            outcome, detail = "session_timeout", watchdog_reason
                            break
                    members = _snapshot_members(
                        root_identity, tracked, group_anchors, snapshot
                    )
                    footprint = sum(
                        _read_member_footprint(snapshot[pid], read_memory)
                        for pid in members
                    )
                    if footprint > 0:
                        peak = max(peak or 0, footprint)
                        samples += 1
                    if footprint > memory_bytes:
                        outcome = "memory_limit"
                        break
                    if active_test_path is not None:
                        assert active_test_timeout is not None
                        try:
                            active_test = _active_test_timeout(
                                active_test_path, active_test_timeout
                            )
                        except (OSError, ValueError, TypeError) as error:
                            outcome = "measurement_failed"
                            detail = f"active-test instrumentation failed: {error}"
                            break
                        if active_test is not None:
                            nodeid, elapsed = active_test
                            if elapsed >= active_test_timeout:
                                outcome = "test_timeout"
                                detail = (
                                    f"test {nodeid!r} exceeded "
                                    f"{active_test_timeout:g} seconds"
                                )
                                break
                    # Do not reap the direct child until its process identity
                    # has been observed.  A fast worker can otherwise exit
                    # between the first ps snapshot and poll(), leaving only
                    # an unanchored descendant in the next snapshot.  An
                    # unreaped child remains visible as a zombie and pins its
                    # PID, so the next bounded sample can bind it safely.
                    if root_identity is not None and child.poll() is not None:
                        # The previous membership view predates waitpid. Refresh
                        # after observing leader exit so a descendant that died
                        # between ps and poll cannot cause a stale refusal.
                        exit_snapshot = _process_snapshot()
                        members = _snapshot_members(
                            root_identity, tracked, group_anchors, exit_snapshot
                        )
                        if any(pid != child.pid for pid in members):
                            outcome = "descendants_retired"
                            break
                        if sink.eof:
                            break
                    if time.monotonic() - started >= timeout:
                        outcome = "timeout"
                        break
                    time.sleep(interval)
                if child.returncode != 0 and outcome in {
                    "completed",
                    "descendants_retired",
                }:
                    if outcome == "descendants_retired":
                        detail = "cleanup=descendants_retired; child_failed"
                    outcome = "child_failed"
            except (OSError, RuntimeError, subprocess.SubprocessError) as error:
                outcome, detail = "measurement_failed", str(error)
            except KeyboardInterrupt as error:
                outcome, detail = "interrupted", str(error)
            finally:
                try:
                    returncode = _retire(child, tracked, root_identity, group_anchors)
                except (OSError, RuntimeError, subprocess.SubprocessError) as error:
                    cleanup_confirmed = False
                    outcome = "measurement_failed"
                    cleanup_detail = (
                        f"cleanup inspection failed: {error}; "
                        "descendant cleanup was not confirmed"
                    )
                    detail = "; ".join(
                        part for part in (detail, cleanup_detail) if part
                    )
                    if child.returncode is None:
                        try:
                            _signal_unreaped_owned_group(child, signal.SIGKILL)
                        except OSError as signal_error:
                            detail += f"; owned-group kill failed: {signal_error}"
                            try:
                                os.kill(child.pid, signal.SIGKILL)
                            except ProcessLookupError:
                                pass
                            except OSError as direct_signal_error:
                                detail += (
                                    f"; direct-child kill failed: {direct_signal_error}"
                                )
                        try:
                            returncode = child.wait(timeout=2)
                        except subprocess.TimeoutExpired:
                            detail += "; direct child did not exit after cleanup"
                            returncode = -1
                    else:
                        returncode = child.returncode
                        if tracked:
                            try:
                                _signal_tracked(tracked, signal.SIGKILL)
                            except (OSError, RuntimeError, subprocess.SubprocessError):
                                pass
                finally:
                    if child.stdout is not None:
                        child.stdout.close()
            return GuardResult(
                1,
                outcome,
                returncode,
                time.monotonic() - started,
                peak,
                memory_bytes,
                metric,
                interval,
                samples,
                sink.observed,
                detail,
                cleanup_confirmed,
            )


def _active_test_timeout(
    path: Path, timeout_seconds: float | None
) -> tuple[str, float] | None:
    """Read the atomic pytest node marker and return its elapsed duration."""
    if timeout_seconds is None:
        raise ValueError("active-test timeout is missing")
    try:
        raw = path.read_text(encoding="utf-8")
    except FileNotFoundError:
        return None
    marker = json.loads(raw)
    if not isinstance(marker, dict):
        raise TypeError("active-test marker must contain an object")
    nodeid = marker.get("nodeid")
    started = marker.get("started_monotonic")
    deadline = marker.get("deadline_monotonic")
    if not isinstance(nodeid, str) or not nodeid:
        raise ValueError("active-test marker has no node ID")
    if type(started) not in (int, float) or type(deadline) not in (int, float):
        raise ValueError("active-test marker has invalid timing fields")
    started_value = float(cast(int | float, started))
    deadline_value = float(cast(int | float, deadline))
    if not math.isfinite(started_value) or not math.isfinite(deadline_value):
        raise ValueError("active-test marker timing must be finite")
    expected_deadline = started_value + timeout_seconds
    if not math.isclose(deadline_value, expected_deadline, rel_tol=0, abs_tol=0.01):
        raise ValueError("active-test marker deadline does not match policy")
    return nodeid, max(0.0, time.monotonic() - started_value)


def _interrupted(number: int, frame: FrameType | None) -> None:
    raise KeyboardInterrupt(f"received signal {number}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    arguments = parser.parse_args()
    command = tuple(arguments.command)
    if command[:1] == ("--",):
        command = command[1:]
    generation = uuid4().hex
    environment = dict(os.environ)
    # A nested or unbound run must not inherit another memo owner's authority.
    environment.pop(PROOF_GENERATION_ENV, None)
    environment[PROOF_GENERATION_ENV] = generation
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    effective_remaining = remaining_deadline_seconds()
    inherited_memory = environment.get(MEMORY_BUDGET_ENV)
    effective_memory = PYTHON_MEMORY_BYTES
    if inherited_memory is not None:
        effective_memory = min(effective_memory, int(inherited_memory))
    previous = signal.signal(signal.SIGTERM, _interrupted)
    try:
        result = run_guarded(
            command,
            output=arguments.output,
            timeout=PYTHON_COMMAND_SECONDS,
            memory_bytes=PYTHON_MEMORY_BYTES,
            environment=environment,
        )
    finally:
        signal.signal(signal.SIGTERM, previous)
    report = asdict(result) | {
        "policy_version": POLICY_VERSION,
        "command": list(command),
        "cwd": str(Path.cwd()),
        "timeout_seconds": PYTHON_COMMAND_SECONDS,
        "effective_remaining_seconds_at_start": effective_remaining,
        "effective_memory_bytes": effective_memory,
        "proof_generation": generation,
    }
    arguments.report.parent.mkdir(parents=True, exist_ok=True)
    arguments.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report))
    return 0 if result.outcome == "completed" else 1


if __name__ == "__main__":
    raise SystemExit(main())

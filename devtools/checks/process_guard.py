"""Run one diagnostic worker with measured memory and process-group cleanup.

The sampled limit is an operational watchdog, not an allocation budget or an
exact peak measurement. A child must not detach from its process group.
"""

from __future__ import annotations

import argparse
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
from dataclasses import asdict, dataclass, replace
from pathlib import Path
from types import FrameType
from typing import BinaryIO
from uuid import uuid4

PROOF_GENERATION_ENV = "NUMBER_COMPILER_PROOF_GENERATION"


def source_revision(root: Path) -> tuple[tuple[str, int, int, int, int, int], ...]:
    """Detect source edits, including content restored during a proof run.

    Sample only at evidence boundaries, never on a theorem memo hit. The
    content fingerprint remains authoritative for the bytes being certified.
    """
    from devtools.checks.test_run_evidence import authored_source_paths

    rows = []
    for path in authored_source_paths(root, include_directories=True):
        status = path.stat()
        rows.append(
            (
                path.relative_to(root).as_posix(),
                status.st_dev,
                status.st_ino,
                status.st_size,
                status.st_mtime_ns,
                status.st_ctime_ns,
            )
        )
    return tuple(rows)


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


def group_members(group: int) -> tuple[int, ...]:
    listing = subprocess.run(
        ["ps", "-axo", "pid=,pgid=,stat="],
        check=True,
        capture_output=True,
        text=True,
        timeout=2,
    )
    members = []
    for row in listing.stdout.splitlines():
        pid, pgid, state = row.split()
        if int(pgid) == group and not state.startswith("Z"):
            members.append(int(pid))
    return tuple(members)


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


def _retire(child: subprocess.Popen[bytes]) -> int:
    """Also retire surviving descendants when the group leader already exited."""
    _signal_group(child.pid, signal.SIGTERM)
    try:
        child.wait(timeout=0.2)
    except subprocess.TimeoutExpired:
        pass
    finally:
        _signal_group(child.pid, signal.SIGKILL)
    code = child.wait(timeout=2)
    deadline = time.monotonic() + 2
    while group_members(child.pid):
        if time.monotonic() >= deadline:
            raise RuntimeError("worker group still has live members after SIGKILL")
        time.sleep(0.02)
    return code


class _OutputSink:
    """Drain bounded pipe chunks; never write beyond the retained log cap."""

    def __init__(self, stream: BinaryIO, limit: int) -> None:
        self.stream = stream
        self.limit = limit
        self.observed = 0
        self.eof = False

    def drain(self, descriptor: int) -> bool:
        for _ in range(16):
            try:
                data = os.read(descriptor, min(65536, self.limit - self.observed + 1))
            except BlockingIOError:
                return False
            if not data:
                self.eof = True
                return False
            remaining = self.limit - self.observed
            self.stream.write(data[:remaining])
            self.observed += len(data)
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


def run_guarded(
    command: tuple[str, ...],
    *,
    output: Path,
    cwd: Path | None = None,
    timeout: float = 35,
    memory_bytes: int = 1024**3,
    output_bytes: int = 8 * 1024**2,
    interval: float = 0.05,
    lock_path: Path | None = None,
    environment: Mapping[str, str] | None = None,
) -> GuardResult:
    """Supervise cooperative workers that do not detach from their group."""
    if not command or any(not math.isfinite(n) or n <= 0 for n in (timeout, interval)):
        raise ValueError("a command and positive finite time limits are required")
    if any(type(n) is not int or n <= 0 for n in (memory_bytes, output_bytes)):
        raise ValueError("byte limits must be positive integers")
    metric, read_memory = memory_reader()
    # Validate instrumentation before starting potentially expensive work.
    read_memory(os.getpid())
    lock = (
        lock_path
        or Path(tempfile.gettempdir()) / f"number-compiler-worker-{os.getuid()}.lock"
    )
    with lock.open("a+b") as lease:
        fcntl.flock(lease, fcntl.LOCK_EX | fcntl.LOCK_NB)
        output.parent.mkdir(parents=True, exist_ok=True)
        with output.open("xb") as log:
            started = time.monotonic()
            child = subprocess.Popen(
                command,
                cwd=cwd,
                env=environment,
                stdin=subprocess.DEVNULL,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                start_new_session=True,
            )
            peak: int | None = None
            samples = 0
            sink = _OutputSink(log, output_bytes)
            outcome, detail = "completed", ""
            try:
                assert child.stdout is not None
                descriptor = child.stdout.fileno()
                os.set_blocking(descriptor, False)
                while True:
                    members = group_members(child.pid)
                    footprint = sum(read_memory(pid) for pid in members)
                    if footprint > 0:
                        peak = max(peak or 0, footprint)
                        samples += 1
                    if footprint > memory_bytes:
                        outcome = "memory_limit"
                        break
                    if sink.drain(descriptor):
                        outcome = "output_limit"
                        break
                    if child.poll() is not None:
                        if any(pid != child.pid for pid in group_members(child.pid)):
                            outcome = "descendants_retired"
                            break
                        if sink.eof:
                            break
                    if time.monotonic() - started >= timeout:
                        outcome = "timeout"
                        break
                    time.sleep(interval)
                if outcome == "completed" and child.returncode != 0:
                    outcome = "child_failed"
            except (OSError, RuntimeError, subprocess.SubprocessError) as error:
                outcome, detail = "measurement_failed", str(error)
            except KeyboardInterrupt as error:
                outcome, detail = "interrupted", str(error)
            finally:
                try:
                    returncode = _retire(child)
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
            )


def _interrupted(number: int, frame: FrameType | None) -> None:
    raise KeyboardInterrupt(f"received signal {number}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--timeout", type=float, default=35)
    parser.add_argument("--memory-mib", type=int, default=1024)
    parser.add_argument(
        "--source-root",
        type=Path,
        help="reject successful evidence if authored sources change during the run",
    )
    parser.add_argument("command", nargs=argparse.REMAINDER)
    arguments = parser.parse_args()
    command = tuple(arguments.command)
    if command[:1] == ("--",):
        command = command[1:]
    source_before: str | None = None
    revision_before: tuple[tuple[str, int, int, int, int, int], ...] | None = None
    generation = ""
    environment = dict(os.environ)
    # A nested or unbound run must not inherit another memo owner's authority.
    environment.pop(PROOF_GENERATION_ENV, None)
    source_root: Path | None = arguments.source_root
    if source_root is not None:
        from devtools.checks.test_run_evidence import source_fingerprint

        source_root = source_root.resolve(strict=True)
        # Create output directories before binding the revision. Put artifacts
        # below non-source directories (normally results/), not in src/tests.
        arguments.output.parent.mkdir(parents=True, exist_ok=True)
        arguments.report.parent.mkdir(parents=True, exist_ok=True)
        revision_before = source_revision(source_root)
        source_before = source_fingerprint(source_root)
        if revision_before != source_revision(source_root):
            parser.error("authored sources changed while binding the proof generation")
        generation = f"{uuid4().hex}:{source_before}"
        environment[PROOF_GENERATION_ENV] = generation
        environment["PYTHONDONTWRITEBYTECODE"] = "1"
    previous = signal.signal(signal.SIGTERM, _interrupted)
    try:
        result = run_guarded(
            command,
            output=arguments.output,
            timeout=arguments.timeout,
            memory_bytes=arguments.memory_mib * 1024**2,
            environment=environment,
        )
    finally:
        signal.signal(signal.SIGTERM, previous)
    provenance: dict[str, str | bool] = {}
    if source_root is not None:
        assert source_before is not None
        source_after = source_fingerprint(source_root)
        revision_unchanged = revision_before == source_revision(source_root)
        unchanged = source_before == source_after and revision_unchanged
        provenance = {
            "source_root": str(source_root),
            "source_fingerprint_before": source_before,
            "source_fingerprint_after": source_after,
            "source_unchanged": unchanged,
            "source_revision_unchanged": revision_unchanged,
            "proof_generation": generation,
        }
        if not unchanged and result.outcome == "completed":
            result = replace(
                result,
                outcome="source_changed",
                detail="authored sources changed during guarded execution",
            )
    report = asdict(result) | provenance
    arguments.report.parent.mkdir(parents=True, exist_ok=True)
    arguments.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report))
    return 0 if result.outcome == "completed" else 1


if __name__ == "__main__":
    raise SystemExit(main())

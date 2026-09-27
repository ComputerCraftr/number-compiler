"""Small worker probes for the developer watchdog; no algorithm stress fixtures."""

from __future__ import annotations

import fcntl
import json
import os
import subprocess
import sys
from functools import partial
from pathlib import Path
from collections.abc import Mapping

import pytest

from devtools.checks import process_guard


@pytest.mark.parametrize(
    "mutation", ["none", "change", "restore", "restore_mtime", "transient"]
)
@pytest.mark.parametrize("child_outcome", ["completed", "child_failed"])
def test_guarded_cli_binds_evidence_to_unchanged_sources(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    mutation: str,
    child_outcome: str,
) -> None:
    source = tmp_path / "src"
    source.mkdir()
    authored = source / "sample.py"
    authored.write_text("value = 1\n")
    original_mtime = authored.stat().st_mtime_ns
    monkeypatch.setenv(process_guard.PROOF_GENERATION_ENV, "foreign-generation")
    report = tmp_path / "report.json"
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "process_guard",
            "--source-root",
            str(tmp_path),
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
        assert len(generation.split(":")) == 2
        if mutation == "transient":
            transient = source / "transient.py"
            transient.write_text("value = 2\n")
            transient.unlink()
            directory = source.stat()
            os.utime(
                source, ns=(directory.st_atime_ns, directory.st_mtime_ns + 1_000_000)
            )
        elif mutation != "none":
            authored.write_text("value = 2\n")
            if mutation in {"restore", "restore_mtime"}:
                authored.write_text("value = 1\n")
            restored_mtime = (
                original_mtime
                if mutation == "restore_mtime"
                else original_mtime + 1_000_000
            )
            os.utime(authored, ns=(original_mtime, restored_mtime))
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
    mutate = mutation != "none"
    assert process_guard.main() == int(mutate or child_outcome != "completed")
    evidence = json.loads(report.read_text())
    assert evidence["source_unchanged"] is not mutate
    assert (
        evidence["source_fingerprint_before"] == evidence["source_fingerprint_after"]
    ) is (mutation != "change")
    assert evidence["source_revision_unchanged"] is not mutate
    assert evidence["proof_generation"].endswith(evidence["source_fingerprint_before"])
    assert len(evidence["source_fingerprint_before"]) == 64
    expected = (
        "source_changed" if mutate and child_outcome == "completed" else child_outcome
    )
    assert evidence["outcome"] == expected
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


def test_proof_generation_reaches_child_without_mutating_source_cache(
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
            "--source-root",
            str(tmp_path),
            "--output",
            str(output),
            "--report",
            str(report),
            "--",
            sys.executable,
            "-c",
            "import os, sys; sys.path.insert(0, sys.argv[1]); import sample; "
            "print(os.environ['NUMBER_COMPILER_PROOF_GENERATION'])",
            str(source),
        ],
    )
    assert process_guard.main() == 0
    evidence = json.loads(report.read_text())
    assert output.read_text().strip() == evidence["proof_generation"]
    assert evidence["proof_generation"] != "foreign-owner"
    assert evidence["source_revision_unchanged"]
    assert not (source / "__pycache__").exists()


def test_worker_uses_explicit_working_directory(tmp_path: Path) -> None:
    working = tmp_path / "working"
    working.mkdir()
    result = process_guard.run_guarded(
        (
            sys.executable,
            "-c",
            "import pathlib,time; print(pathlib.Path.cwd()); time.sleep(.15)",
        ),
        output=tmp_path / "worker.log",
        cwd=working,
        lock_path=tmp_path / "lock",
    )
    assert result.outcome == "completed"
    observed = Path((tmp_path / "worker.log").read_text().strip())
    assert observed.resolve() == working.resolve()


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
    assert result.outcome == "timeout"
    pid = int(log.read_text().strip())
    with pytest.raises(ProcessLookupError):
        os.kill(pid, 0)


def test_memory_rejection_does_not_need_a_large_allocation(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        process_guard, "memory_reader", lambda: ("test", lambda pid: 100)
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

    monkeypatch.setattr(process_guard, "memory_reader", lambda: ("test", unavailable))
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
                "import subprocess,sys; "
                "p=subprocess.Popen([sys.executable,'-c','import time; time.sleep(30)'], "
                "stdout=subprocess.DEVNULL); print(p.pid, flush=True)"
            ),
        ],
        stdout=subprocess.PIPE,
        start_new_session=True,
    )
    try:
        output, _ = child.communicate(timeout=2)
        descendant = int(output.strip())
        assert child.returncode == 0
        assert descendant in process_guard.group_members(child.pid)
        assert process_guard._retire(child) == 0
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
        process_guard._retire(child)


def test_output_is_capped_even_if_child_exits_between_samples(tmp_path: Path) -> None:
    result = process_guard.run_guarded(
        (sys.executable, "-c", "print('x' * 4096)"),
        output=tmp_path / "worker.log",
        output_bytes=128,
        lock_path=tmp_path / "lock",
    )
    assert result.outcome == "output_limit"
    assert result.output_bytes > 128
    assert (tmp_path / "worker.log").stat().st_size == 128


def test_leader_success_with_background_worker_is_not_completion(
    tmp_path: Path,
) -> None:
    result = process_guard.run_guarded(
        (
            sys.executable,
            "-c",
            (
                "import subprocess,sys; "
                "p=subprocess.Popen([sys.executable,'-c','import time; time.sleep(30)']); "
                "print(p.pid, flush=True)"
            ),
        ),
        output=tmp_path / "worker.log",
        lock_path=tmp_path / "lock",
    )
    assert result.outcome == "descendants_retired"
    descendant = int((tmp_path / "worker.log").read_text().strip())
    state = subprocess.run(
        ["ps", "-o", "stat=", "-p", str(descendant)],
        capture_output=True,
        text=True,
        check=False,
        timeout=2,
    ).stdout.strip()
    assert not state or state.startswith("Z")


def test_missing_memory_samples_are_unavailable_not_zero(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(process_guard, "memory_reader", lambda: ("test", lambda pid: 0))
    result = process_guard.run_guarded(
        (sys.executable, "-c", "print('small')"),
        output=tmp_path / "worker.log",
        lock_path=tmp_path / "lock",
    )
    assert result.outcome == "completed"
    assert result.samples == 0
    assert result.sampled_peak_bytes is None

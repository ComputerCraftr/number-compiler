"""Output and measurement outcomes for guarded child processes."""

from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

from devtools.checks import process_guard
from tests.support.process_guard import zero_memory_reader


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
        timeout=2,
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
    monkeypatch.setattr(process_guard, "memory_reader", zero_memory_reader)
    result = process_guard.run_guarded(
        (sys.executable, "-c", "print('small')"),
        output=tmp_path / "worker.log",
        lock_path=tmp_path / "lock",
    )
    assert result.outcome == "completed"
    assert result.samples == 0
    assert result.sampled_peak_bytes is None

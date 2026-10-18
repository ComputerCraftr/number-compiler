"""Exact session-event timing and cleanup behavior for guarded Isabelle builds."""

from __future__ import annotations

import json
import os
import sys
import time
from pathlib import Path

import pytest

from devtools.checks.isabelle_session_watchdog import IsabelleSessionWatchdog
from devtools.checks.process_guard import DEADLINE_ENV, run_guarded


def test_watchdog_buffers_split_and_unterminated_event_lines() -> None:
    watchdog = IsabelleSessionWatchdog(("Target",), 10)
    watchdog.observe_output(b"Running Tar", 1.0)
    assert watchdog.report()["started_sessions"] == []
    assert watchdog.report()["partial_line_bytes"] == len(b"Running Tar")
    watchdog.observe_output(b"get (building heap)\n", 2.0)
    assert watchdog.report()["started_sessions"] == ["Target"]
    watchdog.observe_output(b"Finished Target (0:00:03 elapsed time)", 4.0)
    assert watchdog.report()["finished_sessions"] == []
    watchdog.finish_output(4.0)
    assert watchdog.report()["finished_sessions"] == ["Target"]
    assert watchdog.check(4.0) is None


def test_watchdog_ignores_reused_and_unadmitted_sessions() -> None:
    watchdog = IsabelleSessionWatchdog(("Rebuilt",), 1)
    watchdog.observe_output(
        b"Finished Reused (0:10:00 elapsed time)\n"
        b"Running Unrequested\nFinished Rebuilt (0:00:01 elapsed time)\n",
        0.0,
    )
    assert watchdog.check(5.0) is None
    report = watchdog.report()
    assert report["started_sessions"] == []
    assert report["finished_sessions"] == []
    assert report["active_sessions"] == []


def test_duplicate_start_does_not_reset_a_live_session_timer() -> None:
    watchdog = IsabelleSessionWatchdog(("Target",), 10)
    watchdog.observe_output(b"Running Target\n", 0.0)
    watchdog.observe_output(b"Building Target\n", 8.0)
    reason = watchdog.check(10.0)
    assert reason is not None and "Target" in reason
    report = watchdog.report()
    assert report["timed_out_session"] == "Target"
    assert report["timed_out_elapsed_seconds"] == 10.0


def test_mismatched_finish_cannot_clear_an_active_session() -> None:
    watchdog = IsabelleSessionWatchdog(("Target", "Other"), 10)
    watchdog.observe_output(b"Running Target\n", 2.0)
    watchdog.observe_output(b"Finished Other (0:00:01 elapsed time)\n", 3.0)
    assert watchdog.check(4.0) is None
    assert watchdog.report()["active_sessions"] == ["Target"]
    assert watchdog.check(12.0) is not None


def test_sequential_sessions_keep_independent_nonresettable_clocks() -> None:
    watchdog = IsabelleSessionWatchdog(("First", "Second"), 10)
    watchdog.observe_output(b"Running First\n", 0.0)
    watchdog.observe_output(b"Finished First (0:00:04 elapsed time)\n", 4.0)
    watchdog.observe_output(b"Running Second\n", 5.0)
    watchdog.observe_output(b"Building Second\n", 12.0)
    assert watchdog.check(14.9) is None
    assert watchdog.report()["finished_sessions"] == ["First"]
    assert watchdog.report()["active_sessions"] == ["Second"]
    assert watchdog.check(15.0) is not None


def test_single_output_chunk_uses_reported_elapsed_time() -> None:
    watchdog = IsabelleSessionWatchdog(("Target",), 10)
    watchdog.observe_output(
        b"Running Target\nFinished Target (0:00:11 elapsed time)\n", 1.0
    )
    assert watchdog.check(1.0) is not None
    assert watchdog.report()["timed_out_session"] == "Target"


def test_live_session_timeout_reaps_the_worker_tree(tmp_path: Path) -> None:
    watchdog = IsabelleSessionWatchdog(("Slow",), 0.25)
    output = tmp_path / "proof.log"
    result = run_guarded(
        (
            sys.executable,
            "-c",
            (
                "import os,subprocess,sys,time; "
                "p=subprocess.Popen([sys.executable,'-c',"
                "'import time; time.sleep(30)'], stdout=subprocess.DEVNULL); "
                "print('Running Slow', flush=True); "
                "print(os.getpid(), flush=True); print(p.pid, flush=True); "
                "time.sleep(30)"
            ),
        ),
        output=output,
        timeout=5,
        progress_watchdog=watchdog,
        lock_path=tmp_path / "lock",
    )
    assert result.outcome == "session_timeout"
    assert "Slow" in result.detail
    assert result.cleanup_confirmed
    pids = tuple(int(line) for line in output.read_text().splitlines()[1:])
    assert len(pids) == 2
    for pid in pids:
        try:
            os.kill(pid, 0)
        except ProcessLookupError:
            continue
        raise AssertionError(f"timed-out Isabelle process {pid} is still alive")


def test_outer_deadline_wins_when_it_expires_before_session_limit(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    watchdog = IsabelleSessionWatchdog(("Slow",), 5)
    deadline = time.monotonic() + 0.4
    monkeypatch.setenv(DEADLINE_ENV, str(deadline))
    result = run_guarded(
        (
            sys.executable,
            "-c",
            "import time; print('Running Slow', flush=True); time.sleep(30)",
        ),
        output=tmp_path / "outer-deadline.log",
        timeout=10,
        progress_watchdog=watchdog,
        lock_path=tmp_path / "lock",
    )
    assert result.outcome == "timeout"
    assert result.cleanup_confirmed
    assert watchdog.report()["timed_out_session"] is None
    assert watchdog.report()["active_sessions"] == ["Slow"]


def test_cancellation_during_watchdog_check_still_cleans_up(tmp_path: Path) -> None:
    class CancelAfterStart(IsabelleSessionWatchdog):
        def check(self, now: float) -> str | None:
            if self.report()["started_sessions"]:
                raise KeyboardInterrupt("synthetic cancellation")
            return super().check(now)

    watchdog = CancelAfterStart(("Slow",), 10)
    result = run_guarded(
        (
            sys.executable,
            "-c",
            "import time; print('Running Slow', flush=True); time.sleep(30)",
        ),
        output=tmp_path / "cancelled.log",
        timeout=5,
        progress_watchdog=watchdog,
        lock_path=tmp_path / "lock",
    )
    assert result.outcome == "interrupted"
    assert "synthetic cancellation" in result.detail
    assert result.cleanup_confirmed


def test_watchdog_report_is_json_safe() -> None:
    watchdog = IsabelleSessionWatchdog(("Target",), 3)
    watchdog.observe_output(b"Running Target\n", 1.0)
    json.dumps(watchdog.report())

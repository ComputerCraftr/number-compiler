"""Proof progress reports are diagnostics, scoped to one guarded run."""

from __future__ import annotations

import json
from pathlib import Path

from devtools.checks.isabelle_proof_progress import ProofProgress


def event(sequence: int, action: str, **changes: object) -> bytes:
    fields: dict[str, object] = {
        "run": "guard-a",
        "session": "Target",
        "lane": "one",
        "invocation": "root",
        "parent": None,
        "stage": "bind",
        "root": 7,
        "event": action,
        "sequence": sequence,
    }
    fields.update(changes)
    return json.dumps(fields).encode() + b"\n"


def test_nested_concurrent_lanes_and_exact_finish_identity() -> None:
    progress = ProofProgress("guard-a", frozenset({"Target"}))
    active = frozenset({"Target"})
    progress.observe(event(1, "start"), active)
    progress.observe(
        event(2, "start", invocation="child", parent="root", stage="slot"), active
    )
    progress.observe(event(3, "start", lane="two", invocation="other"), active)
    progress.observe(event(4, "done", root=8), active)
    progress.observe(
        event(5, "done"), active
    )  # active child prevents parent completion
    progress.observe(
        event(6, "done", invocation="child", parent="root", stage="slot"), active
    )
    progress.observe(event(7, "done"), active)
    report = progress.report("Target")
    assert report["rejected"] == 2
    completed = report["last_completed"]
    assert completed is not None and completed["invocation"] == "root"
    assert [item["invocation"] for item in report["active"]] == ["other"]
    json.dumps(report)


def test_stale_other_guard_inactive_session_and_partial_lines() -> None:
    progress = ProofProgress("guard-a", frozenset({"Target"}))
    active = frozenset({"Target"})
    data = event(1, "start")
    progress.observe(data[:-1], active)
    assert progress.report("Target")["active"] == []
    progress.observe(b"\n", active)
    progress.observe(event(2, "done", run="old"), active)
    progress.observe(event(2, "done", session="Prerequisite"), active)
    progress.observe(event(1, "done"), active)
    assert progress.report("Target")["rejected"] == 3
    progress.observe(event(3, "fail"), active)
    failure = progress.report("Target")["last_failure"]
    assert failure is not None and failure["stage"] == "bind"
    assert progress.report("Target")["active"] == []
    progress.observe(event(4, "start"), active)  # completed invocation cannot restart
    assert progress.report("Target")["rejected"] == 4


def test_prerequisite_is_separate_and_duplicate_fields_are_rejected() -> None:
    progress = ProofProgress(
        "guard-a", frozenset({"Target"}), frozenset({"Target", "Prerequisite"})
    )
    active = frozenset({"Prerequisite"})
    progress.observe(event(1, "start", session="Prerequisite"), active)
    progress.observe(b'{"run":"guard-a","run":"guard-a"}\n', active)
    assert progress.report("Prerequisite")["scope"] == "prerequisite"
    assert progress.report("Target")["active"] == []
    assert progress.report("Prerequisite")["rejected"] == 1


def test_oversized_line_is_discarded_without_accepting_a_suffix() -> None:
    progress = ProofProgress("guard-a", frozenset({"Target"}))
    progress.observe(b"x" * 20000 + event(1, "start"), frozenset({"Target"}))
    assert progress.report("Target")["active"] == []
    assert progress.report("Target")["rejected"] == 1
    progress.observe(event(2, "start"), frozenset({"Target"}))
    assert len(progress.report("Target")["active"]) == 1


def test_fake_reporter_reconciles_with_session_watchdog(tmp_path: Path) -> None:
    from devtools.checks.isabelle_proof_progress import ProofProgressFile
    from devtools.checks.isabelle_session_watchdog import IsabelleSessionWatchdog

    sidecar = tmp_path / "progress.jsonl"
    sidecar.write_bytes(event(1, "start", session="Prerequisite"))
    progress = ProofProgressFile(
        sidecar, "guard-a", frozenset({"Target"}), frozenset({"Target", "Prerequisite"})
    )
    watchdog = IsabelleSessionWatchdog(
        ("Prerequisite", "Target"), 10, proof_progress=progress
    )
    watchdog.observe_output(b"Building Prerequisite\n", 0.0)
    assert progress.report("Prerequisite")["scope"] == "prerequisite"
    with sidecar.open("ab") as stream:
        stream.write(event(2, "done", session="Prerequisite"))
    watchdog.observe_output(b"Finished Prerequisite\n", 1.0)
    assert progress.report("Prerequisite")["last_completed"] is not None
    with sidecar.open("ab") as stream:
        stream.write(event(3, "start", invocation="target-root"))
        stream.write(event(4, "start", invocation="unfinished")[:-1])
    watchdog.observe_output(b"Building Target\n", 2.0)
    assert watchdog.check(12.0) is not None
    report = progress.report("Target")
    assert [item["invocation"] for item in report["active"]] == ["target-root"]
    assert report["partial_line_bytes"] > 0


def test_guarded_timeout_retains_incomplete_scope(tmp_path: Path) -> None:
    import sys
    import time

    from devtools.checks.isabelle_proof_progress import ProofProgressFile
    from devtools.checks.isabelle_session_watchdog import IsabelleSessionWatchdog
    from devtools.checks.process_guard import run_guarded

    sidecar = tmp_path / "timeout.jsonl"
    sidecar.touch()
    progress = ProofProgressFile(sidecar, "guard-a", frozenset({"Target"}))
    watchdog = IsabelleSessionWatchdog(("Target",), 0.5, proof_progress=progress)
    finished = {"invocation": "freeze", "parent": "root", "stage": "freeze-source"}
    entered = {"invocation": "replay", "parent": "root", "stage": "bind-root"}
    records = b"".join(
        (
            event(1, "start"),
            event(2, "start", **finished),
            event(3, "done", **finished),
            event(4, "start", **entered),
        )
    )
    late = event(5, "fail", **entered) + event(6, "fail")
    script = "\n".join(
        (
            "import pathlib, signal, time",
            f"path = pathlib.Path({str(sidecar)!r})",
            "def terminate(_signal, _frame):",
            "    with path.open('ab') as stream:",
            f"        stream.write({late!r})",
            "    raise SystemExit(0)",
            "signal.signal(signal.SIGTERM, terminate)",
            f"path.write_bytes({records!r})",
            "print('Building Target', flush=True)",
            "time.sleep(5)",
        )
    )
    result = run_guarded(
        (sys.executable, "-c", script),
        output=tmp_path / "timeout.log",
        timeout=5,
        interval=0.05,
        lock_path=tmp_path / "guard.lock",
        progress_watchdog=watchdog,
    )
    assert result.outcome == "session_timeout"
    assert result.cleanup_confirmed
    assert watchdog.report()["timed_out_session"] == "Target"
    assert sidecar.read_bytes() == records + late
    before = progress.report("Target")
    completed = before["last_completed"]
    assert completed is not None and completed["stage"] == "freeze-source"
    assert [scope["stage"] for scope in before["active"]] == ["bind-root"]
    assert before["last_failure"] is None
    assert before["unread_bytes"] == len(late)
    watchdog.finish_output(time.monotonic())
    assert watchdog.check(time.monotonic()) is not None
    assert progress.report("Target") == before


def test_proof_progress_defaults_to_coarse_and_honors_explicit_mode() -> None:
    from devtools.checks.isabelle_proof_progress import proof_progress_mode

    assert proof_progress_mode({}) == "coarse"
    for mode in ("off", "coarse", "detailed"):
        assert proof_progress_mode({"NUMBER_COMPILER_PROOF_PROGRESS": mode}) == mode


def test_batch_race_and_final_record_for_completed_session(tmp_path: Path) -> None:
    from devtools.checks.isabelle_proof_progress import ProofProgressFile
    from devtools.checks.isabelle_session_watchdog import IsabelleSessionWatchdog

    sidecar = tmp_path / "racing.jsonl"
    sidecar.write_bytes(event(1, "start", session="Target"))
    progress = ProofProgressFile(
        sidecar, "guard-a", frozenset({"Target"}), frozenset({"Target", "Prerequisite"})
    )
    watchdog = IsabelleSessionWatchdog(
        ("Prerequisite", "Target"), 10, proof_progress=progress
    )
    watchdog.observe_output(b"Building Prerequisite\n", 1.0)
    assert progress.report("Target")["pending_records"] == 1
    watchdog.observe_output(b"Finished Prerequisite\nBuilding Target\n", 2.0)
    assert progress.report("Target")["active"][0]["invocation"] == "root"
    with sidecar.open("ab") as stream:
        stream.write(event(2, "start", invocation="inner", parent="root", stage="bind"))
    watchdog.check(4.0)
    report = progress.report("Target")
    assert [item["invocation"] for item in report["active"]] == ["inner"]
    assert report["active"][0]["elapsed_observed_seconds"] == 0
    watchdog.check(7.0)
    assert progress.report("Target")["active"][0]["elapsed_observed_seconds"] == 3
    watchdog.observe_output(b"Finished Target\n", 8.0)
    with sidecar.open("ab") as stream:
        stream.write(event(3, "done", invocation="inner", parent="root", stage="bind"))
    watchdog.finish_output(9.0)
    with sidecar.open("ab") as stream:
        stream.write(event(4, "start", invocation="late-stale"))
    watchdog.finish_output(9.1)
    assert progress.report("Target")["rejected"] == 1
    assert (
        progress.report("Target")["last_completed_by_lane"]["one"]["invocation"]
        == "inner"
    )


def test_each_session_has_its_own_serialized_sequence() -> None:
    progress = ProofProgress(
        "guard-a", frozenset({"Target"}), frozenset({"Target", "Prerequisite"})
    )
    progress.observe(
        event(1, "start", session="Prerequisite"), frozenset({"Prerequisite"})
    )
    progress.observe(
        event(2, "done", session="Prerequisite"), frozenset({"Prerequisite"})
    )
    progress.observe(event(1, "start"), frozenset({"Target"}))
    assert progress.report("Target")["active"][0]["invocation"] == "root"

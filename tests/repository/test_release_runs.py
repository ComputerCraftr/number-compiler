"""Evidence ownership survives fresh runs, interruption and proof relocation."""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
from collections.abc import Mapping
from pathlib import Path

import pytest

from devtools.checks.validation_policy import PYTHON_COMMAND, ExecutionPolicy
from devtools.git_source import (
    AcceptanceCheckoutError,
    acceptance_checkout,
    git_source,
)
from devtools.runs import EvidenceRun
from tests.support.git_repositories import commit_fixture, git


def test_python_tool_versions_do_not_probe_foreign_path_installations(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from devtools import runs

    def locate(name: str) -> None:
        assert name != "ruff", "the interpreter owns the pinned Ruff version"

    def no_subprocess(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("Python tool inventory must not probe Isabelle")

    monkeypatch.setattr(shutil, "which", locate)
    monkeypatch.setattr(subprocess, "run", no_subprocess)
    monkeypatch.setattr(runs, "version", lambda _name: "pinned-version")
    tools = runs.tool_versions()
    assert tools["ruff"] == "pinned-version"
    assert "isabelle" not in tools


def source(tmp_path: Path) -> Path:
    (tmp_path / ".gitignore").write_text("/results/\n")
    (tmp_path / "pyproject.toml").write_text('[project]\nversion="0.0.0"\n')
    proof = tmp_path / "proofs/isabelle/Test.thy"
    proof.parent.mkdir(parents=True)
    proof.write_text("theory Test imports Main begin end\n")
    isabelle_root = tmp_path / "proofs/isabelle"
    (isabelle_root / "ROOT").write_text(
        "session Base = HOL +\n"
        "  theories\n"
        "    Test\n"
        'session Prefix_Effect_Core in "prefix" = Base +\n'
    )
    (isabelle_root / "prefix").mkdir()
    commit_fixture(tmp_path)
    return proof


def test_git_provenance_tracks_proof_changes_without_file_scans(
    tmp_path: Path,
) -> None:
    proof = source(tmp_path)
    before = git_source(tmp_path)
    proof.write_text(proof.read_text() + "\n(* altered proof *)\n")
    dirty = git_source(tmp_path)
    assert dirty.commit == before.commit
    assert dirty.tree == before.tree
    assert dirty.dirty
    git(tmp_path, "add", "proofs")
    git(
        tmp_path,
        "-c",
        "user.name=Test",
        "-c",
        "user.email=test@example.invalid",
        "commit",
        "-qm",
        "proof update",
        check=True,
    )
    after = git_source(tmp_path)
    assert not after.dirty
    assert after.commit != before.commit
    assert after.tree != before.tree


def test_fresh_runs_and_manifest_completeness(tmp_path: Path) -> None:
    source(tmp_path)
    with EvidenceRun(
        root=tmp_path, command=("probe",), limits={"seconds": 35}
    ) as first:
        first.record({"command": ["probe"], "outcome": "completed"})
    with EvidenceRun(root=tmp_path) as second:
        assert first.path != second.path
    payload = json.loads((first.path / "manifest.json").read_text())
    assert payload["outcome"] == "completed"
    assert payload["git_source_before"] == payload["git_source_after"]
    assert payload["git_identity_unchanged"] is True
    assert payload["cacheable"] is False
    assert payload["limits"] == {"seconds": 35}
    assert payload["schema_version"] == 2
    assert payload["execution_metrics_schema"] == 8
    assert payload["tool_versions"]["python"]
    assert payload["started_at"] and payload["finished_at"]
    with pytest.raises(FileExistsError):
        EvidenceRun(root=tmp_path, output_dir=first.path)
    with pytest.raises(ValueError, match="completed"):
        first.record({"outcome": "changed"})


def test_interrupted_and_changed_runs_never_pass(tmp_path: Path) -> None:
    proof = source(tmp_path)
    run = EvidenceRun(root=tmp_path)
    with pytest.raises(KeyboardInterrupt), run:
        raise KeyboardInterrupt()
    assert run.manifest["outcome"] == "interrupted"
    with EvidenceRun(root=tmp_path) as changed:
        proof.write_text("changed\n")
    assert changed.manifest["outcome"] == "completed"
    assert changed.manifest["git_identity_unchanged"] is True
    after = changed.manifest["git_source_after"]
    assert type(after) is dict and after["git_dirty"] is True
    assert changed.manifest["cacheable"] is False


def test_evidence_context_reentry_preserves_owner_and_bytecode_state(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    source(tmp_path)
    monkeypatch.setattr(sys, "dont_write_bytecode", False)
    with EvidenceRun(root=tmp_path) as run:
        assert sys.dont_write_bytecode
        with pytest.raises(ValueError, match="more than once"), run:
            pytest.fail("reentry must not close the outer evidence")
        assert not run.closed
        assert sys.dont_write_bytecode
        run.record({"outcome": "completed"})
    assert run.closed
    assert not sys.dont_write_bytecode
    with pytest.raises(ValueError, match="more than once"), run:
        pytest.fail("completed evidence must not regain context ownership")
    assert not sys.dont_write_bytecode


def test_gitignore_allows_new_sprint_and_ignores_generated_paths() -> None:
    import subprocess

    from devtools.paths import repository_root

    root = repository_root()
    for path, ignored in (
        ("results/runs/arbitrary/report.json", True),
        ("results/current/week-of-2026-10-04/new-topic.md", True),
        ("docs/sprints/week-of-2026-10-04/new-topic.md", False),
    ):
        result = subprocess.run(
            ["git", "check-ignore", "--no-index", "-q", path], cwd=root, check=False
        )
        assert result.returncode == (0 if ignored else 1)


def test_dirty_development_runs_are_diagnostic_only(tmp_path: Path) -> None:
    source(tmp_path)
    (tmp_path / "new_source.py").write_text("value = 1\n")
    with EvidenceRun(root=tmp_path) as run:
        before = run.manifest["git_source_before"]
        assert type(before) is dict and before["git_dirty"] is True
    assert run.manifest["outcome"] == "completed"
    assert run.manifest["cacheable"] is False


def test_only_successful_clean_acceptance_worktree_can_be_reusable(
    tmp_path: Path,
) -> None:
    source(tmp_path)
    with acceptance_checkout(tmp_path) as checkout:
        run = EvidenceRun(
            root=checkout,
            output_dir=tmp_path / "results" / "runs" / "acceptance-output",
            evidence_mode="acceptance",
        )
        with run:
            run.record({"outcome": "completed"})
    run.mark_acceptance_complete()
    assert run.manifest["acceptance_verified"] is True
    assert run.manifest["cacheable"] is True
    assert run.manifest["reusable"] is True


def test_development_and_failed_acceptance_cannot_be_certified(tmp_path: Path) -> None:
    source(tmp_path)
    with EvidenceRun(root=tmp_path) as development:
        pass
    with pytest.raises(ValueError, match="development"):
        development.mark_acceptance_complete()
    with acceptance_checkout(tmp_path) as checkout:
        failed = EvidenceRun(
            root=checkout,
            output_dir=tmp_path / "results" / "runs" / "failed-output",
            evidence_mode="acceptance",
        )
        with pytest.raises(RuntimeError, match="fixture failure"), failed:
            failed.record({"outcome": "failed"})
            raise RuntimeError("fixture failure")
    with pytest.raises(ValueError, match="completed"):
        failed.mark_acceptance_complete()


def test_checkout_cleanup_failure_revokes_acceptance_evidence(tmp_path: Path) -> None:
    source(tmp_path)
    worktree_parent = tmp_path.parent / f"{tmp_path.name}-acceptance"
    run: EvidenceRun | None = None
    checkout: Path | None = None
    with (
        pytest.raises(AcceptanceCheckoutError, match="was preserved"),
        acceptance_checkout(tmp_path, worktree_parent) as active_checkout,
    ):
        checkout = active_checkout
        active_run = EvidenceRun(
            root=active_checkout,
            output_dir=tmp_path / "results" / "runs" / "acceptance-cleanup",
            evidence_mode="acceptance",
        )
        run = active_run
        with active_run:
            active_run.record({"outcome": "completed"})
        proof = active_checkout / "proofs/isabelle/Test.thy"
        proof.write_text(proof.read_text() + "\n(* cleanup failure *)\n")
    assert run is not None and checkout is not None
    run.mark_acceptance_failed("acceptance checkout cleanup failed")
    assert run.manifest["outcome"] == "acceptance_verification_failed"
    assert run.manifest["acceptance_verified"] is False
    assert run.manifest["cacheable"] is False
    assert run.manifest["reusable"] is False
    after = run.manifest["git_source_after_acceptance_checkout"]
    assert isinstance(after, dict) and after["git_dirty"] is True
    try:
        git(tmp_path, "worktree", "remove", "--force", str(checkout))
    finally:
        worktree_parent.rmdir()


@pytest.mark.parametrize("process_outcome", ["memory_limit", "timeout", "child_failed"])
def test_source_change_preserves_process_failure(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, process_outcome: str
) -> None:
    from devtools.checks import release
    from devtools.checks.process_guard import GuardResult

    proof = source(tmp_path)

    def failed_child(*args: object, **kwargs: object) -> GuardResult:
        proof.write_text(proof.read_text() + "\n(* concurrent edit *)\n")
        return GuardResult(
            schema=1,
            outcome=process_outcome,
            child_returncode=-15,
            elapsed_seconds=60,
            sampled_peak_bytes=4096 * 1024**2,
            memory_limit_bytes=4096 * 1024**2,
            memory_measurement="test",
            sample_interval_seconds=0.05,
            samples=1,
            output_bytes=0,
            detail="",
        )

    monkeypatch.setattr(release, "run_guarded", failed_child)
    with EvidenceRun(root=tmp_path) as run:
        assert not release.execute(
            run,
            "proof",
            ("isabelle",),
            ExecutionPolicy(60, 6 * 1024**3),
        )
        step = json.loads((run.path / "proof.json").read_text())
        assert step["git_revision_stable"] is True
        assert step["git_source_before"]["git_dirty"] is False
        assert step["git_source_after"]["git_dirty"] is True
        assert step["process_outcome"] == process_outcome
        assert step["child_returncode"] == -15


@pytest.mark.parametrize("elapsed", ["0:00:01", "0:01:01"])
def test_release_proof_selection_preserves_aggregate_and_limits(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, elapsed: str
) -> None:
    from devtools.checks import release

    source(tmp_path)
    calls: list[tuple[str, tuple[str, ...], int, int]] = []

    def execute(
        run: EvidenceRun,
        name: str,
        command: tuple[str, ...],
        policy: ExecutionPolicy,
        *,
        acceptance: bool = False,
        pytest_run: bool = False,
        record_fields: Mapping[str, object] | None = None,
    ) -> bool:
        del acceptance, pytest_run, record_fields
        calls.append(
            (
                name,
                command,
                int(policy.timeout_seconds),
                int(policy.memory_bytes) // (1024**2),
            )
        )
        if name == "isabelle-version":
            (run.path / "isabelle-version.log").write_text("Isabelle2026-1\n")
        elif name == "proof-session-inventory":
            (run.path / "proof-session-inventory.log").write_text(
                "Base\nPrefix_Effect_Core\n"
            )
        elif name == "proofs":
            (run.path / "proofs.log").write_text(
                "Finished Base (0:00:01 elapsed time)\n"
                f"Finished Prefix_Effect_Core ({elapsed} elapsed time)\n"
            )
        return True

    monkeypatch.setattr(release, "execute", execute)
    with EvidenceRun(root=tmp_path) as run:
        assert release.proofs(run, "isabelle", ()) is (elapsed == "0:00:01")
        assert release.proofs(run, "isabelle", ("Prefix_Effect_Core",)) is (
            elapsed == "0:00:01"
        )
    assert calls[0][1] == ("isabelle", "version")
    assert "-D" in calls[1][1] and "-d" not in calls[1][1]
    assert "-D" in calls[2][1] and "-d" not in calls[2][1]
    assert calls[3][1] == ("isabelle", "version")
    assert "-d" in calls[4][1] and "-D" not in calls[4][1]
    assert "-d" in calls[5][1] and "-D" not in calls[5][1]
    assert calls[5][1][-1] == "Prefix_Effect_Core"
    assert [(name, seconds, memory) for name, _, seconds, memory in calls] == [
        ("isabelle-version", 60, 6144),
        ("proof-session-inventory", 60, 6144),
        ("proofs", 180, 6144),
        ("isabelle-version", 60, 6144),
        ("proof-session-inventory", 60, 6144),
        ("proofs", 180, 6144),
    ]
    steps = run.manifest.get("steps")
    assert isinstance(steps, list)
    failures = [
        step
        for step in steps
        if isinstance(step, dict) and step.get("name") == "proof-session-duration-gate"
    ]
    assert len(failures) == (0 if elapsed == "0:00:01" else 2)
    assert any(
        step.get("tool_versions") == {"isabelle": "Isabelle2026-1"}
        for step in steps
        if isinstance(step, dict)
    )
    for _, command, _, _ in (calls[2], calls[5]):
        # Isabelle clears _JAVA_OPTIONS during its settings initialization.
        # Apply the actual heap limits inside that initialized environment.
        assert command[:2] == ("isabelle", "env")
        assert command[2] == (
            "ISABELLE_TOOL_JAVA_OPTIONS="
            "-Djava.awt.headless=true -Xms128m -Xmx1024m -Xss16m"
        )
        assert command[3] == "ML_OPTIONS=--minheap 128 --maxheap 4096"
        assert command[4:6] == ("isabelle", "build")


def test_release_quality_retains_failures_and_attempts_later_checks(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from devtools.checks import release

    source(tmp_path)
    calls: list[str] = []

    def execute(
        run: EvidenceRun,
        name: str,
        command: tuple[str, ...],
        policy: ExecutionPolicy = PYTHON_COMMAND,
        *,
        acceptance: bool = False,
        pytest_run: bool = False,
    ) -> bool:
        del run, acceptance, pytest_run
        calls.append(name)
        assert policy.timeout_seconds == 60
        assert policy.memory_bytes == 4 * 1024**3
        if name in ("ruff", "format"):
            assert command[:3] == (sys.executable, "-m", "ruff")
        return name != "mypy"

    monkeypatch.setattr(release, "execute", execute)
    with EvidenceRun(root=tmp_path) as run:
        assert not release.quality(run)
    assert calls == [
        "mypy",
        "ruff",
        "format",
        "policy",
        "docs",
        "proof-index",
        "package",
    ]


def test_all_suite_enforces_validator_time_gate(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from devtools.checks import release

    source(tmp_path)
    with EvidenceRun(root=tmp_path) as run:
        (run.path / "all-collect.log").write_text(
            "tests/test_example.py::test_example\n"
        )
        monkeypatch.setattr(release, "execute", lambda *args, **kwargs: True)
        monkeypatch.setattr(
            release,
            "validate_serial_release",
            lambda *args, **kwargs: {"serial_time_gate_passed": False},
        )
        assert not release.pytest_suite(run, "all")
    assert "300-second" in str(run.manifest["steps"])

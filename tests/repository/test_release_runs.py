"""Evidence ownership survives fresh runs, interruption and proof relocation."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from devtools.checks.test_run_evidence import FINGERPRINT_VERSION, source_fingerprint
from devtools.runs import EvidenceRun


def source(tmp_path: Path) -> Path:
    (tmp_path / "pyproject.toml").write_text('[project]\nversion="0.0.0"\n')
    proof = tmp_path / "proofs/isabelle/Test.thy"
    proof.parent.mkdir(parents=True)
    proof.write_text("theory Test imports Main begin end\n")
    return proof


def test_fingerprint_five_covers_authored_proofs(tmp_path: Path) -> None:
    proof = source(tmp_path)
    before = source_fingerprint(tmp_path)
    proof.write_text(proof.read_text() + "\n(* altered proof *)\n")
    assert FINGERPRINT_VERSION == 5
    assert source_fingerprint(tmp_path) != before


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
    assert payload["source_fingerprint_before"] == payload["source_fingerprint_after"]
    assert payload["limits"] == {"seconds": 35}
    assert payload["fingerprint_version"] == 5
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
    assert changed.manifest["outcome"] == "source_changed"


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


def test_restored_source_bytes_still_invalidate_run(tmp_path: Path) -> None:
    proof = source(tmp_path)
    old = proof.read_text()
    with EvidenceRun(root=tmp_path) as run:
        proof.write_text("temporary edit\n")
        proof.write_text(old)
    assert (
        run.manifest["source_fingerprint_before"]
        == run.manifest["source_fingerprint_after"]
    )
    assert run.manifest["outcome"] == "source_changed"
    assert run.manifest["source_revision_unchanged"] is False


def test_release_proof_selection_preserves_aggregate_and_limits(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from devtools.checks import release

    source(tmp_path)
    calls: list[tuple[tuple[str, ...], int, int]] = []

    def execute(
        run: EvidenceRun,
        name: str,
        command: tuple[str, ...],
        timeout: int = 35,
        memory_mib: int = 1024,
    ) -> bool:
        calls.append((command, timeout, memory_mib))
        return True

    monkeypatch.setattr(release, "execute", execute)
    with EvidenceRun(root=tmp_path) as run:
        assert release.proofs(run, "isabelle", ())
        assert release.proofs(run, "isabelle", ("Prefix_Effect_Core",))
    assert "-D" in calls[0][0] and "-d" not in calls[0][0]
    assert "-d" in calls[1][0] and "-D" not in calls[1][0]
    assert calls[1][0][-1] == "Prefix_Effect_Core"
    assert all((seconds, memory) == (60, 4096) for _, seconds, memory in calls)


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
        timeout: int = 35,
        memory_mib: int = 1024,
    ) -> bool:
        calls.append(name)
        assert timeout == 35 and memory_mib == 1024
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
            lambda *args: {"serial_time_gate_passed": False},
        )
        assert not release.pytest_suite(run, "all")
    assert "300-second" in str(run.manifest["steps"])

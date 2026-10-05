"""Evidence tools do not start a second, unguarded pytest collection."""

from __future__ import annotations

import subprocess
from pathlib import Path
from types import SimpleNamespace

import pytest

from devtools.checks import action_morphism_adversarial_audit as audit


def test_adversarial_audit_routes_one_union_through_release_runner(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(audit, "ROOT", tmp_path)
    monkeypatch.setattr(
        audit,
        "CASES",
        {"probe": ("tests/test_cases.py", "tests/test_cases.py::test_fast")},
    )
    observed: list[tuple[str, ...]] = []

    def failed_runner(command: list[str], **_kwargs: object) -> SimpleNamespace:
        observed.append(tuple(command))
        return SimpleNamespace(returncode=1, stdout="", stderr="failed")

    monkeypatch.setattr(subprocess, "run", failed_runner)
    with pytest.raises(RuntimeError, match="regression union failed"):
        audit.run_cases(("probe",))
    assert len(observed) == 1
    command = observed[0]
    assert command[1:4] == ("-m", "devtools.checks.release", "--suite")
    assert "pytest" not in command
    assert command.count("--select") == 1
    assert command[-2:] == ("--select", "tests/test_cases.py")

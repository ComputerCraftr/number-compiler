"""Fresh release manifests must resist filtering and concurrent tree changes."""

from __future__ import annotations

import subprocess
from pathlib import Path
from types import SimpleNamespace
from typing import TYPE_CHECKING

import pytest

from devtools.checks.test_run_evidence import collect_required

if TYPE_CHECKING:
    import pathlib


def tree(tmp_path: Path) -> pathlib.Path:
    tests = tmp_path / "tests"
    tests.mkdir()
    test = tests / "test_cases.py"
    test.write_text(
        "def test_fast():\n    pass\n\ndef test_slow_regression():\n    pass\n"
    )
    return test


def test_required_collection_cannot_silently_inherit_environment_test_filter(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    tree(tmp_path)
    monkeypatch.setenv("PYTEST_ADDOPTS", "-k fast")
    nodes = collect_required(tmp_path, ("tests/test_cases.py",))
    assert set(nodes) == {
        "tests/test_cases.py::test_fast",
        "tests/test_cases.py::test_slow_regression",
    }


def test_required_collection_cannot_inherit_an_explicit_external_filter_plugin(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    tree(tmp_path)
    (tmp_path / "filter_plugin.py").write_text(
        "def pytest_collection_modifyitems(items):\n"
        '    items[:] = [item for item in items if "slow_regression" not in item.name]\n'
    )
    monkeypatch.setenv("PYTEST_PLUGINS", "filter_plugin")
    nodes = collect_required(tmp_path, ("tests/test_cases.py",))
    assert set(nodes) == {
        "tests/test_cases.py::test_fast",
        "tests/test_cases.py::test_slow_regression",
    }


def test_required_collection_rejects_source_change_during_collection(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    test = tree(tmp_path)

    def changed(*args: object, **kwargs: object) -> SimpleNamespace:
        test.write_text(test.read_text() + "\ndef test_new_regression():\n    pass\n")
        return SimpleNamespace(
            returncode=0,
            stdout="tests/test_cases.py::test_fast\n"
            "tests/test_cases.py::test_slow_regression\n",
            stderr="",
        )

    monkeypatch.setattr(subprocess, "run", changed)
    with pytest.raises(ValueError, match="changed|stale"):
        collect_required(tmp_path, ("tests/test_cases.py",))


def test_fresh_audit_execution_cannot_report_filtered_group_as_complete(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from devtools.checks import action_morphism_adversarial_audit as runner

    tree(tmp_path)
    monkeypatch.setattr(runner, "ROOT", tmp_path)
    monkeypatch.setattr(runner, "CASES", {"probe": ("tests/test_cases.py",)})
    monkeypatch.setenv("PYTEST_ADDOPTS", "-k fast")
    try:
        result = runner.run_case("probe")
    except (RuntimeError, ValueError):
        # The synthetic tree deliberately lacks the repository evidence hook.
        # Rejection is valid; certifying its single selected test is not.
        return
    assert result["tests"] == 2, "fresh audit silently omitted the slow regression"

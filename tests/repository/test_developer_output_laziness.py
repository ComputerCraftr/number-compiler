"""Imports stay read-only; invoked report writers share the chosen evidence run."""

from __future__ import annotations

import ast
import importlib.util
import json
import sys
from pathlib import Path
from typing import Never

import pytest

from devtools import paths, runs
from tests.support.git_repositories import commit_fixture

OUTPUT_MODULES = (
    "collatz_raw_field_probe",
    "compiler_debt_probe",
    "cross_domain_itinerary_probe",
    "cyclotomic_special_probe",
    "prime_coordinate_probe",
    "special_binary_jump_probe",
    "special_successor_generator_probe",
    "terminal_projective_wreath_probe",
    "terminal_section_constructor_frontier_probe",
)


def forbidden(*args: object, **kwargs: object) -> Never:
    raise AssertionError("import allocated a report or evidence run")


@pytest.mark.parametrize("module", OUTPUT_MODULES)
def test_benchmark_import_never_allocates_evidence(
    module: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    source = paths.repository_root() / "devtools" / "benchmarks" / f"{module}.py"
    monkeypatch.setattr(paths, "report_directory", forbidden)
    monkeypatch.setattr(paths, "report_output", forbidden)
    monkeypatch.setattr(runs, "EvidenceRun", forbidden)
    identity = f"_output_laziness_{module}"
    specification = importlib.util.spec_from_file_location(identity, source)
    assert specification is not None and specification.loader is not None
    loaded = importlib.util.module_from_spec(specification)
    monkeypatch.setitem(sys.modules, identity, loaded)
    specification.loader.exec_module(loaded)


def test_all_benchmark_output_allocations_are_demanded() -> None:
    root = paths.repository_root() / "devtools" / "benchmarks"
    for source in root.rglob("*.py"):
        tree = ast.parse(source.read_text())
        pending: list[ast.AST] = list(tree.body)
        while pending:
            node = pending.pop()
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                continue
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                assert node.func.id not in {"report_directory", "report_output"}, (
                    source,
                    node.lineno,
                )
            pending.extend(ast.iter_child_nodes(node))


def test_explicit_output_dir_contains_all_invoked_report_outputs(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    (tmp_path / "pyproject.toml").write_text('[project]\nversion="0.0.0"\n')
    commit_fixture(tmp_path)
    destination = tmp_path / "chosen-run"
    monkeypatch.setattr(paths, "repository_root", lambda: tmp_path)
    monkeypatch.setattr(runs, "repository_root", lambda: tmp_path)
    original = ["example-probe", "--output-dir", str(destination), "--probe-option"]
    monkeypatch.setattr(sys, "argv", original)
    monkeypatch.setattr(sys, "orig_argv", [sys.executable, *original])

    def main() -> None:
        assert sys.argv == ["example-probe", "--probe-option"]
        paths.report_output("devtools.benchmarks.example", "metrics.json").write_text(
            '{"measurement": 1}\n'
        )
        paths.report_output("devtools.benchmarks.example", "report.md").write_text(
            "Measured one.\n"
        )

    assert runs.run_reported(main) == 0
    assert sys.argv is original
    assert (destination / "benchmarks/example/metrics.json").is_file()
    assert (destination / "benchmarks/example/report.md").is_file()
    manifest = json.loads((destination / "manifest.json").read_text())
    assert manifest["outcome"] == "completed"
    assert manifest["command"][-4:] == original
    assert not (tmp_path / "results").exists()

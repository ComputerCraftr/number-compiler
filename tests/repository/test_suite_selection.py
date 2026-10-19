"""Canonical suite partitions rely on one collection and one JUnit manifest."""

from __future__ import annotations

import os
from pathlib import Path
from types import SimpleNamespace
from typing import cast

import pytest

from devtools.checks.test_run_evidence import (
    classify_execution_mode,
    pytest_environment,
)
from devtools.paths import repository_root
from tests.conftest import pytest_collection_modifyitems

ROOT = repository_root()


class _Item:
    def __init__(self, path: Path, fixtures: tuple[str, ...] = ()) -> None:
        self.path = path
        self.fixturenames = fixtures
        self.config = SimpleNamespace(rootpath=ROOT)
        self.nodeid = f"{path.relative_to(ROOT).as_posix()}::test_sample"
        self.user_properties: list[tuple[str, str]] = []
        self.markers: set[str] = set()

    def add_marker(self, marker: object) -> None:
        name = getattr(marker, "name", None)
        assert isinstance(name, str)
        self.markers.add(name)


def test_test_collection_assigns_validation_partition_automatically() -> None:
    ordinary = _Item(ROOT / "tests/test_partition_sample.py")
    automatic_validation = _Item(ROOT / "tests/validation/test_sample.py")
    pytest_collection_modifyitems(
        [cast(pytest.Item, ordinary), cast(pytest.Item, automatic_validation)]
    )
    assert "validation" not in ordinary.markers
    assert "validation" in automatic_validation.markers


def test_source_graph_collection_is_stable_and_preserves_every_node() -> None:
    graph = _Item(ROOT / "tests/test_graph.py", ("production_ast_graph",))
    runtime = _Item(ROOT / "tests/test_runtime.py")
    proof = _Item(ROOT / "tests/test_proof.py", ("repository_proof_graph",))
    registry = _Item(ROOT / "tests/test_registry.py", ("repository_sessions",))
    lifecycle = _Item(ROOT / "tests/test_lifecycle.py")
    items = [
        cast(pytest.Item, item) for item in (graph, runtime, proof, registry, lifecycle)
    ]
    pytest_collection_modifyitems(items)
    expected = [
        cast(pytest.Item, item) for item in (runtime, registry, lifecycle, graph, proof)
    ]
    assert items == expected
    assert all(len(item.user_properties) == 1 for item in items)


def test_guarded_pytest_environment_drops_external_filters(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("PYTEST_ADDOPTS", "-k fast")
    monkeypatch.setenv("PYTEST_PLUGINS", "filter_plugin")
    environment = pytest_environment()
    assert "PYTEST_ADDOPTS" not in environment
    assert "PYTEST_PLUGINS" not in environment
    assert environment["PYTEST_DISABLE_PLUGIN_AUTOLOAD"] == "1"
    assert os.environ["PYTEST_ADDOPTS"] == "-k fast"


@pytest.mark.parametrize(
    ("expression", "expected"),
    (
        ("not validation", "serial-unit"),
        ("validation", "serial-validation"),
        ("", "serial-unfiltered"),
    ),
)
def test_execution_mode_classifies_release_and_validation_partitions(
    expression: str,
    expected: str,
) -> None:
    assert (
        classify_execution_mode(
            mark_expression=expression,
            parallel=False,
            keyword="",
            deselected=False,
            last_failed=False,
            collection_args=("tests",),
        )
        == expected
    )

"""Unit, exhaustive-validation, and release collections stay distinct."""

from __future__ import annotations

import json
import subprocess
import sys
import tomllib
from pathlib import Path

from devtools.checks.test_run_evidence import collect_required, pytest_environment
from devtools.paths import repository_root

ROOT = repository_root()


def _temporary_suite(root: Path) -> tuple[Path, tuple[Path, ...]]:
    configured = tomllib.loads((ROOT / "pyproject.toml").read_text())["tool"]["pytest"][
        "ini_options"
    ]
    config = root / "pyproject.toml"
    config.write_text(
        "[tool.pytest.ini_options]\n"
        f"testpaths = {json.dumps(configured['testpaths'])}\n"
        f"addopts = {json.dumps(configured['addopts'])}\n"
        f"markers = {json.dumps(configured['markers'])}\n"
    )
    tests = root / "tests"
    validation = tests / "validation"
    validation.mkdir(parents=True)
    ordinary = tests / "test_partition_samples.py"
    ordinary.write_text(
        "import pytest\n\n"
        "def test_unit_sample():\n"
        "    pass\n\n"
        "@pytest.mark.validation\n"
        "def test_explicit_validation_sample():\n"
        "    pass\n"
    )
    automatic = validation / "test_automatic_sample.py"
    automatic.write_text("def test_automatic_validation_sample():\n    pass\n")
    return config, (ordinary, automatic)


def _collected(
    config: Path, selectors: tuple[Path, ...], marker: str | None
) -> frozenset[str]:
    command = [
        sys.executable,
        "-m",
        "pytest",
        "-c",
        str(config),
        "-p",
        "tests.conftest",
        "--collect-only",
        "-q",
    ]
    if marker is not None:
        command.extend(("-m", marker))
    command.extend(str(path) for path in selectors)
    completed = subprocess.run(
        command,
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
        timeout=30,
        env=pytest_environment(),
    )
    assert completed.returncode == 0, completed.stdout + completed.stderr
    return frozenset(
        line.rsplit("::", 1)[-1]
        for line in completed.stdout.splitlines()
        if "::test_" in line
    )


def test_configured_partitions_and_release_collection_preserve_every_case(
    tmp_path: Path,
) -> None:
    config, selectors = _temporary_suite(tmp_path)
    unit = "test_unit_sample"
    explicit = "test_explicit_validation_sample"
    automatic = "test_automatic_validation_sample"
    assert _collected(config, selectors, None) == {unit}
    assert _collected(config, selectors, "validation") == {explicit, automatic}
    assert _collected(config, selectors, "") == {unit, explicit, automatic}
    assert {
        node.rsplit("::", 1)[-1] for node in collect_required(tmp_path, ("tests",))
    } == {unit, explicit, automatic}

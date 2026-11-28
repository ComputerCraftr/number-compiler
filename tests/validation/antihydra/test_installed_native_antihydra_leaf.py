"""Validate the native arithmetic receipt through an installed native wheel."""

import os
import subprocess
from pathlib import Path

import pytest

pytestmark = pytest.mark.validation


def test_installed_antihydra_leaf_replaces_only_the_admitted_scalar_fold() -> None:
    interpreter = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if interpreter is None:
        pytest.skip("requires an installed native CF wheel")
    fixture = Path(__file__).with_name("native_antihydra_leaf_fixture.py")
    run = subprocess.run(
        (interpreter, "-I", str(fixture)), capture_output=True, text=True
    )
    assert run.returncode == 0, run.stderr
    assert "native calls" in run.stdout

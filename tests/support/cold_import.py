"""Check a public module's lazy imports in a fresh Python interpreter."""

import os
import subprocess
import sys
from importlib import import_module
from pathlib import Path

_SOURCE = Path(__file__).resolve().parents[2] / "src"


def assert_import_stays_lazy(module: str, *excluded: str) -> None:
    # A subprocess does not inherit pytest's checkout source path.
    result = subprocess.run(
        (sys.executable, str(Path(__file__)), module, *excluded),
        capture_output=True,
        text=True,
        env={**os.environ, "PYTHONPATH": str(_SOURCE)},
    )
    assert result.returncode == 0, result.stderr


if __name__ == "__main__":
    selected = import_module(sys.argv[1])
    if selected.__file__ is None or not Path(
        selected.__file__
    ).resolve().is_relative_to(_SOURCE):
        raise AssertionError(f"{sys.argv[1]} did not load from {_SOURCE}")
    unexpected = set(sys.argv[2:]).intersection(sys.modules)
    if unexpected:
        raise AssertionError(f"{sys.argv[1]} imported {sorted(unexpected)}")

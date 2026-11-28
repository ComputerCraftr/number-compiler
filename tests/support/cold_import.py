"""Check a public module's lazy imports in a fresh Python interpreter."""

import subprocess
import sys
from importlib import import_module
from pathlib import Path


def assert_import_stays_lazy(module: str, *excluded: str) -> None:
    result = subprocess.run(
        (sys.executable, str(Path(__file__)), module, *excluded),
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stderr


if __name__ == "__main__":
    import_module(sys.argv[1])
    unexpected = set(sys.argv[2:]).intersection(sys.modules)
    if unexpected:
        raise AssertionError(f"{sys.argv[1]} imported {sorted(unexpected)}")

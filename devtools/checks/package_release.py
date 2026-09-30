"""Build and check a wheel from clean staging, with metadata-derived filenames."""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from devtools.checks.installed_distribution import verify_wheel
from devtools.paths import report_directory, repository_root
from devtools.runs import run_reported


def main() -> int:
    argparse.ArgumentParser(description=__doc__).parse_args()
    root = repository_root()
    output = report_directory("devtools.checks.package_release")
    with tempfile.TemporaryDirectory(prefix="number-compiler-package-") as directory:
        staging = Path(directory)
        for name in ("pyproject.toml", "README.md", "LICENSE"):
            shutil.copy2(root / name, staging / name)
        shutil.copytree(
            root / "src",
            staging / "src",
            ignore=shutil.ignore_patterns("__pycache__", "*.egg-info", ".DS_Store"),
        )
        subprocess.run(
            (
                sys.executable,
                "-m",
                "pip",
                "wheel",
                "--no-deps",
                "--wheel-dir",
                str(output),
                str(staging),
            ),
            check=True,
        )
    wheels = tuple(output.glob("*.whl"))
    if len(wheels) != 1:
        raise ValueError("clean staging must produce exactly one wheel")
    result = verify_wheel(wheels[0])
    (output / "verification.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result))
    return 0


if __name__ == "__main__":
    raise SystemExit(run_reported(main))

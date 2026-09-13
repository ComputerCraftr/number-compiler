"""Validate a built wheel in an isolated environment outside the source checkout."""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
import zipfile
from pathlib import Path


def validate_wheel_contents(wheel: Path, source: Path) -> list[str]:
    """Reject stale build products and missing or changed package resources."""
    expected = {
        path.relative_to(source).as_posix(): path
        for path in (source / "number_compiler").rglob("*")
        if path.is_file()
        and "__pycache__" not in path.parts
        and path.name != ".DS_Store"
    }
    with zipfile.ZipFile(wheel) as archive:
        members = archive.namelist()
        packaged = {
            name
            for name in members
            if name.startswith("number_compiler/") and not name.endswith("/")
        }
        if packaged != set(expected):
            raise ValueError(
                {
                    "extra_package_files": sorted(packaged - expected.keys()),
                    "missing_package_files": sorted(expected.keys() - packaged),
                }
            )
        for name, path in expected.items():
            if archive.read(name) != path.read_bytes():
                raise ValueError(f"wheel contains stale package content: {name}")
    return members


def verify_wheel(wheel: Path) -> dict[str, object]:
    """Check package contents, resource admission, public imports, and the CLI."""
    wheel = wheel.resolve(strict=True)
    from devtools.paths import repository_root

    members = validate_wheel_contents(wheel, repository_root() / "src")
    if any(
        name.startswith(("devtools/", "tests/", "research/", "bench/"))
        for name in members
    ):
        raise ValueError("developer packages leaked into the installed distribution")
    if "number_compiler/py.typed" not in members:
        raise ValueError("installed distribution has no typing marker")
    resources = [
        name
        for name in members
        if name.startswith("number_compiler/kernels/") and name.endswith(".zlib")
    ]
    if not resources:
        raise ValueError("installed distribution has no immutable kernel resources")
    environment = dict(os.environ)
    environment.pop("PYTHONPATH", None)
    environment.pop("MYPYPATH", None)
    with tempfile.TemporaryDirectory(
        prefix="number-compiler-wheel-check-"
    ) as directory:
        work = Path(directory)
        venv = work / "environment"
        subprocess.run(
            [sys.executable, "-m", "venv", str(venv)],
            check=True,
            env=environment,
            capture_output=True,
            text=True,
        )
        python = venv / ("Scripts/python.exe" if os.name == "nt" else "bin/python")
        subprocess.run(
            [
                str(python),
                "-m",
                "pip",
                "install",
                "--no-deps",
                "--no-index",
                str(wheel),
            ],
            cwd=work,
            env=environment,
            check=True,
            capture_output=True,
            text=True,
        )
        smoke = subprocess.run(
            [
                str(python),
                "-I",
                "-c",
                """
import json
import sys
from importlib.util import find_spec
from importlib.resources import files
import number_compiler as api
from number_compiler.arithmetic.contracts.physical_collatz_kernel import PhysicalCollatzFourBlockEffect
assert all(hasattr(api, name) for name in api.__all__)
assert not hasattr(api, 'ComposedBlockEffect')
assert api.ReverseAddPoweredTerm(196, 0).digit(0) == 6
kernel = PhysicalCollatzFourBlockEffect()
assert kernel.left_count > 0 and kernel.right_count > 0
for removed in ('classical_ceiling', 'digit_power'):
    assert find_spec('number_compiler.sequences.power_numbers.' + removed) is None
assert not any(name == 'devtools' or name.startswith('devtools.') for name in sys.modules)
print(json.dumps({'public_exports': len(api.__all__), 'kernel_left_states': kernel.left_count, 'kernel_right_states': kernel.right_count, 'installed_path': api.__file__}))
""",
            ],
            cwd=work,
            env=environment,
            check=True,
            capture_output=True,
            text=True,
        )
        cli = subprocess.run(
            [
                str(python),
                "-I",
                "-m",
                "number_compiler",
                "nth",
                "prime",
                "0",
                "--format",
                "json",
            ],
            cwd=work,
            env=environment,
            check=True,
            capture_output=True,
            text=True,
        )
        result: object = json.loads(cli.stdout)
        if not isinstance(result, dict) or result.get("value") != "2":
            raise ValueError("installed CLI returned another prime result")
        factor_cli = subprocess.run(
            [
                str(python), "-I", "-m", "number_compiler", "classify",
                "mersenne", "11", "--factor", "--format", "json",
            ],
            cwd=work,
            env=environment,
            check=True,
            capture_output=True,
            text=True,
        )
        factor: object = json.loads(factor_cli.stdout)
        if (
            not isinstance(factor, dict)
            or factor.get("status") != "composite"
            or factor.get("factor_witness") != 23
        ):
            raise ValueError("installed CLI did not print the checked M11 factor")
        return {
            "wheel": wheel.name,
            "kernel_resources": resources,
            "smoke": json.loads(smoke.stdout),
            "cli_value": "2",
            "cli_m11_factor": 23,
        }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("wheel", type=Path)
    args = parser.parse_args()
    print(json.dumps(verify_wheel(args.wheel), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

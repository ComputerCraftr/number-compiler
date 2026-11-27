"""Source-checked two-tick interiors retain their physical boundary cones."""

from __future__ import annotations

import json
import os
import subprocess

import pytest

pytestmark = pytest.mark.validation


def _literal(seed: str, multiplier: int, ticks: int) -> str:
    value = int(seed)
    for _ in range(ticks):
        value = multiplier * int(str(value)[::-1])
    return str(value)


@pytest.mark.parametrize("multiplier", (2, 5))
@pytest.mark.parametrize("ticks", (128, 129))
def test_checked_relative_interior_and_mutated_halo(
    multiplier: int, ticks: int
) -> None:
    native = pytest.importorskip("number_compiler.kernels._reverse_quotients")
    motif = "0333329666667"
    if multiplier == 5:
        motif = motif[::-1]
    source = "17" + motif * 94 + "88"
    center = len(source) // 2
    mutant = source[:center] + "5" + source[center + 1 :]
    result, work = native.multiply(source, multiplier, ticks, 3)
    changed, changed_work = native.multiply(mutant, multiplier, ticks, 3)
    assert result == _literal(source, multiplier, ticks)
    assert changed == _literal(mutant, multiplier, ticks)
    assert work[0] < changed_work[0]
    assert work[2] == work[3] == 0


@pytest.mark.parametrize("prefix", (1, 137, 611))
def test_relative_return_is_found_after_nonmatching_prefix(prefix: int) -> None:
    native = pytest.importorskip("number_compiler.kernels._reverse_quotients")
    motif = "0333329666667"
    source = "17" + "5" * prefix + motif * 94 + "88"
    result, work = native.multiply(source, 2, 128, 3)
    assert result == _literal(source, 2, 128)
    assert work[0] < 14000


def test_installed_cli_enters_the_checked_relative_endpoint() -> None:
    python = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if not python:
        pytest.skip("set NUMBER_COMPILER_INSTALLED_PYTHON to the native wheel venv")
    assert os.path.isabs(python)
    program = """\
import pathlib, sys, sysconfig
import number_compiler
from number_compiler.kernels import _reflected_multiply as native
from number_compiler.api.cli import main
roots = [pathlib.Path(sysconfig.get_path(key)).resolve() for key in ('purelib', 'platlib')]
for module in (number_compiler, native):
    assert any(pathlib.Path(module.__file__).resolve().is_relative_to(root) for root in roots)
calls = []
def profile(frame, event, arg):
    if event == 'c_call' and arg is native.multiply:
        calls.append(1)
sys.setprofile(profile)
try: status = main(sys.argv[1:])
finally: sys.setprofile(None)
print('NATIVE_C_CALLS',len(calls),file=sys.stderr)
raise SystemExit(status)
"""
    source = "17" + "0333329666667" * 90 + "88"
    env = dict(os.environ, NUMBER_COMPILER_ENABLE_REFLECTED_MULTIPLY="1")
    result = subprocess.run(
        [
            python,
            "-I",
            "-c",
            program,
            "2rev10",
            "--seed",
            source,
            "--nth",
            "128",
            "--max-steps",
            "128",
            "--max-state-bits",
            "8192",
            "--max-output-bits",
            "8192",
            "--format",
            "json",
        ],
        check=True,
        capture_output=True,
        text=True,
        env=env,
    )
    assert int(result.stderr.strip().split("NATIVE_C_CALLS ")[-1]) > 0
    assert json.loads(result.stdout)["value"] == _literal(source, 2, 128)

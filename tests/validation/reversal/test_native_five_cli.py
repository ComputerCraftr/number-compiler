"""Check the bounded five-reverse kernel through its installed CLI."""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

pytestmark = pytest.mark.validation


def _literal(seed: int, steps: int) -> int:
    for _ in range(steps):
        seed = 5 * int(str(seed)[::-1])
    return seed


def test_installed_five_reverse_native_and_refused_paths() -> None:
    installed = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if installed is None:
        pytest.importorskip("number_compiler.kernels._reverse_quotients")
    else:
        assert Path(installed).is_absolute() and Path(installed).is_file()
    program = """\
import pathlib,sys,sysconfig
import number_compiler
from number_compiler.kernels import _reverse_quotients as native
if sys.argv.pop(1) == 'installed':
    roots = [pathlib.Path(sysconfig.get_path(key)).resolve() for key in ('purelib', 'platlib')]
    for path in (number_compiler.__file__, native.__file__):
        assert path is not None and any(pathlib.Path(path).resolve().is_relative_to(root) for root in roots)
from number_compiler.api.cli import main
calls=[]
def profile(frame,event,arg):
    if event == 'c_call' and arg is native.multiply:
        calls.append(1)
sys.setprofile(profile)
try:
    status=main(sys.argv[1:])
finally:
    sys.setprofile(None)
print('NATIVE_C_CALLS',len(calls),file=sys.stderr)
raise SystemExit(status)
"""
    results: dict[str, subprocess.CompletedProcess[str]] = {}
    for label, enabled, seed, ticks, bits in (
        ("native", True, 73, 1024, 8192),
        ("fallback", False, 73, 1024, 8192),
        ("short", True, 73, 16, 8192),
        ("bounded_fallback", True, 73, 512, 512),
        ("native_odd", True, 30, 513, 8192),
        ("refused", True, 6, 512, 4),
        ("refused_fallback", False, 6, 512, 4),
    ):
        env = dict(os.environ)
        env.pop("NUMBER_COMPILER_ENABLE_NATIVE_REVERSE", None)
        if enabled:
            env["NUMBER_COMPILER_ENABLE_NATIVE_REVERSE"] = "1"
        command = [
            installed or sys.executable,
            *(["-I"] if installed else []),
            "-c",
            program,
            "installed" if installed else "source",
            "5rev10",
            "--seed",
            str(seed),
            "--nth",
            str(ticks),
            "--max-steps",
            str(ticks),
            "--max-state-bits",
            str(bits),
            "--max-output-bits",
            "8192",
            "--format",
            "json",
        ]
        result = subprocess.run(command, capture_output=True, text=True, env=env)
        calls = int(result.stderr.strip().split("NATIVE_C_CALLS ")[-1])
        assert (calls > 0) == label.startswith("native")
        if label.startswith("refused"):
            assert result.returncode != 0
        else:
            assert result.returncode == 0
            assert json.loads(result.stdout)["value"] == str(_literal(seed, ticks))
        results[label] = result
    assert results["native"].stdout == results["fallback"].stdout
    assert results["refused"].returncode == results["refused_fallback"].returncode

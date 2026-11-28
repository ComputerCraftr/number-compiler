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
    fixture = Path(__file__).with_name("installed_native_cli_fixture.py")
    results: dict[str, subprocess.CompletedProcess[str]] = {}
    for label, enabled, seed, ticks, bits in (
        ("native", True, 73, 1024, 8192),
        ("fallback", False, 73, 1024, 8192),
        ("short", True, 73, 16, 8192),
        ("prethreshold", True, 73, 63, 8192),
        ("native_short", True, 73, 64, 8192),
        ("native_short_fallback", False, 73, 64, 8192),
        ("native_middle", True, 73, 96, 8192),
        ("native_before_old_threshold", True, 73, 127, 8192),
        ("native_short_wide", True, int("123456789" * 17), 64, 8192),
        ("unmeasured_width", True, 1 << 512, 64, 8192),
        ("bounded_short_fallback", True, 73, 64, 128),
        ("zero_short", True, 0, 64, 8192),
        ("native_threshold", True, 73, 128, 8192),
        ("native_wide", True, int("123456789" * 17), 128, 8192),
        ("bounded_fallback", True, 73, 512, 512),
        ("native_odd", True, 30, 513, 8192),
        ("refused_short", True, 6, 128, 4),
        ("refused_short_fallback", False, 6, 128, 4),
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
            str(fixture),
            "five" if installed else "five-source",
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
        assert (calls > 0) == (
            label.startswith("native") and label != "native_short_fallback"
        )
        if label.startswith("refused"):
            assert result.returncode != 0
        else:
            assert result.returncode == 0
            assert json.loads(result.stdout)["value"] == str(_literal(seed, ticks))
        if label == "native":
            work = json.loads(result.stderr.split("NATIVE_WORK ")[1].splitlines()[0])
            assert work[:6] == [13803, 486, 0, 0, 500, 2000]
        results[label] = result
    assert results["native"].stdout == results["fallback"].stdout
    assert results["native_short"].stdout == results["native_short_fallback"].stdout
    assert results["refused"].returncode == results["refused_fallback"].returncode
    assert (
        results["refused_short"].returncode
        == results["refused_short_fallback"].returncode
    )

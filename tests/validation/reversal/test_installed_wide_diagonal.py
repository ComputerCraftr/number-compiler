"""The wide non-C0 source uses its bounded diagonal through the installed CLI."""

import json
import os
import subprocess
from pathlib import Path

import pytest

pytestmark = pytest.mark.validation

_WIDE = "314159265358979323846264338327950288419716939937510" * 3


@pytest.mark.parametrize(
    ("ticks", "enabled", "expected_calls"),
    [
        (255, True, 0),
        (256, True, 1),
        (257, True, 1),
        (511, True, 1),
        (512, True, 1),
        (513, True, 1),
        (256, False, 0),
    ],
)
def test_installed_wide_diagonal(
    ticks: int, enabled: bool, expected_calls: int
) -> None:
    python = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if python is None:
        pytest.skip("requires the installed native-reverse wheel interpreter")
    assert Path(python).is_absolute()
    env = dict(os.environ, NUMBER_COMPILER_ENABLE_NATIVE_REVERSE=str(int(enabled)))
    proc = subprocess.run(
        [
            python,
            "-I",
            str(Path(__file__).with_name("installed_native_cli_fixture.py")),
            "wide",
            "2rev10",
            "--seed",
            _WIDE,
            "--nth",
            str(ticks),
            "--max-steps",
            str(ticks),
            "--max-state-bits",
            "32768",
            "--max-output-bits",
            "32768",
            "--format",
            "json",
        ],
        env=env,
        check=True,
        capture_output=True,
        text=True,
    )
    value = int(_WIDE)
    for _ in range(ticks):
        value = 2 * int(str(value)[::-1])
    assert json.loads(proc.stdout)["value"] == str(value)
    assert int(proc.stderr) == expected_calls

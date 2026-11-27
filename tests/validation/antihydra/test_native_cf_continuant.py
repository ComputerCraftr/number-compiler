"""The bounded native continuant preserves the issued row and every clip."""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

pytestmark = pytest.mark.validation


def test_installed_native_continuant_cylinder_and_fallback() -> None:
    installed = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if installed is None:
        pytest.importorskip("number_compiler.kernels._cf_continuant")
    else:
        assert Path(installed).is_absolute() and Path(installed).is_file()
    program = """\
import pathlib,sys,sysconfig
import number_compiler
from number_compiler.kernels import _cf_continuant as native
if sys.argv.pop(1) == 'installed':
    roots=[pathlib.Path(sysconfig.get_path(key)).resolve() for key in ('purelib','platlib')]
    for path in (number_compiler.__file__,native.__file__):
        assert path is not None and any(pathlib.Path(path).resolve().is_relative_to(root) for root in roots)
from number_compiler.api.cli import main
calls=[]
def trace(frame,event,arg):
    if event == 'c_call' and arg is native.ordered_product:calls.append(1)
sys.setprofile(trace)
try:status=main(sys.argv[1:])
finally:sys.setprofile(None)
print('NATIVE_C_CALLS',len(calls),file=sys.stderr)
raise SystemExit(status)
"""
    results: dict[str, subprocess.CompletedProcess[str]] = {}
    for label, enabled, horizon in (
        ("native", True, 4096),
        ("fallback", False, 4096),
        ("short", True, 63),
    ):
        env = dict(os.environ)
        env["NUMBER_COMPILER_ENABLE_CF_RECIPROCAL"] = "1"
        env.pop("NUMBER_COMPILER_ENABLE_CF_CONTINUANT", None)
        if enabled:
            env["NUMBER_COMPILER_ENABLE_CF_CONTINUANT"] = "1"
        cmd = [
            installed or sys.executable,
            *(["-I"] if installed else []),
            "-c",
            program,
            "installed" if installed else "source",
            "antihydra",
            "--nth",
            "0",
            "--no-value",
            "--format",
            "json",
            "--info",
            "arithmetic.continued-fraction",
            "--safety-horizon",
            str(horizon),
        ]
        result = subprocess.run(
            cmd, capture_output=True, text=True, env=env, check=True
        )
        calls = int(result.stderr.strip().split("NATIVE_C_CALLS ")[-1])
        assert (calls > 0) == (label == "native")
        value = json.loads(result.stdout)["info"]["arithmetic.continued-fraction"]
        assert value["status"] == "available"
        count = value["coefficient_count"]
        if horizon == 4096:
            assert count == 540
        digits = "".join(str(5**power) for power in range(1, 60))[:count]
        entries = (1, 0, 0, 1)
        for digit in digits:
            a, b, c, d = entries
            coefficient = int(digit) + 1
            entries = (
                a * coefficient + b,
                a,
                c * coefficient + d,
                c,
            )
        assert value["matrix"] == [list(entries[:2]), list(entries[2:])]
        results[label] = result
    assert results["native"].stdout == results["fallback"].stdout


def test_native_word_alphabet_and_leading_zero_clips() -> None:
    installed = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if installed is None:
        pytest.importorskip("number_compiler.kernels._cf_continuant")
    program = """\
import random
from number_compiler.kernels._cf_continuant import ordered_product
from number_compiler.arithmetic.fields.ordered_matrix import append_decimal_value
rng = random.Random(43)
for width in range(1,17):
    values = [0,1,10**width-1] + [rng.randrange(10**width) for _ in range(100)]
    if width == 2: values.extend(range(100))
    for value in values:
        assert ordered_product(value,width) == append_decimal_value(value,10**(width-1),(1,0,0,1))
for value,width in ((1,0),(1,17),(100,2),(-1,2),(2**64+7,2),(1,-1),(1,2**64+4),(True,2),(1,True)):
    try: ordered_product(value,width)
    except (ValueError, OverflowError, TypeError): pass
    else: raise AssertionError((value,width))

import os
os.environ['NUMBER_COMPILER_ENABLE_CF_CONTINUANT']='1'
from number_compiler.sequences.antihydra.mahler_cf_reciprocal_tile import ReciprocalTile
for q in (10002345, 123456789012):
    rows = [str(q*5**i) for i in range(3)]
    word = ''.join(rows)
    tile = ReciprocalTile(q,tuple(map(len,rows)),0,len(word))
    for begin in range(len(word)):
        for length in range(len(word)-begin+1):
            entries=(1,0,0,1)
            for digit in word[begin:begin+length]:
                a,b,c,d=entries
                k=int(digit)+1
                entries=(a*k+b,a,c*k+d,c)
            assert tile.segment(begin,length).entries == entries
"""
    subprocess.run(
        [installed or sys.executable, *(["-I"] if installed else []), "-c", program],
        check=True,
    )

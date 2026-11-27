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
import os,pathlib,sys,sysconfig
import number_compiler
from number_compiler.kernels import _cf_continuant as native
if sys.argv.pop(1) == 'installed':
    roots=[pathlib.Path(sysconfig.get_path(key)).resolve() for key in ('purelib','platlib')]
    for path in (number_compiler.__file__,native.__file__):
        assert path is not None and any(pathlib.Path(path).resolve().is_relative_to(root) for root in roots)
from number_compiler.api.cli import main
from number_compiler.sequences.antihydra import mahler_cf_reciprocal_tile as tile
calls=[]
banks=[]
paired=[]
indexed=[]
fused=hasattr(native,'indexed_pair')
opens=[]
select=tile.reciprocal_row_interval
def watch(q,t,width,start,count):
    if q==5**38 and t==1:
        opens.append((width,start,count))
        if os.environ.get('NUMBER_COMPILER_ENABLE_CF_CONTINUANT')=='1':
            assert not fused and opens==[(28,0,22)], 'issued head reopened during descent'
    return select(q,t,width,start,count)
tile.reciprocal_row_interval=watch
def trace(frame,event,arg):
    if event == 'c_call' and arg is native.ordered_product:calls.append(1)
    if event == 'c_call' and arg is native.ordered_prefix_bank:banks.append(1)
    if event == 'c_call' and fused:
        if arg is native.settled_four:paired.append(1)
        if arg is native.indexed_pair:indexed.append(1)
sys.setprofile(trace)
try:status=main(sys.argv[1:])
finally:sys.setprofile(None)
print('NATIVE_C_CALLS',len(calls),len(banks),len(opens),len(paired),len(indexed),int(fused),file=sys.stderr)
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
        calls, banks, opens, pairs, indexed, fused = map(
            int, result.stderr.strip().split("NATIVE_C_CALLS ")[-1].split()
        )
        assert (calls > 0) == (label == "native")
        assert banks + indexed == int(label == "native")
        assert pairs == (4 if label == "native" and fused else 0)
        assert indexed == int(label == "native" and fused)
        if label == "native":
            assert opens == 1 - indexed
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
import struct
from number_compiler.kernels._cf_continuant import ordered_prefix_bank, ordered_product
from number_compiler.arithmetic.fields.ordered_matrix import append_decimal_value
rng = random.Random(43)
for width in range(1,17):
    values = [0,1,10**width-1] + [rng.randrange(10**width) for _ in range(100)]
    if width == 2: values.extend(range(100))
    for value in values:
        bank=ordered_prefix_bank(value,width)
        assert type(bank) is bytes and len(bank)==32*(width+1)
        expected=(1,0,0,1)
        for cut,digit in enumerate(str(value).zfill(width)):
            assert struct.unpack_from('=4Q',bank,32*cut)==expected
            a,b,c,d=expected
            x=int(digit)+1
            expected=(a*x+b,a,c*x+d,c)
        assert struct.unpack_from('=4Q',bank,32*width)==expected
        assert ordered_product(value,width) == append_decimal_value(value,10**(width-1),(1,0,0,1))
for fn in (ordered_product,ordered_prefix_bank):
    for bad,width,err in ((1,0,ValueError),(1,17,ValueError),(100,2,ValueError),
                          (-1,1,OverflowError),(2**64+7,2,OverflowError),(1,-1,OverflowError),
                          (1,2**64+4,OverflowError),(True,1,TypeError),(1,True,TypeError)):
        try:
            fn(bad,width)
        except err:
            pass
        else:
            raise AssertionError((fn.__name__,bad,width))

import os
os.environ['NUMBER_COMPILER_ENABLE_CF_CONTINUANT']='1'
from number_compiler.sequences.antihydra.mahler_cf_reciprocal_tile import ReciprocalTile
for width in range(17,33):
    for value in (0,1,10**(width-2)+105,10**width-1):
        source=ReciprocalTile(value,(width,),0,width)
        for begin,end in ((0,width),(1,width),(0,width-1)):
            digits=str(value).zfill(width)[begin:end]
            entries=(1,0,0,1)
            for digit in digits:
                a,b,c,d=entries
                k=int(digit)+1
                entries=(a*k+b,a,c*k+d,c)
            assert source.segment(begin,end-begin).entries == entries
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


def test_native_settled_pairs_phases_carries_and_indexed_clips() -> None:
    installed = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if installed is None:
        pytest.importorskip("number_compiler.kernels._cf_continuant")
    program = """\
import random,struct
from number_compiler.kernels import _cf_continuant as native
if not hasattr(native,'indexed_pair'):
    raise SystemExit(77)
rng=random.Random(640)
def product(word):
    a,b,c,d=1,0,0,1
    for digit in word:
        k=int(digit)+1
        a,b,c,d=a*k+b,a,c*k+d,c
    return a,b,c,d
# Exercise every base-100 carry-table entry through a complete ordered tile.
phases={5*pow(5,i,64)//64:i for i in range(16)}
assert set(phases)==set(range(5))
for phase in phases.values():
    for pair in range(100):
        q=(100+pair)*1000000+15625*pow(5,phase,64)
        words=[str(q*5**i) for i in range(4)]
        got=native.settled_four(q,tuple(map(len,words)),phase)
        assert got==(product(''.join(words[:2])),product(''.join(words[2:])))
for phase in range(16):
    suffix=15625*pow(5,phase,64)
    for width in range(7,17):
        for head in [10**(width-7),10**(width-6)-1,rng.randrange(10**(width-7),10**(width-6))]:
            q=head*1000000+suffix
            words=[str(q*5**i) for i in range(4)]
            widths=tuple(map(len,words))
            if widths[-1]>18:continue
            assert native.settled_four(q,widths,phase)==(product(''.join(words[:2])),product(''.join(words[2:])))
            assert native.settled_four(q,widths,(phase+1)%16) is None
            assert native.settled_four(q,(*widths[:2],widths[2]+1,widths[3]),phase) is None
    for width in range(27,33):
        for _ in range(25):
            q=rng.randrange(10**(width-7),10**(width-6))*1000000+suffix
            first=str(q)
            second=str(5*q)
            w=len(second)
            if not 28<=w<=32:continue
            cut=w//2
            high,low=divmod(q,10**(w-cut))
            a,b,bank=native.indexed_pair(high,low,width,w,phase)
            assert (a,b)==(product(first),product(second))
            for i in range(cut+1):
                assert struct.unpack_from('=4Q',bank,32*i)==product(second[:i])
            assert native.indexed_pair(high,low,width,w,(phase+1)%16) is None
            assert native.indexed_pair(high,low+1,width,w,phase) is None
"""
    result = subprocess.run(
        [installed or sys.executable, *(["-I"] if installed else []), "-c", program],
        check=False,
    )
    if result.returncode == 77:
        pytest.skip(
            "paired emitter requires native unsigned 128-bit arithmetic and CPython 3.13+"
        )
    assert result.returncode == 0


@pytest.mark.parametrize("cap,status", [(539, "unknown"), (540, "available")])
def test_installed_paired_cylinder_cap(cap: int, status: str) -> None:
    installed = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if installed is None:
        pytest.importorskip("number_compiler.kernels._cf_continuant")
    args = [
        installed or sys.executable,
        *(["-I"] if installed else []),
        "-c",
        "from number_compiler.api.cli import main; raise SystemExit(main())",
        "antihydra",
        "--nth",
        "0",
        "--no-value",
        "--format",
        "json",
        "--info",
        "arithmetic.continued-fraction",
        "--safety-horizon",
        "4096",
        "--continued-fraction-max-coefficients",
        str(cap),
    ]
    env = dict(os.environ, NUMBER_COMPILER_ENABLE_CF_RECIPROCAL="1")
    results = [
        subprocess.run(
            args,
            env=dict(env, NUMBER_COMPILER_ENABLE_CF_CONTINUANT=flag),
            check=False,
            capture_output=True,
        )
        for flag in ("0", "1")
    ]
    assert all(result.returncode == (3 if cap == 539 else 0) for result in results)
    assert results[0].stdout == results[1].stdout
    packet = json.loads(results[0].stdout)["info"]["arithmetic.continued-fraction"]
    assert (packet["status"], packet["coefficient_count"]) == (status, cap)

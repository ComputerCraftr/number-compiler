"""A joint physical four-tick Q19 action retains both collars and the clock."""

from __future__ import annotations

import json
import os
import random
import subprocess

import pytest

pytestmark = pytest.mark.validation


def _seed() -> int:
    value = int("1" * 500 + "8" * 500)
    for _ in range(202):
        value += int(str(value)[::-1])
    return value


def _two_birth_seed(index: int = 0) -> int:
    original = str(_seed())
    generator = random.Random(731)
    prefix = suffix = ""
    for _ in range(index + 1):
        prefix = str(generator.randrange(1, 10)) + "".join(
            str(generator.randrange(10)) for _ in range(11)
        )
        suffix = "".join(str(generator.randrange(10)) for _ in range(12))
    return int(prefix + original[12:-12] + suffix)


def _literal(seed: int, ticks: int) -> int:
    for _ in range(ticks):
        seed += int(str(seed)[::-1])
    return seed


def test_installed_cli_enters_joint_action_and_preserves_fallback() -> None:
    interpreter = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if not interpreter:
        pytest.skip("set NUMBER_COMPILER_INSTALLED_PYTHON to the native wheel")
    assert os.path.isabs(interpreter)
    program = """\
import pathlib,sys,sysconfig
import number_compiler
from number_compiler.kernels import _reverse_quotients as native
from number_compiler.api.cli import main
roots=[pathlib.Path(sysconfig.get_path(k)).resolve() for k in ('purelib','platlib')]
for module in (number_compiler,native):
    assert any(pathlib.Path(module.__file__).resolve().is_relative_to(root) for root in roots)
original=native.add_folded_joint4
calls=[]
def wrapped(*args):
    result=original(*args)
    calls.append(result[2])
    return result
native.add_folded_joint4=wrapped
status=main(sys.argv[1:])
print('JOINT_CALLS',len(calls),sum(x[7] for x in calls),sum(x[8] for x in calls),file=sys.stderr)
print('PROBES',sum(x[9] for x in calls),'TWO_BIRTHS',sum(x[13] for x in calls),'ONE_BIRTH',sum(x[14] for x in calls),file=sys.stderr)
raise SystemExit(status)
"""
    seed = _seed()
    outputs: dict[str, subprocess.CompletedProcess[str]] = {}
    for label, enabled, value, ticks in (
        ("joint", True, seed, 1024),
        ("fallback", False, seed, 1024),
        ("two-birth", True, _two_birth_seed(), 1024),
        ("two-birth-fallback", False, _two_birth_seed(), 1024),
        ("two-birth-eq", True, _two_birth_seed(65), 1024),
        ("two-birth-eq-fallback", False, _two_birth_seed(65), 1024),
        ("one-birth", True, _two_birth_seed(18), 1024),
        ("one-birth-fallback", False, _two_birth_seed(18), 1024),
        ("unprotected", True, 196, 1024),
        ("short-collar", True, int("809" * 47), 1024),
        ("short", True, seed, 16),
    ):
        env = dict(os.environ, NUMBER_COMPILER_ENABLE_NATIVE_REVERSE="1")
        env.pop("NUMBER_COMPILER_ENABLE_Q19_JOINT4", None)
        if enabled:
            env["NUMBER_COMPILER_ENABLE_Q19_JOINT4"] = "1"
        result = subprocess.run(
            [
                interpreter,
                "-I",
                "-c",
                program,
                "reverse-add",
                "--seed",
                str(value),
                "--nth",
                str(ticks),
                "--format",
                "json",
            ],
            capture_output=True,
            text=True,
            env=env,
            check=True,
        )
        counts, probes = (
            result.stderr.strip().split("JOINT_CALLS ")[-1].split("PROBES ")
        )
        probe_values, one_birth_value = probes.split("ONE_BIRTH ")
        probe_count, two_birth_count = map(int, probe_values.split("TWO_BIRTHS "))
        one_birth_count = int(one_birth_value)
        parts = counts.split()
        calls, bands, columns = map(int, parts)
        if label in {"joint", "two-birth", "two-birth-eq", "one-birth"}:
            assert calls > 0 and bands > 0 and columns >= 48
        else:
            assert bands == columns == 0
        if label in {"fallback", "short"}:
            assert calls == 0
        if label == "short-collar":
            assert calls == 1 and 0 < probe_count <= 10
        assert two_birth_count == (
            1 if label in {"two-birth", "two-birth-eq", "one-birth"} else 0
        )
        assert one_birth_count == (1 if label == "one-birth" else 0)
        assert json.loads(result.stdout)["value"] == str(_literal(value, ticks))
        outputs[label] = result
    assert outputs["joint"].stdout == outputs["fallback"].stdout
    assert outputs["two-birth"].stdout == outputs["two-birth-fallback"].stdout
    assert outputs["two-birth-eq"].stdout == outputs["two-birth-eq-fallback"].stdout
    assert outputs["one-birth"].stdout == outputs["one-birth-fallback"].stdout


def test_joint_native_both_clocks_and_rejected_eq_core() -> None:
    interpreter = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if not interpreter:
        pytest.skip("set NUMBER_COMPILER_INSTALLED_PYTHON to the native wheel")
    program = """\
import random
from number_compiler.kernels import _reverse_quotients as native
random_source=random.Random(196)
clocks=set()
for i in range(100):
    half=bytes([18]+[random_source.randrange(19) for _ in range(i%5)] +
               [random_source.choice((8,17,18)) for _ in range(100+i%31)] +
               [random_source.randrange(19) for _ in range(i%20)])
    center=-1 if i%2==0 else i%10
    low=[min(s,9) for s in half]
    high=[s-d for s,d in zip(half,low)]
    source=int(''.join(map(str,high))+('' if center<0 else str(center))+''.join(map(str,reversed(low))))
    for ticks in (4,5,17):
        base=native.add_folded(half,center,ticks,4<<20)
        result=native.add_folded_joint4(half,center,ticks,4<<20)
        assert result[:2]==base[:2]
        assert result[2][7]==1 and result[2][8]>=48
        if ticks==4:
            assert result[2][0]==result[2][2]==result[2][3]==0
        assert result[2][11]+result[2][12]==1
        value=source
        clock=0
        for step in range(ticks):
            nxt=value+int(str(value)[::-1])
            if step<4: clock|=(len(str(nxt))-len(str(value)))<<step
            value=nxt
        digits=str(value)
        physical=bytes(int(a)+int(b) for a,b in zip(digits,digits[::-1]))
        actual=result[0]+(b'' if result[1]<0 else bytes([2*result[1]]))+result[0][::-1]
        assert actual==physical and clock in (7,13)
        assert (result[2][11],result[2][12]) == ((1,0) if clock==13 else (0,1))
        clocks.add(clock)
assert clocks=={7,13}
for size in (64,65,101,127,128):
    half=bytes([18]+[9]*(size-1))
    refused=native.add_folded_joint4(half,-1,4,4<<20)
    assert refused[:2]==native.add_folded(half,-1,4,4<<20)[:2]
    assert refused[2][7]==0 and refused[2][9]==size-64
for padding in (0,8,126,127):
    half=bytes([18]+[9]*padding+[17]*64)
    result=native.add_folded_joint4(half,-1,4,4<<20)
    assert result[:2]==native.add_folded(half,-1,4,4<<20)[:2]
    assert result[2][7:9]==((1,48) if padding<127 else (0,0))
"""
    subprocess.run([interpreter, "-I", "-c", program], check=True)


def test_joint_refuses_finite_ledger_before_opening_source(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.carry.native_reverse_actions import (
        PairWork,
        native_folded_pair_action,
    )
    from number_compiler.resources.ledger import ResourceLedger

    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_Q19_JOINT4", "1")
    ledger = ResourceLedger(max_nodes=128)
    owner = ledger.register("joint refusal", "scratch")

    def source() -> bytes:
        pytest.fail("a refused joint source was opened")

    def receive(_pairs: bytes, _center: int | None, _work: PairWork) -> None:
        pytest.fail("a refused joint endpoint was published")

    try:
        assert (
            native_folded_pair_action(
                ledger, owner, source, None, 512, receive, source_width=256
            )
            is None
        )
        assert ledger.nodes == ledger.entries == 0
    finally:
        ledger.mark_disposed(owner)


def test_joint_action_warm_publication_reuses_completed_result() -> None:
    interpreter = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if not interpreter:
        pytest.skip("set NUMBER_COMPILER_INSTALLED_PYTHON to the native wheel")
    program = """\
import os
os.environ['NUMBER_COMPILER_ENABLE_NATIVE_REVERSE']='1'
os.environ['NUMBER_COMPILER_ENABLE_Q19_JOINT4']='1'
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.q19_output import ReversePairQ19OutputOwner
from number_compiler.arithmetic.carry import native_reverse_actions
value=int('1'*500+'8'*500)
for _ in range(202):value+=int(str(value)[::-1])
ledger=ResourceLedger()
owner=ReversePairQ19OutputOwner(ledger,tuple(map(int,reversed(str(value)))),base=10)
try:
    first=owner.publish_carry_window_continuation(1024,shared_cache=False)
    assert ledger.counters['native_pair_joint_bands']>=1
    def refuse(*args,**kwargs):raise AssertionError('completed endpoint rebuilt')
    native_reverse_actions.native_folded_pair_action=refuse
    assert owner.publish_carry_window_continuation(1024,shared_cache=False)==first
finally:
    owner.dispose()
assert ledger.nodes==ledger.entries==0
"""
    subprocess.run([interpreter, "-I", "-c", program], check=True)


@pytest.mark.parametrize(
    "fault",
    [
        "missing_clock",
        "short_core",
        "negative_clock",
        "negative_one_birth",
        "residual_birth",
    ],
)
def test_joint_rejects_forged_work_receipt_before_publication(
    fault: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    from number_compiler.arithmetic.carry import native_reverse_actions as actions
    from number_compiler.resources.ledger import ResourceLedger

    class Native:
        @staticmethod
        def add_folded(*_args: object) -> None:
            pytest.fail("joint test fell back before checking the receipt")

        @staticmethod
        def add_folded_joint4(*_args: object) -> tuple[bytes, int, tuple[int, ...]]:
            columns = 47 if fault == "short_core" else 48
            clock = 0 if fault == "missing_clock" else 1
            if fault == "negative_clock":
                return (
                    bytes([18] * 129),
                    0,
                    (0, 1, 0, 0, 3, 0, 0, 1, 48, 64, 0, -1, 2, 0),
                )
            if fault == "negative_one_birth":
                return (
                    bytes([18] * 129),
                    0,
                    (0, 1, 0, 0, 3, 0, 0, 1, 48, 64, 0, 0, 0, 2, -1),
                )
            if fault == "residual_birth":
                return (
                    bytes([18] * 256),
                    0,
                    (0, 128, 0, 0, 257, 0, 0, 128, 6144, 8192, 0, 0, 0, 128),
                )
            return (
                bytes([18] * 129),
                0,
                (0, 1, 0, 0, 3, 0, 0, 1, columns, 64, 0, clock, 0),
            )

    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_Q19_JOINT4", "1")
    monkeypatch.setattr(actions, "_load", lambda: Native())
    ledger = ResourceLedger()
    owner = ledger.register("forged joint receipt", "scratch")

    def receive(_half: bytes, _center: int | None, _work: actions.PairWork) -> None:
        pytest.fail("a forged joint receipt reached publication")

    try:
        with pytest.raises(RuntimeError, match="invalid native folded causal endpoint"):
            actions.native_folded_pair_action(
                ledger,
                owner,
                lambda: bytes([18] * 128),
                None,
                512,
                receive,
                source_width=256,
            )
        assert ledger.nodes == ledger.entries == 0
    finally:
        ledger.mark_disposed(owner)


def test_two_birth_slabs_match_physical_rows_and_mixed_receipts() -> None:
    interpreter = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if not interpreter:
        pytest.skip("set NUMBER_COMPILER_INSTALLED_PYTHON to the native wheel")
    program = """\
from collections import Counter
from random import Random
from number_compiler.kernels import _reverse_quotients as native
r=Random(4095)
clocks=Counter()
for j in range(500):
    half=bytes([r.randrange(10,19)]+[r.randrange(19) for _ in range(j%14)]+
               [r.choice((8,17,18)) for _ in range(96+j%29)]+
               [r.randrange(19) for _ in range(j%13)])
    center=-1 if j%2==0 else j%10
    low=[max(x-9,0) for x in half]
    high=[x-y for x,y in zip(half,low)]
    value=int(''.join(map(str,high))+('' if center<0 else str(center))+
              ''.join(map(str,reversed(low))))
    for ticks in (4,5,17):
        got=native.add_folded_joint4(half,center,ticks,4<<20)
        assert got[:2]==native.add_folded(half,center,ticks,4<<20)[:2]
        v=value
        clock=0
        births=0
        for k in range(ticks):
            after=v+int(str(v)[::-1])
            birth=len(str(after))-len(str(v))
            births+=birth
            if k<4: clock|=birth<<k
            v=after
        digits=str(v)
        physical=bytes(int(a)+int(b) for a,b in zip(digits,digits[::-1]))
        produced=got[0]+(b'' if got[1]<0 else bytes([2*got[1]]))+got[0][::-1]
        assert physical==produced and got[2][4]==births
        if got[2][7]: clocks[clock]+=1
assert clocks[1]>0 and clocks[5]>0 and clocks[9]>0
# Two source-admitted two-birth slabs followed by the exact continuation.
half=bytes([13,17,18,3,6,12,6,4,4]+[18]*100)
result=native.add_folded_joint4(half,-1,16,4<<20)
assert result[:2]==native.add_folded(half,-1,16,4<<20)[:2]
assert result[2][7]==result[2][13]==2 and result[2][4]==7
# The exterior is not an unconditional admission. A first-tick no-birth
# source must use the exact continuation.
for outer in range(1,9):
    got=native.add_folded_joint4(bytes([outer]+[18]*100),-1,4,4<<20)
    assert got[2][7]==0
# The first physical carry can also be issued by an EQ exterior when its
# checked inward carry is one. This fixture has the 1100 clock.
half=bytes([9,14,2,4,11,0,17,8,17,18,17,17,17,8]+[18]*100)
for center in (-1, 3):
    got=native.add_folded_joint4(half,center,4,4<<20)
    assert got[:2]==native.add_folded(half,center,4,4<<20)[:2]
    assert got[2][7]==got[2][13]==1
    low=[max(x-9,0) for x in half]
    high=[x-y for x,y in zip(half,low)]
    value=int(''.join(map(str,high))+('' if center<0 else str(center))+
              ''.join(map(str,reversed(low))))
    clock=0
    for k in range(4):
        after=value+int(str(value)[::-1])
        clock|=(len(str(after))-len(str(value)))<<k
        value=after
    assert clock==3
    digits=str(value)
    assert bytes(int(a)+int(b) for a,b in zip(digits,digits[::-1])) == (
        got[0]+(b'' if got[1]<0 else bytes([2*got[1]]))+got[0][::-1]
    )
"""
    subprocess.run([interpreter, "-I", "-c", program], check=True)


def test_one_birth_slab_uses_physical_collars_and_center() -> None:
    interpreter = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if not interpreter:
        pytest.skip("set NUMBER_COMPILER_INSTALLED_PYTHON to the native wheel")
    program = """\\
import sys
from number_compiler.kernels import _reverse_quotients as native

source=int(sys.argv[1])
for _ in range(12): source+=int(str(source)[::-1])
digits=str(source)
half=bytes(int(a)+int(b) for a,b in zip(digits[:len(digits)//2],reversed(digits)))
for center in (-1, 4):
    low=[max(x-9,0) for x in half]
    high=[x-y for x,y in zip(half,low)]
    value=int(''.join(map(str,high))+('' if center<0 else str(center))+
              ''.join(map(str,reversed(low))))
    got=native.add_folded_joint4(half,center,4,4<<20)
    assert got[:2]==native.add_folded(half,center,4,4<<20)[:2]
    assert got[2][7]==got[2][14]==1 and got[2][8]>=48
    clock=0
    for k in range(4):
        after=value+int(str(value)[::-1])
        clock|=(len(str(after))-len(str(value)))<<k
        value=after
    assert clock==1
    output=str(value)
    assert bytes(int(a)+int(b) for a,b in zip(output,output[::-1]))==(
        got[0]+(b'' if got[1]<0 else bytes([2*got[1]]))+got[0][::-1])
    broken=bytearray(half)
    for i in range(90,len(broken)): broken[i]=9
    rejected=native.add_folded_joint4(bytes(broken),center,4,4<<20)
    assert rejected[2][7]==0
    assert rejected[:2]==native.add_folded(bytes(broken),center,4,4<<20)[:2]

"""
    subprocess.run(
        [interpreter, "-I", "-c", program, str(_two_birth_seed(18))], check=True
    )


def test_installed_seed196_uses_four_tick_action_with_exact_fallback() -> None:
    interpreter = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if not interpreter:
        pytest.skip("set NUMBER_COMPILER_INSTALLED_PYTHON to the native wheel")
    program = """\
import json,sys
from number_compiler.api.cli import main
from number_compiler.kernels import _reverse_quotients as native
calls=[]
original=native.add_folded
def checked(*args):
    result=original(*args)
    calls.append(result[2])
    return result
native.add_folded=checked
status=main(sys.argv[1:])
print("Q19_RECEIPTS",json.dumps(calls),file=sys.stderr)
raise SystemExit(status)
"""
    for seed, ticks in (
        (196, 511),
        (196, 1024),
        (196, 2048),
        (196, 4096),
        (73, 1024),
        (0, 1024),
    ):
        packets: list[object] = []
        for enabled in (False, True):
            env = dict(os.environ)
            env.pop("NUMBER_COMPILER_ENABLE_NATIVE_REVERSE", None)
            env.pop("NUMBER_COMPILER_ENABLE_Q19_JOINT4", None)
            if enabled:
                env["NUMBER_COMPILER_ENABLE_NATIVE_REVERSE"] = "1"
            proc = subprocess.run(
                [
                    interpreter,
                    "-I",
                    "-c",
                    program,
                    "reverse-add",
                    "--seed",
                    str(seed),
                    "--nth",
                    str(ticks),
                    "--format",
                    "json",
                    "--max-output-bits",
                    "10000",
                ],
                env=env,
                capture_output=True,
                text=True,
                check=True,
            )
            packet = json.loads(proc.stdout)
            assert packet["value"] == str(_literal(seed, ticks))
            receipts = json.loads(proc.stderr.removeprefix("Q19_RECEIPTS ").strip())
            packets.append(packet)
            if not enabled or ticks < 512 or seed == 0:
                assert not receipts
            else:
                assert len(receipts) == 1
                attempts, actions, cores, refused, converted, peak = receipts[0][19:25]
                assert actions > 0 and cores >= actions
                assert attempts == actions + refused
                assert converted > 0 and peak > 0
        assert packets[0] == packets[1]


def test_four_tick_carries_match_literal_width_and_center_transitions() -> None:
    interpreter = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if not interpreter:
        pytest.skip("set NUMBER_COMPILER_INSTALLED_PYTHON to the native wheel")
    program = """\
import random
from number_compiler.kernels import _reverse_quotients as native
r=random.Random(11319)
admitted=refused=0
for width in (64,65,95,96,127,128,129,160,193):
    for case in range(40):
        values=bytes([r.randrange(1,19)]+[r.randrange(19) for _ in range(width//2-1)])
        center=r.randrange(10) if width%2 else -1
        high=[min(s,9) for s in values]
        low=[s-d for s,d in zip(values,high)]
        source=int(''.join(map(str,high))+('' if center<0 else str(center))+''.join(map(str,reversed(low))))
        for ticks in (4,5,9,16):
            result=native.add_folded(values,center,ticks,4<<20)
            number=source
            for _ in range(ticks):
                number+=int(str(number)[::-1])
            digits=str(number)
            physical=bytes(int(a)+int(b) for a,b in zip(digits,digits[::-1]))
            got=result[0]+(b'' if result[1]<0 else bytes([2*result[1]]))+result[0][::-1]
            assert physical==got,(width,case,ticks)
            attempts,actions,tiles,declined,_,_=result[2][19:25]
            assert attempts==actions+declined
            assert tiles>=actions
            admitted+=actions
            refused+=declined
assert admitted>0 and refused>0
"""
    subprocess.run([interpreter, "-I", "-c", program], check=True)


def test_four_tick_failed_publication_releases_native_reservation() -> None:
    interpreter = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if not interpreter:
        pytest.skip("set NUMBER_COMPILER_INSTALLED_PYTHON to the native wheel")
    program = """\
from number_compiler.arithmetic.carry.native_reverse_actions import native_folded_pair_action
from number_compiler.resources.ledger import ResourceLedger

ledger=ResourceLedger()
owner=ledger.register("four tick publication","scratch")
def publish(half,center,work):
    assert half and center in (None, *range(10))
    assert work.tile_actions == 128 and work.tile_refusals == 0
    assert work.states == work.joins == work.table_bytes == 0
    raise RuntimeError("publication interrupted")
try:
    try:
        native_folded_pair_action(
            ledger,owner,lambda: bytes([18]*128),None,512,publish,source_width=256
        )
    except RuntimeError as error:
        assert str(error)=="publication interrupted"
    else:
        raise AssertionError("publication fault was lost")
    assert ledger.nodes==ledger.entries==0
finally:
    ledger.mark_disposed(owner)
"""
    subprocess.run([interpreter, "-I", "-c", program], check=True)

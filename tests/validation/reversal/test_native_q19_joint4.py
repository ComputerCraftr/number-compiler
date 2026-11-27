"""A joint physical four-tick Q19 action retains both collars and the clock."""

from __future__ import annotations

import json
import os
import subprocess

import pytest

pytestmark = pytest.mark.validation


def _seed() -> int:
    value = int("1" * 500 + "8" * 500)
    for _ in range(202):
        value += int(str(value)[::-1])
    return value


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
print('PROBES',sum(x[9] for x in calls),file=sys.stderr)
raise SystemExit(status)
"""
    seed = _seed()
    outputs: dict[str, subprocess.CompletedProcess[str]] = {}
    for label, enabled, value, ticks in (
        ("joint", True, seed, 1024),
        ("fallback", False, seed, 1024),
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
        parts = counts.split()
        calls, bands, columns = map(int, parts)
        if label == "joint":
            assert calls > 0 and bands > 0 and columns >= 48
        else:
            assert bands == columns == 0
        if label in {"fallback", "short"}:
            assert calls == 0
        if label == "short-collar":
            assert calls == 1 and 0 < int(probes) <= 10
        assert json.loads(result.stdout)["value"] == str(_literal(value, ticks))
        outputs[label] = result
    assert outputs["joint"].stdout == outputs["fallback"].stdout


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


@pytest.mark.parametrize("fault", ["missing_clock", "short_core"])
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

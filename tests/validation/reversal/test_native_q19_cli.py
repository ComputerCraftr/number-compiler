"""Installed CLI dispatch for the optional source-bound Q19 continuation."""

from __future__ import annotations

import json
import os
import subprocess

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.q19_broadword_publisher import PackedQ19
from number_compiler.sequences.reverse_add.q19_carry_window import _native_segment

pytestmark = pytest.mark.validation


def _literal(seed: int, ticks: int) -> int:
    for _ in range(ticks):
        seed += int(str(seed)[::-1])
    return seed


def test_native_pair_continuation_and_failed_receiver_release(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pytest.importorskip("number_compiler.kernels._reverse_quotients")
    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_NATIVE_REVERSE", "1")
    ledger = ResourceLedger()
    owner = ledger.register("native Q19 test", "scratch")
    frame = PackedQ19.from_digits((6, 9, 1))
    target = _native_segment(frame, 512, ledger, owner)
    expected = PackedQ19.from_digits(tuple(map(int, reversed(str(_literal(196, 512))))))
    assert target == expected
    assert ledger.counters["native_pair_bands"] > 0
    assert ledger.nodes == ledger.entries == 0

    from number_compiler.arithmetic.carry import native_reverse_actions

    def interrupted(*args: object, **kwargs: object) -> None:
        raise KeyboardInterrupt

    monkeypatch.setattr(native_reverse_actions, "native_pair_action", interrupted)
    with pytest.raises(KeyboardInterrupt):
        _native_segment(frame, 512, ledger, owner)
    assert ledger.nodes == ledger.entries == 0


def test_installed_cli_native_admission_and_refusals() -> None:
    interpreter = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if not interpreter:
        pytest.skip("set NUMBER_COMPILER_INSTALLED_PYTHON to a native-wheel venv")
    assert os.path.isabs(interpreter)
    program = """\
import pathlib, sys, sysconfig
import number_compiler
from number_compiler.kernels import _reverse_quotients as native
from number_compiler.api.cli import main
roots = [pathlib.Path(sysconfig.get_path(key)).resolve() for key in ('purelib', 'platlib')]
for module in (number_compiler, native):
    path = pathlib.Path(module.__file__).resolve()
    assert any(path.is_relative_to(root) for root in roots), path
calls = []
def profile(frame, event, arg):
    if event == 'c_call' and arg is native.add:
        calls.append(1)
sys.setprofile(profile)
try:
    status = main(sys.argv[1:])
finally:
    sys.setprofile(None)
print('NATIVE_ADD_CALLS', len(calls), file=sys.stderr)
raise SystemExit(status)
"""
    outputs = {}
    for label, enabled, ticks in (
        ("enabled", True, 1024),
        ("disabled", False, 1024),
        ("short", True, 16),
    ):
        env = dict(os.environ)
        env.pop("NUMBER_COMPILER_ENABLE_NATIVE_REVERSE", None)
        if enabled:
            env["NUMBER_COMPILER_ENABLE_NATIVE_REVERSE"] = "1"
        result = subprocess.run(
            [
                interpreter,
                "-I",
                "-c",
                program,
                "reverse-add",
                "--seed",
                "196",
                "--nth",
                str(ticks),
                "--format",
                "json",
            ],
            check=True,
            capture_output=True,
            text=True,
            env=env,
        )
        assert (int(result.stderr.strip().split("NATIVE_ADD_CALLS ")[-1]) > 0) == (
            label == "enabled"
        )
        output = json.loads(result.stdout)
        assert output["value"] == str(_literal(196, ticks))
        outputs[label] = output
    assert outputs["enabled"] == outputs["disabled"]


def test_warm_q19_frontier_uses_native_suffix_without_step_replay(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pytest.importorskip("number_compiler.kernels._reverse_quotients")
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )

    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_NATIVE_REVERSE", "1")
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, (6, 9, 1), base=10)
    try:
        owner.publish_carry_window_continuation(1024, shared_cache=False)
        prior_bands = ledger.counters["native_pair_bands"]

        def forbid(*_args: object, **_kwargs: object) -> None:
            pytest.fail("warm native suffix replayed chronological pair steps")

        monkeypatch.setattr(PackedQ19, "advance_repeated", forbid)
        result = owner.publish_carry_window_continuation(2048, shared_cache=False)
        assert ledger.counters["native_pair_bands"] > prior_bands
        assert tuple(owner.iter_digits(result)) == tuple(
            map(int, reversed(str(_literal(196, 2048))))
        )
        monkeypatch.setattr(
            "number_compiler.arithmetic.carry.native_reverse_actions.native_pair_action",
            forbid,
        )
        assert (
            owner.publish_carry_window_continuation(2048, shared_cache=False) == result
        )
    finally:
        owner.dispose()
    assert ledger.nodes == ledger.entries == 0

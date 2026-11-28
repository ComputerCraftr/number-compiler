"""A joint physical four-tick Q19 action retains both collars and the clock."""

from __future__ import annotations

import json
import os
import random
import subprocess
from pathlib import Path

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
                str(Path(__file__).with_name("installed_native_cli_fixture.py")),
                "joint",
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
    fixture = Path(__file__).with_name("installed_native_cli_fixture.py")
    task = "joint_native_both_clocks_and_rejected_eq_core"
    subprocess.run([interpreter, "-I", str(fixture), "joint-task", task], check=True)


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
    fixture = Path(__file__).with_name("installed_native_cli_fixture.py")
    task = "joint_action_warm_publication_reuses_completed_result"
    subprocess.run([interpreter, "-I", str(fixture), "joint-task", task], check=True)


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
    fixture = Path(__file__).with_name("installed_native_cli_fixture.py")
    task = "two_birth_slabs_match_physical_rows_and_mixed_receipts"
    subprocess.run([interpreter, "-I", str(fixture), "joint-task", task], check=True)


def test_one_birth_slab_uses_physical_collars_and_center() -> None:
    interpreter = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if not interpreter:
        pytest.skip("set NUMBER_COMPILER_INSTALLED_PYTHON to the native wheel")
    fixture = Path(__file__).with_name("installed_native_cli_fixture.py")
    task = "one_birth_slab_uses_physical_collars_and_center"
    subprocess.run(
        [interpreter, "-I", str(fixture), "joint-task", task, str(_two_birth_seed(18))],
        check=True,
    )


def test_installed_seed196_uses_four_tick_action_with_exact_fallback() -> None:
    interpreter = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if not interpreter:
        pytest.skip("set NUMBER_COMPILER_INSTALLED_PYTHON to the native wheel")
    fixture = Path(__file__).with_name("installed_native_cli_fixture.py")
    task = "q19-receipts"
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
                    str(fixture),
                    task,
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
    fixture = Path(__file__).with_name("installed_native_cli_fixture.py")
    task = "four_tick_carries_match_literal_width_and_center_transitions"
    subprocess.run([interpreter, "-I", str(fixture), "joint-task", task], check=True)


def test_four_tick_failed_publication_releases_native_reservation() -> None:
    interpreter = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if not interpreter:
        pytest.skip("set NUMBER_COMPILER_INSTALLED_PYTHON to the native wheel")
    fixture = Path(__file__).with_name("installed_native_cli_fixture.py")
    task = "four_tick_failed_publication_releases_native_reservation"
    subprocess.run([interpreter, "-I", str(fixture), "joint-task", task], check=True)

"""Installed dense rev10 endpoint admission and exact physical fallbacks."""

from __future__ import annotations

import json
import os
import subprocess
from pathlib import Path
from typing import cast

import pytest

pytestmark = pytest.mark.validation


def _literal(seed: int, multiplier: int, ticks: int) -> str:
    for _ in range(ticks):
        seed = multiplier * int(str(seed)[::-1])
    return str(seed)


def _installed_cli(
    python: str,
    family: str,
    seed: int | str,
    ticks: int,
    *,
    dense: bool,
    portable: bool,
    front: bool = False,
) -> tuple[dict[str, object], list[tuple[int, int, int, int, int, int]]]:
    env = dict(
        os.environ,
        NUMBER_COMPILER_ENABLE_NATIVE_REVERSE="1",
        NUMBER_COMPILER_ENABLE_REFLECTED_MULTIPLY="1",
        NUMBER_COMPILER_ENABLE_REV10_DENSE=str(int(dense)),
        NUMBER_COMPILER_ENABLE_REV10_FRONT=str(int(front)),
    )
    if portable:
        env["NUMBER_COMPILER_DENSE_PORTABLE"] = "1"
    else:
        env.pop("NUMBER_COMPILER_DENSE_PORTABLE", None)
    result = subprocess.run(
        [
            python,
            "-I",
            str(Path(__file__).with_name("installed_native_cli_fixture.py")),
            "dense",
            family,
            "--seed",
            str(seed),
            "--nth",
            str(ticks),
            "--max-steps",
            str(ticks),
            "--max-state-bits",
            "32768",
            "--max-output-bits",
            "32768",
            "--info",
            "metrics",
            "--format",
            "json",
        ],
        env=env,
        text=True,
        capture_output=True,
        check=True,
        timeout=60,
    )
    packet: dict[str, object] = json.loads(result.stdout)
    work = json.loads(result.stderr.split("DENSE_WORK ", 1)[1])
    return packet, [tuple(item) for item in work]


@pytest.mark.parametrize(
    ("family", "multiplier", "seed", "ticks"),
    [
        ("2rev10", 2, 73, 1024),
        ("5rev10", 5, 73, 1024),
        ("2rev10", 2, 73, 16),
        ("5rev10", 5, 73, 16),
        ("2rev10", 2, 0, 1024),
        ("5rev10", 5, 0, 1024),
    ],
)
def test_installed_dense_dispatch_and_fallback(
    family: str, multiplier: int, seed: int, ticks: int
) -> None:
    python = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if python is None:
        pytest.skip("requires installed native reverse wheel")
    assert Path(python).is_absolute()
    fallback, _ = _installed_cli(
        python, family, seed, ticks, dense=False, portable=False
    )
    for portable in (False, True):
        accelerated, counts = _installed_cli(
            python, family, seed, ticks, dense=True, portable=portable
        )
        assert (
            accelerated["value"]
            == fallback["value"]
            == _literal(seed, multiplier, ticks)
        )
        assert {k: v for k, v in accelerated.items() if k != "info"} == {
            k: v for k, v in fallback.items() if k != "info"
        }
        assert (sum(item[0] for item in counts) > 0) == (ticks == 1024 and seed != 0)


@pytest.mark.parametrize("multiplier", (2, 5))
@pytest.mark.parametrize("ticks", (128, 129, 130, 131, 255, 256, 257, 512))
@pytest.mark.parametrize("seed", (73, 410, 1960, 12345007890))
def test_native_dense_ports_trimming_and_clock(
    multiplier: int, ticks: int, seed: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    native = pytest.importorskip("number_compiler.kernels._reverse_quotients")
    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_REV10_DENSE", "1")
    expected = _literal(seed, multiplier, ticks)
    outputs: list[tuple[str, tuple[int | float, ...]]] = []
    for portable in ("0", "1"):
        if portable == "1":
            monkeypatch.setenv("NUMBER_COMPILER_DENSE_PORTABLE", "1")
        else:
            monkeypatch.delenv("NUMBER_COMPILER_DENSE_PORTABLE", raising=False)
        digits, work = cast(
            tuple[str, tuple[int, int, int, int, int, int, float, float]],
            native.multiply(str(seed), multiplier, ticks, 3),
        )
        assert digits == expected
        assert work[3] > 0
        outputs.append((digits, work[:6]))
    assert outputs[0] == outputs[1]


@pytest.mark.parametrize(
    ("family", "multiplier", "motif", "ticks"),
    [("2rev10", 2, "69207", 256), ("5rev10", 5, "96702", 128)],
)
@pytest.mark.parametrize("changed", (False, True))
def test_installed_source_conditioned_front(
    family: str, multiplier: int, motif: str, ticks: int, changed: bool
) -> None:
    python = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if python is None:
        pytest.skip("requires installed native reverse wheel")
    word = motif * (180 if multiplier == 5 else 240)
    if changed:
        middle = len(word) // 2
        word = word[:middle] + str((int(word[middle]) + 1) % 10) + word[middle + 1 :]
    seed = word[::-1]
    baseline, baseline_work = _installed_cli(
        python, family, seed, ticks, dense=True, portable=False
    )
    actual, front_work = _installed_cli(
        python, family, seed, ticks, dense=True, portable=False, front=True
    )
    assert (
        actual["value"] == baseline["value"] == _literal(int(seed), multiplier, ticks)
    )
    assert {k: v for k, v in actual.items() if k != "info"} == {
        k: v for k, v in baseline.items() if k != "info"
    }
    assert sum(row[1] for row in front_work) > 0
    assert sum(row[0] for row in front_work) < sum(row[0] for row in baseline_work)


@pytest.mark.parametrize("family,multiplier", (("2rev10", 2), ("5rev10", 5)))
def test_installed_unrelated_train_has_no_front_authority(
    family: str, multiplier: int
) -> None:
    python = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if python is None:
        pytest.skip("requires installed native reverse wheel")
    seed = ("35148351483" * 110)[::-1]
    ticks = 256
    packet, work = _installed_cli(
        python, family, seed, ticks, dense=True, portable=False, front=True
    )
    assert packet["value"] == _literal(int(seed), multiplier, ticks)
    assert sum(row[1] for row in work) == 0


@pytest.mark.parametrize(
    "family,multiplier,motif", (("2rev10", 2, "69207"), ("5rev10", 5, "96702"))
)
def test_source_period_with_wrong_open_inlet_refuses_front(
    family: str, multiplier: int, motif: str
) -> None:
    python = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if python is None:
        pytest.skip("requires installed native reverse wheel")
    seed = ("1" * 300 + motif * 20 + "8" * 150)[::-1]
    packet, work = _installed_cli(
        python, family, seed, 256, dense=True, portable=False, front=True
    )
    assert packet["value"] == _literal(int(seed), multiplier, 256)
    assert sum(row[2] for row in work) > 0
    assert sum(row[1] for row in work) == 0


def test_complete_dense_port_table_against_scalar_oracle(tmp_path: Path) -> None:
    import shutil

    compiler = shutil.which(os.environ.get("CXX", "c++"))
    if compiler is None:
        pytest.skip("requires a C++20 compiler")
    root = Path(__file__).resolve().parents[3]
    source = Path(__file__).with_name("native_dense_ports.cpp")
    executable = tmp_path / "dense_ports"
    subprocess.run(
        [
            compiler,
            "-std=c++20",
            "-O2",
            "-I",
            str(root / "src/number_compiler/kernels/native_reverse"),
            str(source),
            "-o",
            str(executable),
        ],
        check=True,
        capture_output=True,
        text=True,
        timeout=60,
    )
    result = subprocess.run(
        [str(executable)], check=True, capture_output=True, text=True, timeout=60
    )
    assert result.stdout.strip() == "ordered ports match independent mixed-radix oracle"


def _literal_text(value: str, multiplier: int, ticks: int) -> str:
    for _ in range(ticks):
        digits: list[str] = []
        carry = 0
        for digit in value:
            product = multiplier * (ord(digit) - ord("0")) + carry
            digits.append(chr(ord("0") + product % 10))
            carry = product // 10
        while carry:
            digits.append(chr(ord("0") + carry % 10))
            carry //= 10
        value = "".join(reversed(digits)).lstrip("0") or "0"
    return value


@pytest.mark.parametrize(
    ("family", "multiplier", "motif"),
    (("2rev10", 2, "69207"), ("5rev10", 5, "96702")),
)
def test_installed_train_after_source_qualified_periodic_seam(
    family: str, multiplier: int, motif: str
) -> None:
    python = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if python is None:
        pytest.skip("requires installed native reverse wheel")
    suffix = "3141592653" * 90
    seed = (motif * 580 + suffix)[::-1]
    packet, work = _installed_cli(
        python, family, seed, 2048, dense=True, portable=False, front=True
    )
    assert packet["value"] == _literal_text(seed, multiplier, 2048)
    assert sum(row[3] for row in work) > 0
    assert sum(row[4] for row in work) > 0
    assert sum(row[5] for row in work) >= sum(row[3] for row in work)


@pytest.mark.parametrize(("dense", "updates"), ((False, 1), (True, -1)))
def test_forged_dense_work_receipt_is_rejected(
    dense: bool, updates: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    from number_compiler.arithmetic.carry import native_reverse_actions
    from number_compiler.resources.ledger import ResourceLedger

    class Native:
        @staticmethod
        def multiply(
            source: str, multiplier: int, steps: int, side: int
        ) -> tuple[str, tuple[int, int, int, int, int, int, float, float]]:
            assert source == "73" and multiplier == 5 and steps == 128 and side == 3
            return "1", (0, 0, 0, updates, 0, 0, 0.0, 0.0)

    monkeypatch.setattr(native_reverse_actions, "_load", lambda: Native())
    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_REV10_DENSE", str(int(dense)))
    monkeypatch.delenv("NUMBER_COMPILER_ENABLE_REV10_FRONT", raising=False)
    ledger = ResourceLedger()
    owner = ledger.register("dense receipt fixture", "scratch")
    try:
        with pytest.raises(RuntimeError, match="invalid native diagonal endpoint"):
            native_reverse_actions.diagonal_endpoint(
                ledger, owner, 73, 5, 128, 8192, lambda digits, _work: digits
            )
    finally:
        ledger.mark_disposed(owner)
    assert ledger.nodes == ledger.entries == 0


@pytest.mark.parametrize(
    ("front_columns", "train_columns", "skipped", "lookups"),
    ((2, 3, 1, 3), (2, 1, -1, 3), (2, 1, 1, 1000)),
)
def test_forged_train_work_receipt_is_rejected(
    front_columns: int,
    train_columns: int,
    skipped: int,
    lookups: int,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.carry import native_reverse_actions
    from number_compiler.resources.ledger import ResourceLedger

    class Native:
        @staticmethod
        def multiply_front_profiled(
            source: str, multiplier: int, steps: int, side: int
        ) -> tuple[
            str,
            tuple[int, int, int, int, int, int, float, float],
            int,
            int,
            int,
            int,
            int,
        ]:
            assert source == "73" and multiplier == 5 and steps == 128 and side == 3
            return (
                "1",
                (0, 0, 0, 2, 0, 0, 0.0, 0.0),
                front_columns,
                1,
                train_columns,
                skipped,
                lookups,
            )

    monkeypatch.setattr(native_reverse_actions, "_load", lambda: Native())
    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_REV10_DENSE", "1")
    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_REV10_FRONT", "1")
    ledger = ResourceLedger()
    owner = ledger.register("train receipt fixture", "scratch")
    try:
        with pytest.raises(RuntimeError, match="invalid native"):
            native_reverse_actions.diagonal_endpoint(
                ledger, owner, 73, 5, 128, 8192, lambda digits, _work: digits
            )
    finally:
        ledger.mark_disposed(owner)
    assert ledger.nodes == ledger.entries == 0

"""Installed CLI dispatch for the optional source-bound Q19 continuation."""

from __future__ import annotations

import ast
import json
import os
import subprocess

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.q19_broadword_publisher import PackedQ19
from number_compiler.sequences.reverse_add.q19_carry_window import (
    completed_continuation,
)

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
    expected = PackedQ19.from_digits(tuple(map(int, reversed(str(_literal(196, 512))))))
    with completed_continuation(
        frame,
        512,
        shared_cache=False,
        before_step=lambda _count, _rounds: None,
        ledger=ledger,
        scratch_owner=owner,
    ) as (target, reused):
        assert target == expected
        assert reused == 0
    assert ledger.counters["native_pair_bands"] > 0
    assert ledger.counters["native_pair_hinge_cells"] > 0
    assert ledger.nodes == ledger.entries == 0

    from number_compiler.arithmetic.carry import native_reverse_actions

    def interrupted(*args: object, **kwargs: object) -> None:
        raise KeyboardInterrupt

    with monkeypatch.context() as patch, pytest.raises(KeyboardInterrupt):
        patch.setattr(native_reverse_actions, "native_folded_pair_action", interrupted)
        with completed_continuation(
            frame,
            512,
            shared_cache=False,
            before_step=lambda _count, _rounds: None,
            ledger=ledger,
            scratch_owner=owner,
        ):
            pytest.fail("interrupted native continuation returned")
    assert ledger.nodes == ledger.entries == 0

    # A finite ledger refuses the optional native action before invoking it,
    # and the exact continuation still produces the same endpoint.
    bounded = ResourceLedger(max_nodes=128)
    bounded_owner = bounded.register("bounded Q19 test", "scratch")
    with completed_continuation(
        frame,
        512,
        shared_cache=False,
        before_step=lambda _count, _rounds: None,
        ledger=bounded,
        scratch_owner=bounded_owner,
    ) as (fallback, reused):
        assert fallback == expected
        assert reused == 0
    assert bounded.nodes == bounded.entries == 0


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
    if event == 'c_call' and arg is native.add_folded:
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
            "number_compiler.arithmetic.carry.native_reverse_actions.native_folded_pair_action",
            forbid,
        )
        assert (
            owner.publish_carry_window_continuation(2048, shared_cache=False) == result
        )
    finally:
        owner.dispose()
    assert ledger.nodes == ledger.entries == 0


def test_native_refusal_precedes_mirrored_source_construction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.carry import native_reverse_actions as native

    ledger = ResourceLedger()
    owner = ledger.register("deferred Q19 validation", "scratch")

    def forbid() -> bytes:
        pytest.fail("refused Q19 source was materialized")

    def no_module() -> None:
        return None

    try:
        monkeypatch.setattr(native, "_load", no_module)
        assert (
            native.native_pair_action(
                ledger, owner, forbid, 512, lambda p, w: p, source_width=5
            )
            is None
        )
        monkeypatch.setattr(native, "_load", forbid)
        assert (
            native.native_pair_action(
                ledger, owner, forbid, 512, lambda p, w: p, source_width=1_000_000
            )
            is None
        )
    finally:
        ledger.mark_disposed(owner)
    assert ledger.nodes == ledger.entries == 0


def _literal_pair_fields(seed: int) -> tuple[bytes, bytes, int]:
    digits = str(seed)
    field = bytes(int(a) + int(b) for a, b in zip(digits, digits[::-1], strict=True))
    half = field[: len(field) // 2]
    center = int(digits[len(half)]) if len(field) % 2 else -1
    return field, half, center


def test_folded_kernel_matches_full_pair_field_and_rejects_bad_centers() -> None:
    import random

    native = pytest.importorskip("number_compiler.kernels._reverse_quotients")
    rng = random.Random(43)
    sources = (0, 1, 9, 10, 50, 95, 98, 104, 196, 9999, 190999)
    for seed in (*sources, *(rng.randrange(10**20) for _ in range(50))):
        full, half, center = _literal_pair_fields(seed)
        for ticks in (0, 1, 2, 3, 4, 5, 7, 16, 17, 31, 64, 128, 512):
            expected, _ = native.add(full, ticks, 2, 1, 4 << 20)
            pairs, result_center, _ = native.add_folded(half, center, ticks, 4 << 20)
            midpoint = bytes((2 * result_center,)) if result_center >= 0 else b""
            assert pairs + midpoint + pairs[::-1] == expected
            if ticks in (1, 7, 512):
                literal = str(_literal(seed, ticks))
                assert expected == bytes(
                    int(a) + int(b) for a, b in zip(literal, literal[::-1], strict=True)
                )
    for bad_center in (-2, 10):
        with pytest.raises(ValueError, match="folded"):
            native.add_folded(b"\x01", bad_center, 2, 4 << 20)
    with pytest.raises(ValueError, match="invalid pair coefficient"):
        native.add_folded(b"\x13", -1, 2, 4 << 20)


def test_old_native_module_falls_back_before_unfolding_source(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.carry import native_reverse_actions

    monkeypatch.setattr(native_reverse_actions, "_load", lambda: object())
    ledger = ResourceLedger()
    owner = ledger.register("old native module", "scratch")

    def forbid() -> bytes:
        pytest.fail("old native module opened the source")

    assert (
        native_reverse_actions.native_folded_pair_action(
            ledger, owner, forbid, 6, 512, lambda p, c, w: p, source_width=3
        )
        is None
    )
    assert ledger.nodes == ledger.entries == 0


@pytest.mark.parametrize("seed,clock", ((909, "1011"), (99, "1110"), (59, "1010")))
def test_adjacent_folded_bands_preserve_physical_births(seed: int, clock: str) -> None:
    native = pytest.importorskip("number_compiler.kernels._reverse_quotients")
    _, half, center = _literal_pair_fields(seed)
    widths = [len(str(seed))]
    current = seed
    for _ in range(4):
        current += int(str(current)[::-1])
        widths.append(len(str(current)))
    assert (
        "".join(str(int(b > a)) for a, b in zip(widths, widths[1:], strict=False))
        == clock
    )
    for band in range(2):
        half, center, work = native.add_folded(half, center, 2, 4 << 20)
        assert work[4] == widths[2 * band + 2] - widths[2 * band]
        full = half + (bytes((2 * center,)) if center >= 0 else b"") + half[::-1]
        text = str(_literal(seed, 2 * band + 2))
        assert full == bytes(
            int(a) + int(b) for a, b in zip(text, text[::-1], strict=True)
        )


def test_band_birth_totals_do_not_authorize_a_four_tick_schedule() -> None:
    native = pytest.importorskip("number_compiler.kernels._reverse_quotients")
    observed: list[list[int]] = []
    for seed in (9, 18):
        _, half, center = _literal_pair_fields(seed)
        totals: list[int] = []
        for _ in range(2):
            half, center, work = native.add_folded(half, center, 2, 4 << 20)
            totals.append(int(work[4]))
        observed.append(totals)
    assert observed == [[1, 2], [1, 2]]
    clocks: list[str] = []
    for seed in (9, 18):
        clock = ""
        for _ in range(4):
            successor = seed + int(str(seed)[::-1])
            clock += str(int(len(str(successor)) > len(str(seed))))
            seed = successor
        clocks.append(clock)
    assert clocks == ["1011", "0111"]


@pytest.mark.parametrize("slot", (1, 2, 3))
@pytest.mark.parametrize("bad", (True, False, -1, 2**64 + 1))
def test_folded_binding_rejects_non_exact_and_overflowing_controls(
    slot: int, bad: int
) -> None:
    native = pytest.importorskip("number_compiler.kernels._reverse_quotients")
    args: list[object] = [b"\x01", 5, 512, 4 << 20]
    args[slot] = bad
    # Center -1 is the valid even-width sentinel.
    if slot == 1 and bad == -1 and type(bad) is int:
        assert native.add_folded(*args)[1] in range(-1, 10)
    else:
        with pytest.raises((TypeError, ValueError, OverflowError)):
            native.add_folded(*args)


def test_folded_two_tick_action_reuses_issued_cells_under_tight_table_cap() -> None:
    native = pytest.importorskip("number_compiler.kernels._reverse_quotients")
    seed = _literal(196, 12)
    field, half, center = _literal_pair_fields(seed)
    expected, _ = native.add(field, 3, 2, 1, 4 << 20)
    pairs, result_center, work = native.add_folded(half, center, 3, 300000)
    midpoint = bytes((2 * result_center,)) if result_center >= 0 else b""
    assert pairs + midpoint + pairs[::-1] == expected
    assert work[5] == 290128
    with pytest.raises(ValueError, match="budget exceeded"):
        native.add_folded(half, center, 3, work[5] - 1)


@pytest.mark.parametrize("seed", (73, 196))
def test_guarded_four_tick_tiles_match_direct_and_keep_the_clock(seed: int) -> None:
    native = pytest.importorskip("number_compiler.kernels._reverse_quotients")
    source = _literal(seed, 12)
    full, half, center = _literal_pair_fields(source)
    direct = native.add_folded(half, center, 4083, 300000)
    banked = native.add_folded(half, center, 4083, 4 << 20)
    assert banked[:2] == direct[:2]
    assert banked[2][:5] == direct[2][:5]
    assert banked[2][20] > 0
    assert banked[2][15:19] == (0, 0, 0, 0)
    assert direct[2][15:19] == (0, 0, 0, 0)
    expected, _ = native.add(full, 4083, 2, 1, 4 << 20)
    midpoint = bytes((2 * banked[1],)) if banked[1] >= 0 else b""
    assert banked[0] + midpoint + banked[0][::-1] == expected
    assert native.add_folded(half, center, 1011, 4 << 20)[2][15] == 0


def test_folded_bank_uses_full_ordered_rows_at_admission_boundary() -> None:
    native = pytest.importorskip("number_compiler.kernels._reverse_quotients")
    # A source-ambiguous outer prefix forces the exact fallback before
    # the later four-tick actions become available.
    half = bytes([9] * 8 + [1] * 1016)
    center = 0
    full = half + bytes([2 * center]) + half[::-1]
    below = native.add_folded(half, center, 511, 4 << 20)
    assert below[2][15:19] == (0, 0, 0, 0)
    for cap in (300000, 4 << 20):
        got = native.add_folded(half, center, 512, cap)
        expected, _ = native.add(full, 512, 2, 1, 4 << 20)
        midpoint = bytes((2 * got[1],)) if got[1] >= 0 else b""
        assert got[0] + midpoint + got[0][::-1] == expected
        if cap == 300000:
            assert got[2][15] == 0
        else:
            assert 0 < got[2][16] <= got[2][15]
            assert got[2][18] == 33212


def test_installed_cli_prefers_source_guarded_four_tick_tiles() -> None:
    interpreter = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if not interpreter:
        pytest.skip("set NUMBER_COMPILER_INSTALLED_PYTHON to a native-wheel venv")
    program = """\
import sys
from number_compiler.kernels import _reverse_quotients as native
from number_compiler.api.cli import main
import os
name = "add_folded_joint4" if os.environ.get("NUMBER_COMPILER_ENABLE_Q19_JOINT4") == "1" else "add_folded"
original = getattr(native, name)
counts = []
def observed(*args):
    result = original(*args)
    counts.append(result[2][15:25])
    return result
setattr(native, name, observed)
status = main(sys.argv[1:])
print("BANK", repr(counts), file=sys.stderr)
raise SystemExit(status)
"""
    env = dict(os.environ, NUMBER_COMPILER_ENABLE_NATIVE_REVERSE="1")
    env.pop("NUMBER_COMPILER_ENABLE_Q19_JOINT4", None)
    for ticks, joint in ((1024, False), (4096, False), (4096, True)):
        if joint:
            env["NUMBER_COMPILER_ENABLE_Q19_JOINT4"] = "1"
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
        assert json.loads(result.stdout)["value"] == str(_literal(196, ticks))
        receipt = ast.literal_eval(result.stderr.removeprefix("BANK "))
        assert len(receipt) == 1
        probes, builds, comparisons, slots, attempts, actions, cores, *_ = receipt[0]
        assert probes == builds == comparisons == slots == 0
        assert 0 < actions <= attempts
        assert cores >= actions


@pytest.mark.parametrize(
    "bank",
    (
        (1, 2, 1, 2),
        (1, 1, 1, 0),
        (11, 1, 1, 2),
        (-1, 0, 1, 2),
        (1, 1, -1, 2),
    ),
)
def test_invalid_folded_bank_receipt_does_not_publish(
    bank: tuple[int, ...], monkeypatch: pytest.MonkeyPatch
) -> None:
    from number_compiler.arithmetic.carry import native_reverse_actions as actions

    class Native:
        @staticmethod
        def add_folded(*_args: object) -> tuple[bytes, int, tuple[int, ...]]:
            return b"\x01\x01", -1, (1, 256, 20, 20, 0, 1, 1, *([0] * 8), *bank)

    monkeypatch.setattr(actions, "_load", lambda: Native())
    monkeypatch.delenv("NUMBER_COMPILER_ENABLE_Q19_JOINT4", raising=False)
    ledger = ResourceLedger()
    owner = ledger.register("invalid folded bank receipt", "scratch")

    def receive(_half: bytes, _center: int | None, _work: actions.PairWork) -> None:
        pytest.fail("invalid bank receipt reached the consumer")

    with pytest.raises(RuntimeError, match="invalid native folded causal endpoint"):
        actions.native_folded_pair_action(
            ledger, owner, lambda: b"\x01\x01", None, 512, receive, source_width=4
        )
    assert ledger.nodes == ledger.entries == 0

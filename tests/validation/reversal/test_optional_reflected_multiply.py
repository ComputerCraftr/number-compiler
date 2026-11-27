"""The optional reflected kernel remains subordinate to source and bounds."""

from __future__ import annotations

import importlib
import sys
from collections.abc import Callable
from types import FrameType

import pytest

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.temporal_carry_spacetime import (
    try_native_reflected_endpoint,
)

pytestmark = pytest.mark.validation


def _literal(seed: int, ticks: int) -> int:
    for _ in range(ticks):
        seed = 2 * int(str(seed)[::-1])
    return seed


def test_reflected_suffix_honors_explicit_opt_out(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    native = pytest.importorskip("number_compiler.kernels._reflected_multiply")
    expected = _literal(73, 1024)
    calls: list[object] = []

    def trace(
        _frame: FrameType, event: str, arg: object
    ) -> Callable[..., object] | None:
        if event == "c_call" and arg is native.multiply:
            calls.append(arg)
        return None

    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_REFLECTED_MULTIPLY", "1")
    try:
        sys.setprofile(trace)
        with DoubleReverseTerm(73, 1024, max_steps=1024, max_state_bits=8192) as term:
            assert term.materialize(max_bits=8192) == expected
            assert term.metrics()["double_reverse_native_suffix_ticks"] == 1016
            assert term.metrics()["double_reverse_packed_diagonal_row_evaluations"] == 0
    finally:
        sys.setprofile(None)
    assert calls

    calls.clear()
    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_REFLECTED_MULTIPLY", "0")
    try:
        sys.setprofile(trace)
        with DoubleReverseTerm(73, 1024, max_steps=1024, max_state_bits=8192) as term:
            assert term.materialize(max_bits=8192) == expected
            assert term.metrics()["double_reverse_native_suffix_ticks"] == 0
            assert (
                term.metrics()["double_reverse_packed_diagonal_row_evaluations"] == 896
            )
    finally:
        sys.setprofile(None)
    assert not calls


def test_source_suffix_rejects_issued_border_on_wrong_clock(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    native = pytest.importorskip("number_compiler.kernels._reflected_multiply")
    from number_compiler.sequences.double_reverse.source_adapter import (
        DoubleReverseSourceAdapter,
    )
    from number_compiler.sequences.double_reverse.temporal_hashlife_types import (
        DoubleReverseSourcePrefix,
    )

    issue = DoubleReverseSourceAdapter.certified_prefix_entry

    def wrong_clock(
        self: DoubleReverseSourceAdapter,
        generation: int,
        *,
        max_prefix: int,
        require_even_remainder: bool,
    ) -> DoubleReverseSourcePrefix:
        return issue(
            self, generation, max_prefix=max_prefix, require_even_remainder=False
        )

    def forbidden(*_args: object) -> str:
        raise AssertionError("foreign phase reached native multiplication")

    monkeypatch.delenv("NUMBER_COMPILER_ENABLE_REFLECTED_MULTIPLY", raising=False)
    monkeypatch.setattr(
        DoubleReverseSourceAdapter, "certified_prefix_entry", wrong_clock
    )
    monkeypatch.setattr(native, "multiply", forbidden)
    with DoubleReverseTerm(196, 513, max_steps=513, max_state_bits=8192) as term:
        with pytest.raises(ValueError, match="wrong physical clock"):
            term.materialize(max_bits=8192)


def test_optional_reflected_bounds_and_missing_extension_fall_back(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    owner = ledger.register("optional reflected test", "scratch")
    arena = LedgerSLPArena(ledger, "optional reflected source", "grammar")
    root = arena.word((1, 7, 8, 8))
    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_REFLECTED_MULTIPLY", "1")
    original = importlib.import_module

    def missing(name: str, package: str | None = None) -> object:
        if name == "number_compiler.kernels._reflected_multiply":
            raise ModuleNotFoundError("absent optional extension", name=name)
        return original(name, package)

    try:
        assert try_native_reflected_endpoint(arena, root, 32, 0, owner) is None
        monkeypatch.setattr(importlib, "import_module", missing)
        assert try_native_reflected_endpoint(arena, root, 64, 0, owner) is None
    finally:
        arena.dispose()
        ledger.mark_disposed(owner)
    assert ledger.nodes == ledger.entries == 0


def test_native_rejects_foreign_phase_before_kernel(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pytest.importorskip("number_compiler.kernels._reflected_multiply")
    ledger = ResourceLedger()
    owner = ledger.register("foreign phase", "scratch")
    arena = LedgerSLPArena(ledger, "foreign reflected source", "grammar")
    root = arena.word((1, 7, 8, 8))
    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_REFLECTED_MULTIPLY", "1")
    checkpoint = len(arena.nodes)
    try:
        with pytest.raises(ValueError, match="another issued phase"):
            try_native_reflected_endpoint(arena, root, 64, 1, owner)
        assert len(arena.nodes) == checkpoint
    finally:
        arena.dispose()
        ledger.mark_disposed(owner)
    assert ledger.nodes == ledger.entries == 0


def test_native_close_failure_rolls_back_unpublished_root(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    pytest.importorskip("number_compiler.kernels._reflected_multiply")
    ledger = ResourceLedger()
    owner = ledger.register("native cleanup failure", "scratch")
    arena = LedgerSLPArena(ledger, "native cleanup source", "grammar")
    root = arena.word((1, 7, 8, 8))
    checkpoint = len(arena.nodes)
    slots = 128 * 1000 + 256 * (4 + 128 + 256)
    original = ResourceLedger.release

    def fail_after_release(
        instance: ResourceLedger, owner_id: int, *, entries: int = 0, nodes: int = 0
    ) -> None:
        original(instance, owner_id, entries=entries, nodes=nodes)
        if instance is ledger and owner_id == owner and entries == nodes == slots:
            raise RuntimeError("injected native cleanup failure")

    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_REFLECTED_MULTIPLY", "1")
    try:
        with monkeypatch.context() as patch:
            patch.setattr(ResourceLedger, "release", fail_after_release)
            with pytest.raises(RuntimeError, match="injected native cleanup failure"):
                try_native_reflected_endpoint(arena, root, 64, 0, owner)
        assert len(arena.nodes) == checkpoint
    finally:
        arena.dispose()
        ledger.mark_disposed(owner)
    assert ledger.nodes == ledger.entries == 0


@pytest.mark.parametrize("seed", [1788, 1742, 4888, 4842, 1960])
@pytest.mark.parametrize("ticks", [128, 129, 256])
def test_native_physical_word_matches_literal(seed: int, ticks: int) -> None:
    native = pytest.importorskip("number_compiler.kernels._reflected_multiply")
    assert native.multiply(str(seed), ticks) == str(_literal(seed, ticks))
    with pytest.raises(ValueError, match="bounded geometry"):
        native.multiply(str(seed), 127)


def test_native_rejects_wrong_ordered_outlet_before_publication(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    native = pytest.importorskip("number_compiler.kernels._reflected_multiply")
    ledger = ResourceLedger()
    owner = ledger.register("native wrong outlet", "scratch")
    arena = LedgerSLPArena(ledger, "native wrong outlet source", "grammar")
    root = arena.word((1, 7, 8, 8))
    checkpoint = len(arena.nodes)
    original = importlib.import_module

    class WrongOutlet:
        @staticmethod
        def multiply(word: str, ticks: int) -> str:
            output = native.multiply(word, ticks)
            assert isinstance(output, str)
            return output[:-2] + "0" + output[-1]

    def fake(name: str, package: str | None = None) -> object:
        if name == "number_compiler.kernels._reflected_multiply":
            return WrongOutlet()
        return original(name, package)

    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_REFLECTED_MULTIPLY", "1")
    try:
        with monkeypatch.context() as patch:
            patch.setattr(importlib, "import_module", fake)
            with pytest.raises(ValueError, match="changed its issued borders"):
                try_native_reflected_endpoint(arena, root, 64, 0, owner)
        assert len(arena.nodes) == checkpoint
    finally:
        arena.dispose()
        ledger.mark_disposed(owner)
    assert ledger.nodes == ledger.entries == 0


def test_same_installed_cli_opt_in_and_fallback_have_exact_output() -> None:
    import json
    import os
    import subprocess

    installed_python = os.environ.get("NUMBER_COMPILER_INSTALLED_PYTHON")
    if installed_python is None:
        pytest.importorskip("number_compiler.kernels._reflected_multiply")
    else:
        from pathlib import Path

        assert Path(installed_python).is_absolute() and Path(installed_python).is_file()
    program = """\
import json, pathlib, sys, sysconfig
import number_compiler
from number_compiler.kernels import _reflected_multiply as native
if sys.argv.pop(1) == 'installed':
    roots = [pathlib.Path(sysconfig.get_path(key)).resolve() for key in ('purelib', 'platlib')]
    for path in (number_compiler.__file__, native.__file__):
        assert path is not None and any(pathlib.Path(path).resolve().is_relative_to(root) for root in roots)
from number_compiler.api.cli import main
calls = []
multiply = native.multiply
def observe(word, ticks):
    calls.append([word,ticks])
    return multiply(word, ticks)
native.multiply = observe
status = main(sys.argv[1:])
print("NATIVE_SPANS", json.dumps(calls), file=sys.stderr)
raise SystemExit(status)
"""
    outputs: dict[str, object] = {}
    for label, seed, enabled, ticks, spans in (
        ("enabled", 73, "1", 1024, [1016]),
        ("disabled", 73, "0", 1024, []),
        ("default", 73, None, 1024, [1016]),
        ("prefix16", 196, None, 1024, [1008]),
        ("odd_clock", 73, None, 513, [504]),
        ("missed_border", 11, None, 512, []),
        ("short", 73, None, 16, []),
    ):
        env = dict(os.environ)
        if enabled is None:
            env.pop("NUMBER_COMPILER_ENABLE_REFLECTED_MULTIPLY", None)
        else:
            env["NUMBER_COMPILER_ENABLE_REFLECTED_MULTIPLY"] = enabled
        command = [
            installed_python or sys.executable,
            *(["-I"] if installed_python is not None else []),
            "-c",
            program,
            "installed" if installed_python is not None else "source",
            "2rev10",
            "--seed",
            str(seed),
            "--nth",
            str(ticks),
            "--max-steps",
            str(ticks),
            "--max-state-bits",
            "8192",
            "--max-output-bits",
            "8192",
            "--format",
            "json",
        ]
        result = subprocess.run(
            command, capture_output=True, text=True, check=True, env=env
        )
        calls = json.loads(result.stderr.strip().split("NATIVE_SPANS ")[-1])
        assert calls == [[str(_literal(seed, ticks - span)), span] for span in spans]
        output = json.loads(result.stdout)
        assert output["value"] == str(_literal(seed, ticks))
        outputs[label] = output
    assert outputs["enabled"] == outputs["disabled"] == outputs["default"]

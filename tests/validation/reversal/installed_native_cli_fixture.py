"""Run the installed console entry with measured native reversal calls.

Execute this file with the installed interpreter and ``-I``.  Native modules
must be files owned by the installed distribution, not an editable checkout.
"""

from __future__ import annotations

import json
import os
import sys
from importlib import import_module
from importlib.metadata import Distribution, distribution
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from types import ModuleType
from typing import Any, cast


def installed_manifest(dist: Distribution) -> frozenset[Path]:
    assert dist.files is not None
    return frozenset(Path(str(dist.locate_file(item))).resolve() for item in dist.files)


def assert_owned_module(owned: frozenset[Path], module: ModuleType) -> None:
    assert module.__file__ is not None
    actual = Path(module.__file__).resolve()
    assert actual in owned, f"{actual} is not owned by the installed distribution"


def main() -> int:
    import number_compiler

    mode = sys.argv[1]
    native: Any = cast(
        Any,
        (
            None
            if mode.removesuffix("-source") == "reflected"
            else import_module("number_compiler.kernels._reverse_quotients")
        ),
    )
    source = mode.endswith("-source")
    if source:
        mode = mode.removesuffix("-source")
        from number_compiler.api.cli import main as run

        owned: frozenset[Path] = frozenset()
    else:
        dist = distribution("number-compiler")
        owned = installed_manifest(dist)
        assert_owned_module(owned, number_compiler)
        if native is not None:
            assert_owned_module(owned, native)
        (entry,) = dist.entry_points.select(
            group="console_scripts", name="number-compiler"
        )
        run = entry.load()
    args = sys.argv[2:]
    if mode == "reflected":
        reflected_native: Any = import_module(
            "number_compiler.kernels._reflected_multiply"
        )
        if not source:
            assert_owned_module(owned, reflected_native)
        original = reflected_native.multiply
        spans: list[list[object]] = []

        def observe(word: str, ticks: int) -> object:
            spans.append([word, ticks])
            return original(word, ticks)

        reflected_native.multiply = observe
        try:
            return int(run(args))
        finally:
            print("NATIVE_SPANS", json.dumps(spans), file=sys.stderr)
    assert native is not None
    if mode in ("joint-task", "relative-task"):
        filename = (
            "native_joint4_fixture.py"
            if mode == "joint-task"
            else "native_relative_fixture.py"
        )
        spec = spec_from_file_location(
            "native_action_fixture", Path(__file__).with_name(filename)
        )
        assert spec is not None and spec.loader is not None
        module = module_from_spec(spec)
        spec.loader.exec_module(module)
        task = args[0]
        sys.argv = [sys.argv[0], *args[1:]]
        module.run_task(task)
        return 0
    if mode == "dense":
        reflected: Any = import_module("number_compiler.kernels._reflected_multiply")

        assert_owned_module(owned, reflected)
        work: list[tuple[int, ...]] = []
        diagonal, diagonal_front = native.multiply, native.multiply_front_profiled
        reflected_step = reflected.multiply_profiled
        reflected_front = reflected.multiply_front_profiled

        def diag(*values: object) -> object:
            result = diagonal(*values)
            work.append((result[1][3], 0, 0, 0, 0, 0))
            return result

        def refl(*values: object) -> object:
            result = reflected_step(*values)
            work.append((result[1], 0, 0, 0, 0, 0))
            return result

        def diag_front(*values: object) -> object:
            result = diagonal_front(*values)
            work.append((result[1][3], *result[2:]))
            return result

        def refl_front(*values: object) -> object:
            result = reflected_front(*values)
            work.append(tuple(result[1:]))
            return result

        native.multiply, native.multiply_front_profiled = diag, diag_front
        reflected.multiply_profiled, reflected.multiply_front_profiled = (
            refl,
            refl_front,
        )
        try:
            return int(run(args))
        finally:
            print("DENSE_WORK", json.dumps(work), file=sys.stderr)
    if mode in ("q19", "wide"):
        target = native.add_folded if mode == "q19" else native.multiply
        calls: list[int] = []

        def profile(_frame: object, event: str, fn: object) -> None:
            if event == "c_call" and fn is target:
                calls.append(1)

        sys.setprofile(profile)
        try:
            return int(run(args))
        finally:
            sys.setprofile(None)
            print(
                "NATIVE_ADD_CALLS" if mode == "q19" else "", len(calls), file=sys.stderr
            )
    if mode == "q19-receipts":
        original = native.add_folded
        receipts: list[Any] = []

        def checked(*values: object) -> object:
            result = original(*values)
            receipts.append(result[2])
            return result

        native.add_folded = checked
        try:
            return int(run(args))
        finally:
            print("Q19_RECEIPTS", json.dumps(receipts), file=sys.stderr)
    if mode == "relative":
        target = native
        if args[0] == "2rev10":
            target = import_module("number_compiler.kernels._reflected_multiply")
            assert_owned_module(owned, target)
        original = target.multiply
        hits: list[int] = []

        def probe(_frame: object, event: str, fn: object) -> None:
            if event == "c_call" and fn is original:
                hits.append(1)

        sys.setprofile(probe)
        try:
            return int(run(args))
        finally:
            sys.setprofile(None)
            print("NATIVE_C_CALLS", len(hits), file=sys.stderr)
    if mode == "five":
        original = native.multiply
        five_hits: list[int] = []

        def measured(*values: object) -> object:
            result = original(*values)
            print("NATIVE_WORK", json.dumps(result[1]), file=sys.stderr)
            return result

        def probe(_frame: object, event: str, fn: object) -> None:
            if event == "c_call" and fn is original:
                five_hits.append(1)

        native.multiply = measured
        sys.setprofile(probe)
        try:
            return int(run(args))
        finally:
            sys.setprofile(None)
            print("NATIVE_C_CALLS", len(five_hits), file=sys.stderr)
    if mode == "q19-bank":
        name = (
            "add_folded_joint4"
            if os.environ.get("NUMBER_COMPILER_ENABLE_Q19_JOINT4") == "1"
            else "add_folded"
        )
        original = getattr(native, name)
        bank_calls: list[Any] = []

        def observed(*values: object) -> object:
            result = original(*values)
            bank_calls.append(result[2][15:26])
            return result

        setattr(native, name, observed)
        try:
            return int(run(args))
        finally:
            print("BANK", repr(bank_calls), file=sys.stderr)
    if mode == "joint":
        original = native.add_folded_joint4
        joint_calls: list[Any] = []

        def joint(*values: object) -> object:
            result = original(*values)
            joint_calls.append(result[2])
            return result

        native.add_folded_joint4 = joint
        try:
            return int(run(args))
        finally:
            print(
                "JOINT_CALLS",
                len(joint_calls),
                sum(x[7] for x in joint_calls),
                sum(x[8] for x in joint_calls),
                file=sys.stderr,
            )
            print(
                "PROBES",
                sum(x[9] for x in joint_calls),
                "TWO_BIRTHS",
                sum(x[13] for x in joint_calls),
                "ONE_BIRTH",
                sum(x[14] for x in joint_calls),
                file=sys.stderr,
            )
    raise ValueError(f"unknown native CLI fixture: {mode}")


if __name__ == "__main__":
    raise SystemExit(main())

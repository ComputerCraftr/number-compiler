"""Run the installed console entry with measured native reversal calls.

Execute this file with the installed interpreter and ``-I``.  Native modules
must be files owned by the installed distribution, not an editable checkout.
"""

from __future__ import annotations

import json
import sys
from importlib import import_module
from importlib.metadata import Distribution, distribution
from pathlib import Path
from types import ModuleType
from typing import Any


def _manifest(dist: Distribution) -> frozenset[Path]:
    assert dist.files is not None
    return frozenset(Path(str(dist.locate_file(item))).resolve() for item in dist.files)


def _owned_module(owned: frozenset[Path], module: ModuleType) -> None:
    assert module.__file__ is not None
    actual = Path(module.__file__).resolve()
    assert actual in owned, f"{actual} is not owned by the installed distribution"


def main() -> int:
    import number_compiler

    native: Any = import_module("number_compiler.kernels._reverse_quotients")

    dist = distribution("number-compiler")
    owned = _manifest(dist)
    _owned_module(owned, number_compiler)
    _owned_module(owned, native)
    mode = sys.argv[1]
    args = sys.argv[2:]
    (entry,) = dist.entry_points.select(group="console_scripts", name="number-compiler")
    if mode == "dense":
        reflected: Any = import_module("number_compiler.kernels._reflected_multiply")

        _owned_module(owned, reflected)
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
            return int(entry.load()(args))
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
            return int(entry.load()(args))
        finally:
            sys.setprofile(None)
            print(
                "NATIVE_ADD_CALLS" if mode == "q19" else "", len(calls), file=sys.stderr
            )
    if mode == "joint":
        original = native.add_folded_joint4
        joint_calls: list[Any] = []

        def joint(*values: object) -> object:
            result = original(*values)
            joint_calls.append(result[2])
            return result

        native.add_folded_joint4 = joint
        try:
            return int(entry.load()(args))
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

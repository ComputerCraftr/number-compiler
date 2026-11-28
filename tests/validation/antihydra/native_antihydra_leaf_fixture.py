"""Exercise the optional transient leaf through the installed CLI entry."""

from __future__ import annotations

import contextlib
import io
import os
from collections.abc import Callable
from importlib import import_module
from importlib.metadata import distribution
from pathlib import Path
from random import Random
from typing import cast

from number_compiler.sequences.antihydra.mahler_transient_carry_sheet import (
    TransientFold,
    fold_transient_returns,
)


def main() -> None:
    native = import_module("number_compiler.kernels._cf_continuant")
    package = import_module("number_compiler")
    installed = distribution("number-compiler")
    assert installed.files is not None
    owned = {
        Path(str(installed.locate_file(item))).resolve() for item in installed.files
    }
    for module in (native, package):
        assert module.__file__ is not None and Path(module.__file__).resolve() in owned

    run_leaf = cast(Callable[[int, int], TransientFold], native.antihydra_leaf)
    os.environ.pop("NUMBER_COMPILER_ENABLE_ANTIHYDRA_LEAF", None)
    random = Random(56214)
    for case in range(256):
        horizon = case % 129
        source = (random.getrandbits(120) << 8) | case
        expected = fold_transient_returns(source, horizon)
        assert run_leaf(source, horizon) == expected
    for value, horizon in ((8, 129), (True, 8), (-1, 8), (1 << 249, 8)):
        try:
            run_leaf(value, horizon)
        except (TypeError, ValueError, OverflowError):
            pass
        else:
            raise AssertionError("native leaf accepted an invalid source or horizon")

    calls = 0

    def observe(value: int, ticks: int) -> TransientFold:
        nonlocal calls
        calls += 1
        assert 8 <= ticks <= 128
        return run_leaf(value, ticks)

    vars(native)["antihydra_leaf"] = observe
    (entry,) = installed.entry_points.select(
        group="console_scripts", name="number-compiler"
    )
    run = entry.load()
    for horizon in (63, 128, 255, 512, 1024, 2048, 4092):
        args = [
            "antihydra",
            "--nth",
            str(horizon),
            "--no-value",
            "--format",
            "json",
            "--info",
            "arithmetic.mahler",
        ]
        readings: list[str] = []
        for enable in ("0", "1"):
            os.environ["NUMBER_COMPILER_ENABLE_ANTIHYDRA_LEAF"] = enable
            with contextlib.redirect_stdout(io.StringIO()) as out:
                assert run(args, shared_cache=False) == 0
            readings.append(out.getvalue())
        assert readings[0] == readings[1]
    assert calls > 0
    issued = calls
    os.environ["NUMBER_COMPILER_ENABLE_ANTIHYDRA_LEAF"] = "0"
    wide = (1 << 249) + 11
    portable = fold_transient_returns(wide, 8)
    os.environ["NUMBER_COMPILER_ENABLE_ANTIHYDRA_LEAF"] = "1"
    assert fold_transient_returns(wide, 8) == portable and calls == issued
    with (
        contextlib.redirect_stdout(io.StringIO()),
        contextlib.redirect_stderr(io.StringIO()),
    ):
        assert run(["antihydra", "--nth", "4092", "--max-steps", "2"]) == 2
    assert calls == issued
    print(f"7 installed CLI packets and 256 leaf receipts exact, {calls} native calls")


if __name__ == "__main__":
    main()

"""Exact public digits must not depend on the retired causal output engine.

The larger 196 seam/seed matrix lives in test_reverse_temporal_publisher_cutover.
These cases cover the other requested families without asking for observers or
classification. Passing does not prove a construction bound or primality.
"""

from typing import Never

import pytest

from number_compiler.api.cli import main
from number_compiler.hashlife.execution.continuations.higher_bimachine import (
    HigherBimachineRuntime,
)
from number_compiler.hashlife.execution.recursive_outputs import (
    RecursiveCoordinateMorphismArena,
)
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine


@pytest.mark.parametrize(
    "family,index",
    [("collatz", 64), ("antihydra", 64), ("fermat", 5), ("mersenne", 31)],
)
def test_exact_digits_do_not_enter_causal_or_temporal_replay(
    family: str,
    index: int,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    # Independent bounded references are used only to check emitted digits.
    if family == "fermat":
        expected = (1 << (1 << index)) + 1
    elif family == "mersenne":
        expected = (1 << index) - 1
    elif family == "antihydra":
        expected = 8
        for _ in range(index):
            expected += expected // 2
    else:
        expected = 27
        for _ in range(index):
            expected = 3 * expected + 1 if expected & 1 else expected // 2

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("public digits still enter causal/temporal replay")

    monkeypatch.setattr(CausalTileEngine, "_run", forbidden)
    monkeypatch.setattr(HigherBimachineRuntime, "point", forbidden)
    monkeypatch.setattr(RecursiveCoordinateMorphismArena, "temporal", forbidden)
    if family == "collatz":
        from number_compiler.sequences.collatz import compilation

        monkeypatch.setattr(compilation, "compile_collatz_physical_power", forbidden)
    arguments = [family, "--nth", str(index)]
    if family == "collatz":
        arguments.extend(("--seed", "27"))
    assert main(arguments) == 0
    captured = capsys.readouterr()
    assert captured.out == f"{expected}\n"
    assert captured.err == ""

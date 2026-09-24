"""Output limits concern actual terminal digits, not a worst-case orbit bound."""

from __future__ import annotations

import pytest

from number_compiler.api import cli
from number_compiler.hashlife.execution.dyadic_return_images import (
    DyadicReturnImageWorkspace,
)
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm


@pytest.mark.parametrize(
    "steps,expected,bits",
    ((109, 4, 3), (110, 2, 2), (999999, 1, 1), (1000000, 4, 3), (10**26, 4, 3)),
)
def test_exact_terminal_width_controls_cli_budget(
    steps: int,
    expected: int,
    bits: int,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("cycle query invoked the causal executor")

    monkeypatch.setattr(CausalTileEngine, "__init__", forbidden)
    monkeypatch.setattr(DyadicReturnImageWorkspace, "branch_segments", forbidden)
    monkeypatch.setattr(DyadicReturnImageWorkspace, "leaf_summaries", forbidden)
    assert (
        cli.main(
            [
                "collatz",
                "--seed",
                "27",
                "--nth",
                str(steps),
                "--max-output-bits",
                str(bits),
            ]
        )
        == 0
    )
    captured = capsys.readouterr()
    assert captured.out == f"{expected}\n"
    assert captured.err == ""


def test_actual_oversized_terminal_still_refuses(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [
                "collatz",
                "--seed",
                "27",
                "--nth",
                "1000000",
                "--max-output-bits",
                "2",
            ]
        )
        == 2
    )
    captured = capsys.readouterr()
    assert captured.out == ""
    assert "output exceeds --max-output-bits" in captured.err


@pytest.mark.parametrize("steps,expected", ((0, "9"), (1, "28"), (2, "14"), (3, "7")))
def test_low_residue_match_is_not_exact_cycle_membership(
    steps: int, expected: str, capsys: pytest.CaptureFixture[str]
) -> None:
    assert cli.main(["collatz", "--seed", "9", "--nth", str(steps)]) == 0
    captured = capsys.readouterr()
    assert captured.out == expected + "\n"
    assert captured.err == ""


def test_reached_cycle_does_not_discover_a_million_branches() -> None:
    term = PoweredCollatzTerm(27, 1000000)
    assert term.materialize(max_bits=3) == 4
    workspace = term._workspace
    assert workspace is not None
    assert (
        sum(node.width for node in workspace.support if node.branch_word is not None)
        <= 256
    )
    assert len(workspace.support) <= 4 * term.steps.bit_length()
    clock = term.s_arithmetic_clock()
    assert (clock.events, clock.divisions) == (333338, 666662)


def test_symbolic_cycle_extent_is_not_charged_as_allocated_operand_bits() -> None:
    term = PoweredCollatzTerm(27, 10**26)
    assert term.materialize(max_bits=3) == 4
    counters = term._ledger.counters
    assert 0 < counters["collatz_physical_leaf_steps"] <= 256
    for name in (
        "transient_leaf_operand_bits",
        "transport_exact_operand_bits",
        "cycle_repeat_operand_bits",
    ):
        assert 0 < counters[f"collatz_physical_{name}"] < 100_000

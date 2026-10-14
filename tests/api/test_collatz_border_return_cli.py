"""The public Collatz route consumes authenticated 6305 border returns."""

from __future__ import annotations

import json
from collections.abc import Callable

import pytest

from number_compiler.api import cli
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz import temporal_border_return_execution
from number_compiler.sequences.collatz.border_return_grammar import (
    BorderReturnMacro,
    select_border_return_macro,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.tape_width import CollatzTapeWidthSummary
from number_compiler.sequences.collatz.temporal_dyadic import (
    D8CylinderFrame,
    D8TemporalTable,
)


@pytest.mark.usefixtures("isolated_process_cache")
@pytest.mark.parametrize(
    ("seed", "ticks", "endpoint", "exit_port"),
    (
        (13, 7, 4, "8_to_4"),
        (23, 13, 4, "8_to_4"),
        (43, 7, 74, "8_to_9_to_8"),
    ),
)
def test_public_cli_publishes_exact_6305_source_macro(
    seed: int,
    ticks: int,
    endpoint: int,
    exit_port: str,
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [
                "collatz",
                "--seed",
                str(seed),
                "--nth",
                str(ticks),
                "--no-value",
                "--info",
                "boundary-macro",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    assert packet["value"] is None
    boundary = packet["info"]["boundary-macro"]
    macro = boundary["first_executed_macro"]
    assert macro["family_word"] == "6305R"
    assert macro["source"] == seed
    assert macro["endpoint"] == endpoint
    assert macro["physical_ticks"] == ticks
    assert macro["exit_port"] == exit_port
    assert macro["starting_physical_tick"] == 0
    expected_returns = {13: ([6], [4]), 23: ([4, 8], [2, 6]), 43: ([4], [2])}
    physical, normalized = expected_returns[seed]
    assert macro["return_physical_ticks"] == physical
    assert macro["return_normalized_steps"] == normalized


@pytest.mark.usefixtures("isolated_process_cache")
@pytest.mark.parametrize(
    "seed,ticks,family,endpoint",
    (
        (30, 9, "0563", 80),
        (112, 6, "26847", 11),
        (592, 11, "26847", 11),
        (296, 10, "26847P1", 11),
        (148, 9, "26847P2", 11),
        (74, 8, "26847P3", 11),
        (37, 7, "26847P4", 11),
    ),
)
def test_public_cli_consumes_guarded_digit_cycle(
    seed: int,
    ticks: int,
    family: str,
    endpoint: int,
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [
                "collatz",
                "--seed",
                str(seed),
                "--nth",
                str(ticks),
                "--info",
                "boundary-macro",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    assert int(packet["value"]) == endpoint
    boundary = packet["info"]["boundary-macro"]
    macro = boundary["first_executed_macro"]
    assert macro["family_word"] == family
    assert macro["physical_ticks"] == ticks
    assert boundary["executed_macro_actions"][family] == 1


@pytest.mark.usefixtures("isolated_process_cache")
def test_public_composite_poison_checks_d8_after_source_bound_prefix(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    route: list[str] = []
    original_selector = select_border_return_macro
    original_transition = D8TemporalTable._transition

    def record_border(
        source: int,
        available_physical_ticks: int,
        *,
        max_returns: int = 64,
        minimum_useful_physical_ticks: int = 0,
        preflight: Callable[[int], None] | None = None,
        ledger: ResourceLedger | None = None,
    ) -> BorderReturnMacro | None:
        macro = original_selector(
            source,
            available_physical_ticks,
            max_returns=max_returns,
            minimum_useful_physical_ticks=minimum_useful_physical_ticks,
            preflight=preflight,
            ledger=ledger,
        )
        if macro is not None:
            route.append("6305R")
        return macro

    def record_d8(
        self: D8TemporalTable,
        frame: D8CylinderFrame,
        *,
        with_width: bool,
        with_joint: bool,
    ) -> tuple[
        D8CylinderFrame,
        int,
        int,
        int,
        CollatzTapeWidthSummary | None,
        DyadicTerminalFieldAction | None,
    ]:
        if "6305R" not in route:
            raise AssertionError("D8 was selected before a source-bound border return")
        route.append("D8")
        return original_transition(
            self, frame, with_width=with_width, with_joint=with_joint
        )

    monkeypatch.setattr(
        temporal_border_return_execution,
        "select_border_return_macro",
        record_border,
    )
    monkeypatch.setattr(D8TemporalTable, "_transition", record_d8)
    assert (
        cli.main(
            [
                "collatz",
                "--seed",
                "43",
                "--nth",
                "80",
                "--no-value",
                "--info",
                "boundary-macro",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    assert packet["value"] is None
    assert route[0] == "6305R"
    macro = packet["info"]["boundary-macro"]["first_executed_macro"]
    assert macro["source"] == 43
    assert macro["exit_port"] == "8_to_9_to_8"


@pytest.mark.usefixtures("isolated_process_cache")
def test_public_source_ending_in_nine_keeps_the_standalone_989_route(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [
                "collatz",
                "--seed",
                "19",
                "--nth",
                "4",
                "--no-value",
                "--info",
                "boundary-macro",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    assert packet["value"] is None
    macro = packet["info"]["boundary-macro"]["first_executed_macro"]
    assert macro["family_word"] == "989"
    assert macro["source"] == 19
    assert macro["endpoint"] == 44

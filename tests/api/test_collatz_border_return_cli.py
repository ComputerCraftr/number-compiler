"""The public Collatz route consumes authenticated 6305 border returns."""

from __future__ import annotations

import json
from collections.abc import Callable
from typing import cast

import pytest

from number_compiler.api import cli
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz import temporal_border_return_execution
from number_compiler.sequences.collatz.border_identity import BoundaryPathKind
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
                "temporal.macro",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    assert packet["value"] is None
    boundary = packet["info"]["temporal.macro"]
    macro = boundary["first_executed_macro"]
    assert macro["border"]["kind"] == "guarded-path"
    assert macro["border"]["path_kind"] == "three-border-return"
    assert macro["border"]["entry_digit"] == 3
    assert macro["border"]["exit_digit"] == 4
    expected_run_parameters = {13: [2], 23: [0, 4], 43: [0]}
    assert macro["border"]["run_parameters"] == expected_run_parameters[seed]
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
    "seed,ticks,entry_phase,endpoint",
    (
        (30, 9, 0, 80),
        (112, 6, 0, 11),
        (592, 11, 0, 11),
        (296, 10, 1, 11),
        (148, 9, 2, 11),
        (74, 8, 3, 11),
        (37, 7, 4, 11),
    ),
)
def test_public_cli_consumes_guarded_digit_cycle(
    seed: int,
    ticks: int,
    entry_phase: int,
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
                "temporal.macro",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    assert int(packet["value"]) == endpoint
    boundary = packet["info"]["temporal.macro"]
    macro = boundary["first_executed_macro"]
    assert macro["border"]["kind"] == "closed-cycle"
    assert macro["border"]["cycle"] == ([0, 5, 6, 3] if seed == 30 else [2, 6, 8, 4, 7])
    assert macro["border"]["entry_phase"] == entry_phase
    assert macro["physical_ticks"] == ticks
    assert sum(boundary["executed_macro_actions"].values()) == 1


@pytest.mark.usefixtures("isolated_process_cache")
def test_public_composite_poison_checks_d8_after_source_bound_prefix(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    route: list[BoundaryPathKind | str] = []
    original_selector = select_border_return_macro
    original_transition = cast(
        Callable[
            ...,
            tuple[
                D8CylinderFrame,
                int,
                int,
                int,
                CollatzTapeWidthSummary | None,
                DyadicTerminalFieldAction | None,
            ],
        ],
        object.__getattribute__(D8TemporalTable, "_transition"),
    )

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
            route.append(macro.identity.kind)
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
        if BoundaryPathKind.THREE_BORDER_RETURN not in route:
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
                "temporal.macro",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    assert packet["value"] is None
    assert route[0] is BoundaryPathKind.THREE_BORDER_RETURN
    macro = packet["info"]["temporal.macro"]["first_executed_macro"]
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
                "temporal.macro",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    assert packet["value"] is None
    macro = packet["info"]["temporal.macro"]["first_executed_macro"]
    assert macro["border"] == {
        "kind": "closed-cycle",
        "cycle": [8, 9],
        "entry_phase": 1,
        "entry_digit": 9,
        "selector_guard": [9, 10, 1],
        "run_parameters": [2],
        "display_label": "989",
    }
    assert macro["source"] == 19
    assert macro["endpoint"] == 44

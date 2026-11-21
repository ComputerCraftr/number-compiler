"""Public result categories select exact, independently demanded views."""

from __future__ import annotations

import json

import pytest

from number_compiler.api import cli
from number_compiler.api.cli_requests import parse_request
from number_compiler.api.observation_views import ObservationView
from number_compiler.sequences.double_reverse import (
    temporal_laurent_return,
    temporal_residue_quotient,
)
from tests.support.observation_views import view_value


def test_modular_only_omits_return_walk_and_accumulator(
    capsys: pytest.CaptureFixture[str],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("residue-only demand opened another view")

    monkeypatch.setattr(
        temporal_residue_quotient, "projected_residue_temporal_quotient", forbidden
    )
    monkeypatch.setattr(
        temporal_laurent_return, "source_laurent_accumulator_packet", forbidden
    )
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "196",
                "--nth",
                "64",
                "--no-value",
                "--info",
                "arithmetic.modular",
                "--format",
                "json",
            ]
        )
        == 0
    )
    info = json.loads(capsys.readouterr().out)["info"]
    assert set(info) == {"arithmetic.modular"}
    assert view_value(info["arithmetic.modular"], "residue")["target_mod198"] == 76


def test_repeated_kinds_and_unsupported_selection() -> None:
    request = parse_request(
        [
            "collatz",
            "--seed",
            "27",
            "--nth",
            "16",
            "--info",
            "temporal.accumulator",
            "--temporal-accumulator-kind",
            "single",
            "--temporal-accumulator-kind",
            "alternating",
            "--temporal-accumulator-kind",
            "single",
        ]
    )
    assert request is not None
    assert request.views == (ObservationView.SINGLE, ObservationView.ALTERNATING)
    with pytest.raises(ValueError, match="compatible observation view"):
        parse_request(
            [
                "collatz",
                "--seed",
                "27",
                "--nth",
                "16",
                "--info",
                "temporal.accumulator",
                "--temporal-accumulator-kind",
                "alternating",
                "--temporal-accumulator-modulus",
                "49",
            ]
        )


@pytest.mark.parametrize(
    "retired", ("temporal.residue99", "temporal.defect-clock", "temporal.seed-morphism")
)
def test_retired_observations_are_parser_errors(retired: str) -> None:
    with pytest.raises(SystemExit) as stopped:
        parse_request(["2rev10", "--nth", "64", "--info", retired])
    assert stopped.value.code == 2


def test_finite_safety_guard_explicit_and_empty(
    capsys: pytest.CaptureFixture[str],
) -> None:
    base = [
        "antihydra",
        "--nth",
        "8",
        "--no-value",
        "--info",
        "safety.ledger",
        "--format",
        "json",
    ]
    assert cli.main(base) == 0
    ordinary = json.loads(capsys.readouterr().out)["info"]["safety.ledger"]
    assert "views" not in ordinary
    assert cli.main([*base, "--safety-ledger-detail", "finite-guard"]) == 0
    detailed = json.loads(capsys.readouterr().out)["info"]["safety.ledger"]
    assert detailed["value"] == ordinary["value"]
    guard = view_value(detailed, "finite-guard")
    assert guard["steps"] == 8
    assert guard["complete"] is True
    assert guard["status"] == "available"
    assert guard["admitted_interval"] == {
        "lower": {"numerator": 0, "denominator": 1},
        "upper": {"numerator": 0, "denominator": 1},
    }


def test_executed_macro_view_reports_the_live_collatz_path(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [
                "collatz",
                "--seed",
                "1486",
                "--nth",
                "24",
                "--info",
                "temporal.macro",
                "--temporal-macro-kind",
                "executed",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    assert packet["value"] == "5366"
    coverage = view_value(packet["info"]["temporal.macro"], "executed")
    ticks = coverage["physical_ticks"]
    assert coverage["actions"] == 1
    assert type(ticks) is int and 0 < ticks <= 24

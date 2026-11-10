"""Explicit CLI detail demands consume the authenticated radix owner."""

from __future__ import annotations

import json

import pytest

from number_compiler.api import cli
from number_compiler.arithmetic.fields.three_power_radix import ThreePowerRadixOrbit
from number_compiler.sequences.antihydra.mahler_source_actions import (
    MahlerSourceBoundSafetyAction,
)


def test_mahler_cli_demands_source_bound_radix6(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("aggregate CLI ports must not construct boundary rows")

    monkeypatch.setattr(ThreePowerRadixOrbit, "tape", forbidden)
    assert (
        cli.main(
            [
                "antihydra",
                "--nth",
                "16",
                "--no-value",
                "--info",
                "arithmetic.mahler",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    port = packet["info"]["arithmetic.mahler"]["value"]["associated_action"][
        "source_bound_radix6_difference"
    ]
    assert port["base"] == 6
    assert port["source_extent"] == 16


def test_antihydra_metrics_do_not_demand_radix_ports(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("metrics must not construct optional radix projections")

    monkeypatch.setattr(
        MahlerSourceBoundSafetyAction, "demanded_tripling_ports", forbidden
    )
    assert (
        cli.main(
            [
                "antihydra",
                "--nth",
                "16",
                "--no-value",
                "--info",
                "metrics",
                "--format",
                "json",
            ]
        )
        == 0
    )
    assert json.loads(capsys.readouterr().out)["value"] is None

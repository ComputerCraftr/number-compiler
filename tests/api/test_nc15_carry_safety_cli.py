"""Carry safety is an explicit finite source demand, not a future oracle."""

import json
from typing import Never

import pytest

from number_compiler.api import cli
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm


def _no_global_graph(*args: object, **kwargs: object) -> Never:
    raise AssertionError("CLI carry demand constructed the global border graph")


def test_carry_cli_uses_source_constraints_without_endpoint(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr(DoubleReverseTerm, "prepare_endpoint", _no_global_graph)
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "173488",
                "--nth",
                "0",
                "--no-value",
                "--info",
                "temporal.carry-safety",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    safety = packet["info"]["temporal.carry-safety"]
    assert packet["value"] is None
    assert safety["prefix_steps"] == 0
    assert safety["source_safety"]["current_forced_carry"] == 0
    assert safety["source_safety"]["next_forced_carry"] == 1
    assert safety["source_safety"]["exact_width_change"] == 1
    assert safety["source_safety"]["unconditional_entry_or_shrink_bound"] is None


def test_short_source_reports_unavailable_without_endpoint(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr(DoubleReverseTerm, "prepare_endpoint", _no_global_graph)
    arguments = [
        "2rev10",
        "--seed",
        "1",
        "--nth",
        "0",
        "--no-value",
        "--info",
        "temporal.carry-safety",
        "--format",
        "json",
    ]
    assert cli.main(arguments) == 3
    result = json.loads(capsys.readouterr().out)
    assert result["value"] is None
    assert result["info"]["temporal.carry-safety"]["status"] == "unavailable"

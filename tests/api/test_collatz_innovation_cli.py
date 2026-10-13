from number_compiler.api import cli_render

"""Guarded innovation observations share admission without demanding sums."""

import json

import pytest

from number_compiler.api import cli
from number_compiler.api.cli_requests import parse_request
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from tests.support.assertions import forbid_explicit_lowering


@pytest.mark.parametrize("modulus", (2, 4, 4097))
def test_innovation_rejects_unsupported_modulus_before_construction(
    modulus: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(PoweredCollatzTerm, "__init__", forbid_explicit_lowering)
    with pytest.raises(ValueError, match="odd modulus"):
        parse_request(
            [
                "collatz",
                "--seed",
                "27",
                "--nth",
                "16",
                "--info",
                "innovation-borrow",
                "--modulus",
                str(modulus),
            ]
        )


@pytest.mark.parametrize("name", ("boundary-macro", "innovation-borrow"))
def test_guarded_observation_does_not_demand_accumulator_or_render(
    name: str, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr(
        PoweredCollatzTerm, "prepare_joint_cocycle", forbid_explicit_lowering
    )
    monkeypatch.setattr(cli_render, "_render_value", forbid_explicit_lowering)
    assert (
        cli.main(
            [
                "collatz",
                "--seed",
                "2174",
                "--nth",
                "13",
                "--no-value",
                "--info",
                name,
                "--format",
                "json",
            ]
        )
        == 0
    )
    result = json.loads(capsys.readouterr().out)
    observation = result["info"][name]
    assert result["value"] is None
    assert observation["index_unit"] == "physical_iterations"
    assert observation["first_executed_macro"] is not None


def test_value_and_innovation_keep_physical_endpoint(
    capsys: pytest.CaptureFixture[str],
) -> None:
    expected = 2174
    for _ in range(13):
        expected = 3 * expected + 1 if expected & 1 else expected // 2
    assert (
        cli.main(
            [
                "collatz",
                "--seed",
                "2174",
                "--nth",
                "13",
                "--info",
                "innovation-borrow",
                "--modulus",
                "49",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    assert packet["value"] == str(expected)
    assert packet["info"]["innovation-borrow"]["index"] == 13


def test_ordinary_value_does_not_prepare_innovation(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr(
        PoweredCollatzTerm, "prepare_innovation_tape", forbid_explicit_lowering
    )
    assert cli.main(["collatz", "--seed", "27", "--nth", "2"]) == 0
    assert capsys.readouterr().out.strip() == "41"

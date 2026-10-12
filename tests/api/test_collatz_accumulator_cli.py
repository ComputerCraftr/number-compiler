"""Explicit normalized accumulator demands share physical query admission."""

import json

import pytest

from number_compiler.api import cli
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.collatz.joint_temporal_action import JointTemporalSpine
from tests.support.assertions import forbid_explicit_lowering


@pytest.mark.parametrize("seed", (1, 16, 27))
@pytest.mark.parametrize("ticks", (0, 1, 2, 17))
def test_accumulator_cli_preserves_normalized_and_physical_clocks(
    seed: int, ticks: int, capsys: pytest.CaptureFixture[str]
) -> None:
    current, consumed, total, pending = seed, 0, seed, 0
    while consumed < ticks:
        if current & 1:
            current = 3 * current + 1
            consumed += 1
            if consumed == ticks:
                pending = 1
                break
        current //= 2
        consumed += 1
        total += current
    assert (
        cli.main(
            [
                "collatz",
                "--seed",
                str(seed),
                "--nth",
                str(ticks),
                "--info",
                "accumulator",
                "--modulus",
                "49",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    assert packet["value"] == str(current)
    observation = packet["info"]["accumulator"]
    assert observation["normalized_accumulator_residue"] == total % 49
    assert observation["source_included"] is True
    assert observation["modulus"] == 49
    assert observation["phase"] == pending
    assert observation["physical_ticks"] == ticks


def test_ordinary_collatz_query_does_not_request_accumulator(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr(
        PoweredCollatzTerm, "prepare_joint_cocycle", forbid_explicit_lowering
    )
    monkeypatch.setattr(PoweredCollatzTerm, "accumulator", forbid_explicit_lowering)
    monkeypatch.setattr(JointTemporalSpine, "__init__", forbid_explicit_lowering)
    assert cli.main(["collatz", "--seed", "27", "--nth", "2"]) == 0
    assert capsys.readouterr().out.strip() == "41"


def test_accumulator_information_does_not_render_digits(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr(cli, "_render_value", forbid_explicit_lowering)
    assert (
        cli.main(
            [
                "collatz",
                "--seed",
                "27",
                "--nth",
                "17",
                "--no-value",
                "--info",
                "accumulator",
                "--format",
                "json",
            ]
        )
        == 0
    )
    assert json.loads(capsys.readouterr().out)["value"] is None

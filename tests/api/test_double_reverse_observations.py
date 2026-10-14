"""Demanded carry moments use the production endpoint and compact CLI metadata."""

from __future__ import annotations

import json

import pytest

from number_compiler.api import cli, cli_render
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm


def _forbidden(*args: object, **kwargs: object) -> None:
    raise AssertionError("an unrequested 2rev10 observer or renderer ran")


def test_closed_form_cli_reads_exact_and_modular_endpoint_ports(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr(cli_render, "_render_value", _forbidden)
    arguments = [
        "2rev10",
        "--seed",
        "173488",
        "--nth",
        "4",
        "--no-value",
        "--info",
        "closed-form",
        "--format",
        "json",
    ]
    assert cli.main(arguments) == 0
    exact = json.loads(capsys.readouterr().out)
    assert exact["value"] is None
    port = exact["info"]["closed-form"]
    assert port["source"] == 173488
    assert port["target"] == 17631568
    assert port["carry_word"] == 10011
    assert port["carry_correction"] == -99109
    assert port["U"] == 85629300
    assert port["H"] == 17631568 // 2 - 884371
    assert port["matrix"][0] == [0, 2, 2 * port["H"]]
    assert port["affine_gain"] == 160
    assert port["phase_in"] == port["phase_out"] == 0

    assert cli.main([*arguments, "--modulus", "97"]) == 0
    modular = json.loads(capsys.readouterr().out)["info"]["closed-form"]
    for field in ("source", "target", "carry_correction", "U", "H"):
        assert modular[field] == port[field] % 97
    assert modular["carry_word"] == port["carry_word"] % 970
    assert modular["carry_word_modulus"] == 970


def test_metrics_alone_do_not_construct_closed_form_ports(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr(DoubleReverseTerm, "temporal_closed_form", _forbidden)
    monkeypatch.setattr(cli_render, "_render_value", _forbidden)
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "196",
                "--nth",
                "128",
                "--no-value",
                "--info",
                "metrics",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    assert packet["value"] is None
    assert set(packet["info"]) == {"metrics"}


def test_closed_form_compact_index_has_no_expanded_request_coordinate(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "12",
                "--nth-power10",
                "0",
                "--no-value",
                "--info",
                "closed-form",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    port = packet["info"]["closed-form"]
    assert (
        packet["index"]
        == port["index"]
        == port["steps"]
        == {
            "encoding": "power10",
            "exponent": 0,
        }
    )
    assert port["target"] == 42


@pytest.mark.parametrize("seed,expected", ((10, 4), (100, 4), (50, 2)))
def test_closed_form_retains_decimal_contraction(
    seed: int,
    expected: int,
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                str(seed),
                "--nth",
                "2",
                "--no-value",
                "--info",
                "closed-form",
                "--format",
                "json",
            ]
        )
        == 0
    )
    port = json.loads(capsys.readouterr().out)["info"]["closed-form"]
    assert port["target"] == expected
    assert port["phase_in"] is None
    assert port["affine_gain"] is None


@pytest.mark.parametrize("value", ("0", "-1"))
def test_closed_form_modulus_is_validated_at_cli_boundary(
    value: str,
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "12",
                "--nth",
                "1",
                "--no-value",
                "--info",
                "closed-form",
                "--modulus",
                value,
            ]
        )
        == 2
    )
    assert capsys.readouterr().out == ""


def test_closed_form_rejects_fractional_modulus() -> None:
    with pytest.raises(SystemExit) as stopped:
        cli.main(
            [
                "2rev10",
                "--seed",
                "12",
                "--nth",
                "1",
                "--no-value",
                "--info",
                "closed-form",
                "--modulus",
                "1.5",
            ]
        )
    assert stopped.value.code == 2

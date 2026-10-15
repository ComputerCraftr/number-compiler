"""Pointed cylinder observations must not construct an unrequested endpoint."""

import json

import pytest

from number_compiler.api import cli, cli_render
from number_compiler.api.cli_requests import parse_request
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm


def _forbid_endpoint(*args: object, **kwargs: object) -> None:
    raise AssertionError("pointed observation reconstructed the complete endpoint")


def test_pointed_cli_matches_literal_without_endpoint_rendering(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    value = 196
    for _ in range(64):
        value = 2 * int(str(value)[::-1])
    monkeypatch.setattr(cli_render, "_render_value", _forbid_endpoint)
    monkeypatch.setattr(DoubleReverseTerm, "materialize", _forbid_endpoint)
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
                "spatial.stencil",
                "--spatial-stencil-position",
                "3",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    stencil = packet["info"]["spatial.stencil"]
    assert packet["value"] is None
    assert stencil["digit"] == (value // 1000) % 10
    assert stencil["width"] == len(str(value))
    assert stencil["position_unit"] == "lsd_digit"
    assert "source" not in stencil


def test_temporal_bank_keeps_conditional_bounds_separate(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr(cli_render, "_render_value", _forbid_endpoint)
    monkeypatch.setattr(DoubleReverseTerm, "materialize", _forbid_endpoint)
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
                "temporal.bank",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    bank = packet["info"]["temporal.bank"]
    assert bank["prefix_steps"] == 16
    rows = {row["observer"]: row for row in bank["envelopes"]}
    assert rows["growth"]["exact_sum"] == 24
    assert rows["carry_edge"]["exact_sum"] == 384
    assert rows["reflected_xor"]["exact_sum"] == 72
    for row in rows.values():
        if row["minimum_emission_sum"] != row["maximum_emission_sum"]:
            assert row["exact_sum"] is None
        if len(row["possible_next_outputs"]) != 1:
            assert row["forced_next_output"] is None


@pytest.mark.parametrize(
    "extra",
    (
        ["--spatial-stencil-position", "-1", "--info", "spatial.stencil"],
        ["--spatial-stencil-position", "0", "--info", "metrics"],
    ),
)
def test_stencil_position_requires_its_observer_and_nonnegative_input(
    extra: list[str],
) -> None:
    with pytest.raises(ValueError):
        parse_request(["2rev10", "--seed", "196", "--nth", "64", *extra])


def test_unadmitted_stencil_keeps_compact_index_and_null_value(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "0",
                "--nth-power10",
                "1",
                "--no-value",
                "--info",
                "spatial.stencil",
                "--format",
                "json",
            ]
        )
        == 3
    )
    packet = json.loads(capsys.readouterr().out)
    assert packet["value"] is None
    assert packet["index"] == {"encoding": "power10", "exponent": 1}
    stencil = packet["info"]["spatial.stencil"]
    assert stencil["index"] == packet["index"]
    assert stencil["status"] == "unavailable"
    assert "digit" not in stencil


def test_closed_form_retains_certified_suffix_from_non_cylinder_seed(
    capsys: pytest.CaptureFixture[str],
) -> None:
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
                "temporal.closed-form",
                "--format",
                "json",
            ]
        )
        == 0
    )
    form = json.loads(capsys.readouterr().out)["info"]["temporal.closed-form"]
    assert form["phase_in"] is None
    assert form["affine_gain"] is None
    assert form["prefix_steps"] == 16
    assert form["entry_value"] == 173488
    assert form["suffix_steps"] == 48
    assert form["suffix_phase_in"] == form["suffix_phase_out"] == 0
    assert form["suffix_affine_gain"] == 160**12
    assert form["target"] == (
        form["suffix_affine_gain"] * form["entry_value"] + form["suffix_affine_shift"]
    )


def test_pair_bank_uses_final_coordinates_without_endpoint(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    monkeypatch.setattr(DoubleReverseTerm, "prepare_endpoint", _forbid_endpoint)
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
                "spatial.pair-bank",
                "--spatial-pair-bank-position",
                "1",
                "--format",
                "json",
            ]
        )
        == 0
    )
    pair = json.loads(capsys.readouterr().out)["info"]["spatial.pair-bank"]
    assert pair["digits"] == [7, 8]
    assert pair["pair"] == 15
    assert pair["gt_high"] == 1
    assert pair["position_unit"] == "final_outer_to_inner_pair"


def test_periodic_grammar_cli_publishes_finite_halo_and_exact_counts(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    monkeypatch.setattr(DoubleReverseTerm, "prepare_endpoint", _forbid_endpoint)
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "17" + "48" * 30 + "88",
                "--nth",
                "20",
                "--no-value",
                "--info",
                "temporal.grammar",
                "--temporal-grammar-position",
                "20",
                "--temporal-grammar-period",
                "2",
                "--format",
                "json",
            ]
        )
        == 0
    )
    bank = json.loads(capsys.readouterr().out)["info"]["temporal.grammar"]
    assert bank["f_steps"] == 10
    assert bank["repeat_count"] > 0
    assert (
        sum(
            bank["counts"][band]
            for band in ("lt_low", "lt_high", "eq", "gt_low", "gt_high")
        )
        == 10
    )
    assert bank["position_unit"] == "entry_outer_to_inner_pair"
    assert bank["region_unit"] == "entry_source_half_open_digits"
    assert "source" not in bank

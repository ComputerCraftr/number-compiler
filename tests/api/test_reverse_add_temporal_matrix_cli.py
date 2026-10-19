"""Requested reverse moments reuse exact output; modular demands stay bounded."""

import json

import pytest

from number_compiler.api import cli, cli_render
from number_compiler.api.cli_requests import parse_request
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def _no_render(*args: object, **kwargs: object) -> None:
    raise AssertionError("information-only request rendered an exact integer")


def test_reverse_matrix_matches_independent_twenty_step_endpoint(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [
                "reverse-add",
                "--seed",
                "196",
                "--nth",
                "20",
                "--no-value",
                "--info",
                "temporal.matrix",
                "--temporal-matrix-kind",
                "innovation",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    action = packet["info"]["temporal.matrix"]
    assert packet["value"] is None
    assert action["source"] == 196
    assert action["target"] == 70446464506
    assert action["moment"] == {
        "duration": 20,
        "U": int(str(70446464506)[::-1]) - 691,
        "V": 70446464506 - 196 - 20 * 691,
        "modulus": None,
    }


def test_modular_reverse_matrix_never_materializes_the_endpoint(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    monkeypatch.setattr(cli_render, "render_value", _no_render)
    monkeypatch.setattr(ReverseAddPoweredTerm, "temporal_matrix", _no_render)
    assert (
        cli.main(
            [
                "reverse-add",
                "--seed",
                "196",
                "--nth-power10",
                "1",
                "--no-value",
                "--info",
                "temporal.matrix",
                "--temporal-matrix-kind",
                "innovation",
                "--temporal-matrix-modulus",
                "1009",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    moment = packet["info"]["temporal.matrix"]
    value = 196
    for _ in range(10):
        value += int(str(value)[::-1])
    assert moment["U"] == (int(str(value)[::-1]) - 691) % 1009
    assert moment["V"] == (value - 196 - 10 * 691) % 1009
    assert moment["duration"] == {"encoding": "power10", "exponent": 1}
    assert packet["value"] is None


def test_reverse_stencil_budget_refuses_before_observing(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    monkeypatch.setattr(ReverseAddPoweredTerm, "temporal_stencil", _no_render)
    assert (
        cli.main(
            [
                "reverse-add",
                "--seed",
                "196",
                "--nth",
                "20",
                "--no-value",
                "--info",
                "temporal.stencil",
                "--max-digits",
                "2",
            ]
        )
        == 2
    )
    assert "budget" in capsys.readouterr().err


def test_reverse_temporal_observers_reject_nondecimal_sources() -> None:
    with pytest.raises(ValueError, match="decimal"):
        parse_request(
            [
                "reverse-add",
                "--seed",
                "196",
                "--base",
                "2",
                "--nth",
                "2",
                "--info",
                "temporal.matrix",
                "--temporal-matrix-kind",
                "innovation",
            ]
        )


def test_bounded_stencil_packet_keeps_the_joint_pair_bands(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [
                "reverse-add",
                "--seed",
                "79",
                "--nth",
                "1",
                "--no-value",
                "--info",
                "temporal.stencil",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    stencil = packet["info"]["temporal.stencil"]
    assert packet["value"] is None
    assert stencil["width"] == 3  # 79 + 97 = 176; symmetric sums 7, 14, 7.
    assert stencil["lt_high_mask"] == 0b101
    assert stencil["gt_low_mask"] == 0b010
    assert stencil["lt_low_mask"] == stencil["eq_mask"] == stencil["gt_high_mask"] == 0

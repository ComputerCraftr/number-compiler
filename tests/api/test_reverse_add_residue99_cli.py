"""Public mod-99 predictive observation must not demand any Q19 image."""

from __future__ import annotations

import json

import pytest

from number_compiler.api import cli, cli_render
from number_compiler.api.cli_requests import parse_request
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def test_reverse_add_temporal_residue99_cli_is_predictive(
    capsys: pytest.CaptureFixture[str], monkeypatch: pytest.MonkeyPatch
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("no whole-number publisher is permitted")

    monkeypatch.setattr(cli_render, "_render_value", forbidden)
    monkeypatch.setattr(ReverseAddPoweredTerm, "_source_workspace", forbidden)
    assert (
        cli.main(
            [
                "reverse-add",
                "--seed",
                "196",
                "--nth",
                str(10**12),
                "--no-value",
                "--info",
                "temporal.residue99",
                "--format",
                "json",
            ]
        )
        == 0
    )
    result = json.loads(capsys.readouterr().out)
    packet = result["info"]["temporal.residue99"]
    assert result["value"] is None
    assert packet["target_mod99"] == 22
    assert packet["source_certified"] is True
    assert packet["complete_integer_certified"] is False


def test_nondecimal_source_rejected_before_term_execution() -> None:
    with pytest.raises(ValueError, match="decimal"):
        parse_request(
            [
                "reverse-add",
                "--seed",
                "196",
                "--base",
                "19",
                "--nth",
                "7",
                "--info",
                "temporal.residue99",
            ]
        )

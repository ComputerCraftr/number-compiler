"""Public mod-99 predictive observation must not demand any Q19 image."""

from __future__ import annotations

import json

import pytest

from number_compiler.api import cli, cli_render
from number_compiler.api.cli_requests import parse_request
from number_compiler.api.number_api import NumberCompiler
from tests.support.observation_views import information_only_view


@pytest.mark.parametrize(
    ("selector", "value"), (("--nth", str(10**12)), ("--nth-power10", "12"))
)
def test_reverse_add_temporal_residue99_cli_is_predictive(
    selector: str,
    value: str,
    capsys: pytest.CaptureFixture[str],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("no whole-number publisher is permitted")

    monkeypatch.setattr(cli_render, "render_value", forbidden)
    monkeypatch.setattr(NumberCompiler, "project", forbidden)
    assert (
        cli.main(
            [
                "reverse-add",
                "--seed",
                "196",
                selector,
                value,
                "--no-value",
                "--info",
                "arithmetic.modular",
                "--arithmetic-modular-kind",
                "residue",
                "--format",
                "json",
            ]
        )
        == 0
    )
    result = json.loads(capsys.readouterr().out)
    packet = information_only_view(result, "arithmetic.modular", "residue")
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
                "arithmetic.modular",
                "--arithmetic-modular-kind",
                "residue",
            ]
        )

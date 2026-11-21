"""The numerical future is predicted from a certified source, not an endpoint."""

from __future__ import annotations

import json

import pytest

from number_compiler.api import cli
from tests.support.observation_views import information_only_view


def test_cli_source_only_residue99_closed_form(
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
                "arithmetic.modular",
                "--arithmetic-modular-kind",
                "residue",
                "--format",
                "json",
            ]
        )
        == 0
    )
    data = json.loads(capsys.readouterr().out)
    port = information_only_view(data, "arithmetic.modular", "residue")
    assert port["prefix_steps"] == 16
    assert port["duration"] == 48
    assert port["width_out"] == 30
    assert port["target_mod99"] == 76
    assert port["target_mod198"] == 76
    assert port["moore_classes99"] == 729
    assert port["moore_classes198"] == 1458

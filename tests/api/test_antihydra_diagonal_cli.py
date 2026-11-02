"""Demanded diagonal fields share the published arithmetic source."""

from __future__ import annotations

import json
import subprocess
import sys

import pytest

from number_compiler.api.cli import main
from number_compiler.api.cli_requests import parse_request
from number_compiler.api.cli_types import AntihydraObservationOptions
from number_compiler.api.observation_types import ObservationId


def test_antihydra_metadata_does_not_import_detailed_observers() -> None:
    program = """
import sys
import number_compiler.api.antihydra_adapters
assert 'number_compiler.sequences.antihydra.mahler' not in sys.modules
assert 'number_compiler.sequences.antihydra.observers' not in sys.modules
assert 'number_compiler.sequences.antihydra.mahler_diagonal_carry' not in sys.modules
"""
    subprocess.run([sys.executable, "-c", program], check=True, capture_output=True)


def test_full_diagonal_width_does_not_authorize_other_zero_width_observers() -> None:
    request = parse_request(
        [
            "antihydra",
            "--nth",
            "16",
            "--info",
            "temporal.diagonal-carry",
            "--spatial-width",
            "0",
        ]
    )
    assert request is not None
    with pytest.raises(ValueError, match="full spatial width"):
        AntihydraObservationOptions(
            info=(ObservationId.TEMPORAL_DIAGONAL_CARRY, ObservationId.SPATIAL_TAPE),
            width=0,
        )


@pytest.mark.parametrize("steps", [0, 4, 65, 128, 3072])
def test_diagonal_cli_uses_exact_published_endpoint(
    steps: int, capsys: pytest.CaptureFixture[str]
) -> None:
    assert (
        main(
            [
                "antihydra",
                "--nth",
                str(steps),
                "--no-value",
                "--info",
                "temporal.diagonal-carry",
                "--spatial-width",
                "0",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)["info"]["temporal.diagonal-carry"]
    expected = 8
    for _ in range(steps):
        expected += expected // 2
    assert packet["endpoint"] == expected
    assert packet["requested_returns"] == steps
    assert packet["all_time_claim"] is False


def test_diagonal_cli_enforces_output_cap(capsys: pytest.CaptureFixture[str]) -> None:
    assert (
        main(
            [
                "antihydra",
                "--nth",
                "128",
                "--no-value",
                "--info",
                "temporal.diagonal-carry",
                "--spatial-width",
                "0",
                "--max-observer-terms",
                "1",
                "--format",
                "json",
            ]
        )
        != 0
    )
    capsys.readouterr()

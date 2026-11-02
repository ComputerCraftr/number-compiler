"""The diagonal consumer shares the issued run and distinguishes its clocks."""

import json
import subprocess
import sys

import pytest

from number_compiler.api.cli import main


def test_collatz_metadata_keeps_diagonal_projection_lazy() -> None:
    subprocess.run(
        [
            sys.executable,
            "-c",
            "import sys; import number_compiler.api.family_registry; "
            "assert 'number_compiler.sequences.collatz.diagonal_carry_action' "
            "not in sys.modules",
        ],
        check=True,
        capture_output=True,
    )


@pytest.mark.parametrize("ticks", [0, 1, 2, 17, 64])
def test_diagonal_cli_preserves_physical_endpoint_and_half_step(
    ticks: int, capsys: pytest.CaptureFixture[str]
) -> None:
    assert (
        main(
            [
                "collatz",
                "--seed",
                "27",
                "--nth",
                str(ticks),
                "--no-value",
                "--info",
                "temporal.diagonal-carry",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)["info"]["temporal.diagonal-carry"]
    expected = 27
    for _ in range(ticks):
        expected = 3 * expected + 1 if expected & 1 else expected // 2
    assert packet["physical_endpoint"] == expected
    assert packet["physical_ticks"] == ticks
    assert packet["all_time_claim"] is False
    normalized = packet["normalized_endpoint"]
    assert expected == (3 * normalized + 1 if packet["phase"] else normalized)
    assert (
        sum(bit << position for position, bit in enumerate(packet["field"]["digits"]))
        == normalized
    )
    assert packet["complete"] is True
    assert packet["weighted_laurent_complete"] is True


def test_diagonal_cli_reports_bounded_prefix_as_incomplete(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        main(
            [
                "collatz",
                "--seed",
                "27",
                "--nth",
                "17",
                "--no-value",
                "--info",
                "temporal.diagonal-carry",
                "--temporal-clock-max-digits",
                "2",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)["info"]["temporal.diagonal-carry"]
    assert packet["field_width"] == 2
    assert packet["complete"] is False
    assert packet["weighted_laurent_complete"] is False
    assert packet["weighted_laurent_aggregate"] is None

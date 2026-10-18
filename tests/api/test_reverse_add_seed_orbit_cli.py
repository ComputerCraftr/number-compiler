"""Public reverse/add source-root Q19 squaring, not unproved fast powering."""

from __future__ import annotations

import json

import pytest

from number_compiler.api import cli
from number_compiler.api.cli_requests import parse_request
from tests.support.reverse_add_source_data import iterate_reverse_add


@pytest.mark.parametrize("seed,n", [(196, 5), (196, 65), (1, 33), (99, 19)])
def test_source_bound_cli_outputs_actual_center_and_carry_ports(
    seed: int,
    n: int,
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [
                "reverse-add",
                "--seed",
                str(seed),
                "--nth",
                str(n),
                "--no-value",
                "--info",
                "temporal.seed-orbit",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    record = packet["info"]["temporal.seed-orbit"]
    value = iterate_reverse_add(seed, n)
    digits = str(value)
    center = digits[
        (len(digits) - len(record["center_out"])) // 2 : (
            len(digits) + len(record["center_out"])
        )
        // 2
    ]
    assert "".join(map(str, record["center_out"])) == center
    assert record["mod99_out"] == value % 99
    assert record["mod198_out"] == value % 198
    assert record["q19_block_applications"] > 0
    assert record["temporal_square_operations"] == 0
    assert record["temporal_square_from_actual_root"] is False
    assert record["terminal_occurrence_reused"] is False
    assert record["whole_word_slp_certified"]
    assert not record["logarithmic_q19_power_certified"]
    assert record["status"] == "available"
    assert packet["value"] is None


@pytest.mark.parametrize("n", [0, 1, 4098, 10**10])
def test_cli_does_not_pretend_to_power_unbounded_future(
    n: int,
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [
                "reverse-add",
                "--seed",
                "196",
                "--nth",
                str(n),
                "--no-value",
                "--info",
                "temporal.seed-orbit",
                "--format",
                "json",
            ]
        )
        == 3
    )
    packet = json.loads(capsys.readouterr().out)["info"]["temporal.seed-orbit"]
    assert packet["status"] == "unavailable"
    assert not packet["logarithmic_q19_power_certified"]


def test_nondecimal_cli_sees_quarantined_q19_port_before_execution() -> None:
    with pytest.raises(ValueError, match="decimal"):
        parse_request(
            [
                "reverse-add",
                "--seed",
                "196",
                "--base",
                "19",
                "--nth",
                "15",
                "--info",
                "temporal.seed-orbit",
            ]
        )

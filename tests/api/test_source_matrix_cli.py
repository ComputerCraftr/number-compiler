"""Independent endpoint fixtures for the unified family matrix consumers."""

import json

import pytest

from number_compiler.api.cli import main


@pytest.mark.parametrize(
    ("seed", "index", "source", "endpoint"), [(7, 0, 7, 11), (11, 2, 17, 26)]
)
def test_collatz_matrix_starts_at_main_query_endpoint(
    seed: int,
    index: int,
    source: int,
    endpoint: int,
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        main(
            [
                "collatz",
                "--seed",
                str(seed),
                "--nth",
                str(index),
                "--info",
                "temporal.matrix",
                "--temporal-matrix-steps",
                "2",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    matrix = packet["info"]["temporal.matrix"]
    assert int(packet["value"]) == source
    assert matrix["status"] == "available"
    assert (matrix["source"], matrix["endpoint"]) == (source, endpoint)
    assert matrix["physical_ticks"] == 2
    assert matrix["normalized_steps"] == 1
    assert matrix["execution_authority"] is False


def test_fermat_source_matrix_keeps_ordered_carry_without_primality_claim(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        main(
            [
                "fermat",
                "--nth",
                "2",
                "--info",
                "temporal.matrix.trace",
                "--temporal-matrix-steps",
                "3",
                "--temporal-matrix-digit-position",
                "1",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    matrix = packet["info"]["temporal.matrix.trace"]
    assert packet["value"] == "17"
    assert matrix["source_level"] == 3
    assert matrix["trace"]["digits"] == [6, 8, 4, 4]
    assert matrix["trace"]["carry_in"] == [0, 0, 2]
    assert matrix["trace"]["carry_out"] == [1, 2, 1]
    assert matrix["primality_authority"] is False
    assert matrix["complete_signed_fold_certified"] is False


def test_collatz_matrix_trace_uses_admitted_parity_prefix(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        main(
            [
                "collatz",
                "--seed",
                "7",
                "--nth",
                "0",
                "--no-value",
                "--info",
                "temporal.matrix.trace",
                "--temporal-matrix-steps",
                "2",
                "--format",
                "json",
            ]
        )
        == 0
    )
    matrix = json.loads(capsys.readouterr().out)["info"]["temporal.matrix.trace"]
    assert matrix["trace"]["parity"] == [1]
    assert matrix["trace"]["physical_ticks"] == {"value": 2, "unit": "physical-ticks"}
    assert matrix["trace"]["endpoint_mod5"] == 11 % 5
    assert matrix["clocks"]["odd_events"]["value"] == 1

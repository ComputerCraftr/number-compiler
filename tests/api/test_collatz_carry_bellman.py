"""Exercise carry observations at the receiving CLI source."""

import json

import pytest

from number_compiler.api.cli import main
from number_compiler.arithmetic.contracts.input_validation import string_keyed_mapping
from number_compiler.sequences.collatz import future_carry_bellman
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm


@pytest.mark.parametrize(
    ("cuts", "precision", "numerator", "plain_hit", "corrected_hit"),
    (("2,3", 4, 8, 2, None), ("6", 7, 104, 1, 2)),
)
def test_carry_bellman_uses_the_selected_endpoint(
    cuts: str,
    precision: int,
    numerator: int,
    plain_hit: int,
    corrected_hit: int | None,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    def forbid(_term: PoweredCollatzTerm) -> None:
        pytest.fail("carry signal rebuilt the historical joint action")

    monkeypatch.setattr(PoweredCollatzTerm, "prepare_joint_cocycle", forbid)
    assert (
        main(
            [
                "collatz",
                "--seed",
                "7",
                "--nth",
                "2",
                "--no-value",
                "--info",
                "temporal.carry-bellman",
                "--temporal-bellman-cuts",
                cuts,
                "--temporal-bellman-horizon",
                "2",
                "--format",
                "json",
            ]
        )
        == 0
    )
    response = string_keyed_mapping(json.loads(capsys.readouterr().out))
    assert response is not None
    information = string_keyed_mapping(response["info"])
    assert information is not None
    bellman = string_keyed_mapping(information["temporal.carry-bellman"])
    assert bellman is not None
    assert bellman["law"] == "homogeneous-centered-carry"
    assert bellman["multipliers"] == [3, 5, 15]
    assert bellman["normalized_source"] == 11
    assert bellman["first_normalized_offset"] == plain_hit
    assert bellman["first_physical_offset"] == 2 * plain_hit
    assert bellman["corrected"] == {
        "law": "centered-minus-power-of-two",
        "numerator_bits": precision,
        "terminal_numerator_residue": numerator,
        "first_normalized_offset": corrected_hit,
        "first_physical_offset": None if corrected_hit is None else 2 * corrected_hit,
    }


@pytest.mark.parametrize(("index", "horizon"), ((1, 0), (1, 1), (2, 3)))
def test_carry_bellman_rejects_unadmitted_normalized_suffix(
    index: int, horizon: int, capsys: pytest.CaptureFixture[str]
) -> None:
    assert (
        main(
            [
                "collatz",
                "--seed",
                "7",
                "--nth",
                str(index),
                "--no-value",
                "--info",
                "temporal.carry-bellman",
                "--temporal-bellman-horizon",
                str(horizon),
            ]
        )
        == 2
    )
    assert "carry" in capsys.readouterr().err


def test_scalar_query_does_not_run_the_carry_bellman_action(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    def forbid(*_args: object, **_kwargs: object) -> None:
        pytest.fail("unrequested carry Bellman action")

    monkeypatch.setattr(future_carry_bellman, "centered_carry_signal", forbid)
    assert main(["collatz", "--seed", "7", "--nth", "2"]) == 0
    assert capsys.readouterr().out.strip() == "11"

"""Exercise homogeneous carry observations at the receiving CLI source."""

import json

import pytest

from number_compiler.api.cli import main
from number_compiler.arithmetic.contracts.input_validation import string_keyed_mapping
from number_compiler.sequences.collatz import future_carry_bellman


def test_carry_bellman_uses_the_selected_endpoint(
    capsys: pytest.CaptureFixture[str],
) -> None:
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
                "2,3",
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
    assert bellman["first_normalized_offset"] == 2
    assert bellman["first_physical_offset"] == 4


@pytest.mark.parametrize(("index", "horizon"), ((1, 1), (2, 3)))
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

    monkeypatch.setattr(future_carry_bellman, "first_simultaneous_even_carries", forbid)
    assert main(["collatz", "--seed", "7", "--nth", "2"]) == 0
    assert capsys.readouterr().out.strip() == "11"

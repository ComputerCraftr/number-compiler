"""Fermat's optional carry tape cannot decide its unresolved prime bit."""

import json

import pytest

from number_compiler.api.cli import main
from number_compiler.api.cli_requests import parse_request


def test_fermat_ordered_carry_is_explicit_and_nondeciding(
    capsys: pytest.CaptureFixture[str], monkeypatch: pytest.MonkeyPatch
) -> None:
    from number_compiler.api import fermat_carry_observation as observer

    arguments = [
        "fermat",
        "--nth",
        "5",
        "--no-value",
        "--info",
        "number-theory.primality",
        "--format",
        "json",
    ]
    assert main(arguments + ["--ordered-carry-windows"]) == 3
    demanded = json.loads(capsys.readouterr().out)["info"]["number-theory.primality"]
    packet = demanded["ordered_carry_windows"]
    assert packet["primality_authority"] is False
    assert packet["full_binary_square_carry_cochain_certified"] is False
    assert [s["outgoing"] for s in packet["windows"][-1]["ordered_carries"]] == [
        1,
        0,
        0,
        2,
    ]

    def forbidden(_index: int) -> dict[str, object]:
        raise AssertionError("ordinary primality query demanded carry tape")

    monkeypatch.setattr(observer, "fermat_carry_packet", forbidden)
    assert main(arguments) == 3
    ordinary = json.loads(capsys.readouterr().out)["info"]["number-theory.primality"]
    assert "ordered_carry_windows" not in ordinary
    assert demanded["status"] == ordinary["status"]


@pytest.mark.parametrize(
    "arguments",
    [
        ["mersenne", "--nth", "5", "--info", "number-theory.primality"],
        ["fermat", "--nth", "5", "--info", "metrics"],
    ],
)
def test_carry_tower_requires_fermat_primality(arguments: list[str]) -> None:
    with pytest.raises((SystemExit, ValueError)):
        parse_request([*arguments, "--ordered-carry-windows"])


def test_carry_extent_rejected_before_theorem_resolution(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("out-of-budget observer started theorem resolution")

    monkeypatch.setattr(CanonicalSequenceCompiler, "resolve_special_theorem", forbidden)
    assert (
        main(
            [
                "fermat",
                "--nth",
                "17",
                "--no-value",
                "--info",
                "number-theory.primality",
                "--ordered-carry-windows",
            ]
        )
        == 2
    )
    assert "Fermat carry source index" in capsys.readouterr().err

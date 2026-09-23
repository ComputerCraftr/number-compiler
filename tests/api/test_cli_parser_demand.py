"""Family-first parsing does not construct unrelated observation options."""

import argparse
import re

import pytest

from number_compiler.api import cli_requests


@pytest.mark.parametrize("family", cli_requests.CAPABILITIES)
def test_family_parser_does_not_build_other_observers(
    monkeypatch: pytest.MonkeyPatch, family: str
) -> None:
    original = cli_requests.observation_options
    visited: list[str] = []

    def demanded(name: str) -> dict[str, tuple[int | None, tuple[str, ...]]]:
        assert name == family, "query built another family's observation actions"
        visited.append(name)
        return original(name)

    monkeypatch.setattr(cli_requests, "observation_options", demanded)
    argv = [family, "--nth", "1"]
    if family in {"reverse-add", "collatz"}:
        argv += ["--seed", "196"]
    request = cli_requests.parse_request(argv)
    assert request is not None and request.family == family
    assert visited
    assert set(visited) == {family}


def test_parser_rejects_unknown_family_demand() -> None:
    with pytest.raises(ValueError, match="unknown demanded CLI family"):
        cli_requests.parser(demanded_family="unknown")


@pytest.mark.parametrize("family", cli_requests.CAPABILITIES)
def test_demanded_help_matches_full_parser(
    family: str, capsys: pytest.CaptureFixture[str]
) -> None:
    for full in (True, False):
        command = cli_requests.parser(demanded_family=None if full else family)
        with pytest.raises(SystemExit) as stopped:
            command.parse_args([family, "--help"])
        assert stopped.value.code == 0
        output = capsys.readouterr()
        assert output.err == ""
        if full:
            expected = output.out
        else:
            assert output.out == expected


@pytest.mark.parametrize(
    "argv",
    (
        ["prime", "--nth", "10", "--info", "metrics"],
        ["collatz", "--events", "4", "--seed", "27", "--info", "hensel"],
        ["antihydra", "--nth", "3", "--info", "mahler"],
        ["fermat", "--nth", "4", "--no-value", "--info", "primality"],
        ["--list-families"],
    ),
)
def test_demanded_request_matches_full_parser(
    argv: list[str], monkeypatch: pytest.MonkeyPatch
) -> None:
    actual = cli_requests.parse_request(argv)
    original = cli_requests.parser

    def complete(*, demanded_family: str | None = None) -> argparse.ArgumentParser:
        return original()

    monkeypatch.setattr(cli_requests, "parser", complete)
    assert cli_requests.parse_request(argv) == actual


def test_collatz_help_distinguishes_term_and_event_information(
    capsys: pytest.CaptureFixture[str],
) -> None:
    command = cli_requests.parser(demanded_family="collatz")
    with pytest.raises(SystemExit) as stopped:
        command.parse_args(["collatz", "--help"])
    assert stopped.value.code == 0
    help_text = re.sub(r"\s+", " ", capsys.readouterr().out)
    assert "--nth: metrics, clock" in help_text
    assert (
        "--events: clock, modular, twisted, hasse, hensel, tropical, factor, safety"
        in help_text
    )


@pytest.mark.parametrize("option", ("--output-base", "--max-output-bits"))
def test_events_reject_term_only_output_controls(option: str) -> None:
    with pytest.raises(ValueError, match="event observations have no term output"):
        cli_requests.parse_request(
            ["collatz", "--events", "1", "--seed", "27", "--info", "clock", option, "2"]
        )


def test_events_reject_term_only_metrics_and_preserve_term_metrics() -> None:
    with pytest.raises(ValueError, match="unavailable for this selector"):
        cli_requests.parse_request(
            ["collatz", "--events", "1", "--seed", "27", "--info", "metrics"]
        )
    term = cli_requests.parse_request(
        ["collatz", "--nth", "1", "--seed", "27", "--info", "metrics"]
    )
    assert term is not None and term.info == ("metrics",)


def test_events_reject_unused_radix_but_nth_retains_it() -> None:
    with pytest.raises(ValueError, match="--radix applies to Collatz --nth"):
        cli_requests.parse_request(
            [
                "collatz",
                "--events",
                "1",
                "--seed",
                "27",
                "--info",
                "clock",
                "--radix",
                "6",
            ]
        )
    term = cli_requests.parse_request(
        ["collatz", "--nth", "1", "--seed", "27", "--radix", "6"]
    )
    assert term is not None and term.radix == 6


def test_selector_index_units_are_explicit() -> None:
    cases = (
        (["collatz", "--nth", "0", "--seed", "27"], "physical_iterations"),
        (
            ["collatz", "--events", "0", "--seed", "27", "--info", "clock"],
            "accelerated_odd_events",
        ),
        (["antihydra", "--nth", "0"], "macro_returns_after_startup"),
    )
    for argv, expected_unit in cases:
        request = cli_requests.parse_request(argv)
        assert request is not None and request.index_unit == expected_unit

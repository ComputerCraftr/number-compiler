"""Family-first parsing builds only the requested family's option actions."""

from __future__ import annotations

import argparse
import re
from dataclasses import dataclass
from typing import ClassVar, cast

import pytest

from number_compiler.api import cli_requests
from number_compiler.api.cli_types import (
    PrimeObservationOptions,
)
from number_compiler.api.family_registry import (
    CAPABILITIES,
    AdapterBinding,
    FamilyCapability,
    FamilySpec,
    ObservationAdapterBinding,
    ObservationValueBinding,
    OptionSpec,
)
from number_compiler.api.query_types import (
    CollatzTermQuery,
    TermQuery,
)


@pytest.mark.parametrize("family", CAPABILITIES)
def test_family_parser_builds_only_demanded_observation_options(
    monkeypatch: pytest.MonkeyPatch, family: str
) -> None:
    original = FamilySpec.parser_options
    visited: list[str] = []

    def demanded(spec: FamilySpec) -> dict[str, OptionSpec]:
        assert spec is CAPABILITIES[family], (
            "parser constructed another family's options"
        )
        visited.append(family)
        return original(spec)

    monkeypatch.setattr(FamilySpec, "parser_options", demanded)
    cli_requests.parser(demanded_family=family)
    assert visited == [family]


def test_parser_rejects_unknown_demanded_family() -> None:
    with pytest.raises(ValueError, match="unknown demanded CLI family"):
        cli_requests.parser(demanded_family="unknown")


@pytest.mark.parametrize("family", CAPABILITIES)
def test_demanded_help_matches_full_parser(
    family: str, capsys: pytest.CaptureFixture[str]
) -> None:
    expected = ""
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
    ),
)
def test_demanded_request_matches_full_parser(
    argv: list[str], monkeypatch: pytest.MonkeyPatch
) -> None:
    actual = cli_requests.parse_request(argv)
    assert actual is not None
    original = cli_requests.parser

    def complete(
        *, demanded_family: str | None = None, registry: object = None
    ) -> argparse.ArgumentParser:
        return original()

    monkeypatch.setattr(cli_requests, "parser", complete)
    assert cli_requests.parse_request(argv) == actual


def test_list_request_has_no_term_execution() -> None:
    assert cli_requests.parse_request(["--list-families"]) is None


def test_collatz_help_distinguishes_term_and_event_information(
    capsys: pytest.CaptureFixture[str],
) -> None:
    command = cli_requests.parser(demanded_family="collatz")
    with pytest.raises(SystemExit) as stopped:
        command.parse_args(["collatz", "--help"])
    assert stopped.value.code == 0
    help_text = re.sub(r"\s+", " ", capsys.readouterr().out)
    assert "--nth: metrics, clock, accumulator" in help_text
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


def test_events_reject_metrics_and_preserve_typed_term_observations() -> None:
    with pytest.raises(ValueError, match="unavailable for this selector"):
        cli_requests.parse_request(
            ["collatz", "--events", "1", "--seed", "27", "--info", "metrics"]
        )
    request = cli_requests.parse_request(
        ["collatz", "--nth", "1", "--seed", "27", "--info", "metrics"]
    )
    assert request is not None
    assert request.observations.info == ("metrics",)
    assert isinstance(request.execution, CollatzTermQuery)
    assert request.execution.seed == 27


def test_events_reject_unused_radix_and_term_retains_it() -> None:
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
    request = cli_requests.parse_request(
        ["collatz", "--nth", "1", "--seed", "27", "--radix", "6"]
    )
    assert request is not None
    assert isinstance(request.execution, CollatzTermQuery)
    assert request.execution.radix == 6


def test_selector_coordinates_and_power10_presentation_are_separate() -> None:
    term = cli_requests.parse_request(["prime", "--nth-power10", "1"])
    assert term is not None
    assert term.index == 10
    assert term.presentation_index == {"encoding": "power10", "exponent": 1}
    assert term.index_unit == "prime_index"
    events = cli_requests.parse_request(
        ["collatz", "--events", "3", "--seed", "27", "--info", "clock"]
    )
    assert events is not None
    assert events.selector == "events"
    assert events.index == 3
    assert events.index_unit == "accelerated_odd_events"


def test_unknown_command_is_rejected() -> None:
    with pytest.raises(SystemExit) as stopped:
        cli_requests.parse_request(["unknown-family", "--nth", "1"])
    assert stopped.value.code == 2


def test_synthetic_registry_entry_builds_a_typed_request(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    @dataclass(frozen=True, slots=True)
    class SyntheticTermQuery:
        index: int

        family: ClassVar[str] = "synthetic"
        selector: ClassVar[str] = "nth"

    spec = FamilySpec(
        FamilyCapability("synthetic_index", (), ("metrics",)),
        cast(type[TermQuery], SyntheticTermQuery),
        AdapterBinding("unused.module", "project"),
        ObservationAdapterBinding("unused.module", "prepare", "admit", "observe"),
        term_observation=ObservationValueBinding(PrimeObservationOptions),
    )
    registry = {"synthetic": spec}
    monkeypatch.setitem(CAPABILITIES, "synthetic", spec)
    command = cli_requests.parser(registry=registry)
    with pytest.raises(SystemExit) as stopped:
        command.parse_args(["synthetic", "--help"])
    assert stopped.value.code == 0
    request = cli_requests.parse_request(
        ["synthetic", "--nth", "3", "--no-value", "--info", "metrics"],
        registry=registry,
    )
    assert request is not None
    assert type(cast(object, request.execution)) is SyntheticTermQuery
    assert request.index == 3
    assert request.index_unit == "synthetic_index"

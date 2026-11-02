"""Family-first parsing builds only the requested family's option actions."""

from __future__ import annotations

import argparse
import re

import pytest

from number_compiler.api import cli_context, cli_requests
from number_compiler.api.cli_context import QueryContext
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
from number_compiler.api.number_api import NumberCompiler
from number_compiler.api.observation_types import (
    IndexUnit,
    ObservationId,
    OutputStatus,
    SelectorId,
)
from number_compiler.api.query_types import (
    CollatzTermQuery,
    PrimeTermQuery,
)
from number_compiler.arithmetic.contracts.family_identity import FamilyId


@pytest.mark.parametrize("family", CAPABILITIES)
def test_family_parser_builds_only_demanded_observation_options(
    monkeypatch: pytest.MonkeyPatch, family: FamilyId
) -> None:
    original = FamilySpec.parser_options
    visited: list[FamilyId] = []

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
        cli_requests.parser(demanded_family=FamilyId.PRIME, registry={})


def test_registry_declarations_reject_forged_internal_ids() -> None:
    capability = FamilyCapability(IndexUnit.ITERATIONS, (), ())
    object.__setattr__(capability, "unit", "iterations")
    with pytest.raises(TypeError, match="IndexUnit"):
        capability.__post_init__()
    option = OptionSpec(None, ())
    object.__setattr__(option, "value_kind", "integer")
    with pytest.raises(TypeError, match="OptionValueKind"):
        option.__post_init__()
    option = OptionSpec(None, ())
    object.__setattr__(option, "information", ("metrics",))
    with pytest.raises(TypeError, match="ObservationIds"):
        option.__post_init__()


@pytest.mark.parametrize("family", CAPABILITIES)
def test_demanded_help_matches_full_parser(
    family: FamilyId, capsys: pytest.CaptureFixture[str]
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
        ["collatz", "--events", "4", "--seed", "27", "--info", "arithmetic.hensel"],
        ["antihydra", "--nth", "3", "--info", "arithmetic.mahler"],
        ["fermat", "--nth", "4", "--no-value", "--info", "number-theory.primality"],
    ),
)
def test_demanded_request_matches_full_parser(
    argv: list[str], monkeypatch: pytest.MonkeyPatch
) -> None:
    actual = cli_requests.parse_request(argv)
    assert actual is not None
    original = cli_requests.parser

    def complete(
        *, demanded_family: FamilyId | None = None, registry: object = None
    ) -> argparse.ArgumentParser:
        return original()

    monkeypatch.setattr(cli_requests, "parser", complete)
    assert cli_requests.parse_request(argv) == actual


def test_list_request_has_no_term_execution() -> None:
    assert cli_requests.parse_request(["--list-families"]) is None


def test_collatz_help_distinguishes_term_and_event_information(
    capsys: pytest.CaptureFixture[str],
) -> None:
    command = cli_requests.parser(demanded_family=FamilyId.COLLATZ)
    with pytest.raises(SystemExit) as stopped:
        command.parse_args(["collatz", "--help"])
    assert stopped.value.code == 0
    help_text = re.sub(r"\s+", " ", capsys.readouterr().out)
    assert (
        "--nth: temporal, metrics, temporal.matrix, temporal.clock, temporal.accumulator, temporal.double-accumulator, "
        "temporal.diagonal-carry, temporal.macro, temporal.innovation-borrow"
    ) in help_text
    assert (
        "--events: temporal, temporal.clock, arithmetic.modular, arithmetic.twisted, "
        "arithmetic.hasse, arithmetic.hensel, arithmetic.tropical, arithmetic.factor, "
        "safety.execution" in help_text
    )

    assert "--events uses accelerated_odd_events" in help_text


def test_collatz_clock_spec_records_units_per_selector() -> None:
    from number_compiler.api.observation_types import IndexUnit

    clock = next(
        item
        for item in CAPABILITIES[FamilyId.COLLATZ].observation_specs
        if item.identifier is ObservationId.TEMPORAL_CLOCK
    )
    assert clock.unit_for(SelectorId.NTH) is IndexUnit.PHYSICAL_ITERATIONS
    assert clock.unit_for(SelectorId.EVENTS) is IndexUnit.ACCELERATED_ODD_EVENTS
    term = cli_requests.parse_request(
        ["collatz", "--nth", "3", "--seed", "27", "--info", "temporal.clock"]
    )
    event = cli_requests.parse_request(
        ["collatz", "--events", "3", "--seed", "27", "--info", "temporal.clock"]
    )
    assert term is not None and term.index_unit is IndexUnit.PHYSICAL_ITERATIONS
    assert event is not None and event.index_unit is IndexUnit.ACCELERATED_ODD_EVENTS


def test_observation_specs_reference_the_canonical_packet_schema() -> None:
    from number_compiler.api.output_schema import ObservationPacket

    assert all(
        observation.packet_schema is ObservationPacket
        for spec in CAPABILITIES.values()
        for observation in spec.observation_specs
    )


@pytest.mark.parametrize(
    "family,selector,options,legacy",
    (
        ("collatz", "--nth", ["27", "--seed", "27"], "clock"),
        ("reverse-add", "--nth", ["1", "--seed", "196"], "boundary-macro"),
        ("antihydra", "--nth", ["1"], "mahler"),
        ("antihydra", "--nth", ["1"], "ledger"),
        ("fermat", "--nth", ["3"], "primality"),
        ("fermat", "--nth", ["3"], "factor"),
        ("2rev10", "--nth", ["1", "--seed", "196"], "temporal-grammar"),
    ),
)
def test_legacy_observation_spellings_are_rejected_by_parser(
    family: str,
    selector: str,
    options: list[str],
    legacy: str,
) -> None:
    with pytest.raises(SystemExit) as stopped:
        cli_requests.parse_request([family, selector, *options, "--info", legacy])
    assert stopped.value.code == 2


@pytest.mark.parametrize("option", ("--output-base", "--max-output-bits"))
def test_events_reject_term_only_output_controls(option: str) -> None:
    with pytest.raises(ValueError, match="event observations have no term output"):
        cli_requests.parse_request(
            [
                "collatz",
                "--events",
                "1",
                "--seed",
                "27",
                "--info",
                "temporal.clock",
                option,
                "2",
            ]
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
                "temporal.clock",
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
        ["collatz", "--events", "3", "--seed", "27", "--info", "temporal.clock"]
    )
    assert events is not None
    assert events.selector == "events"
    assert events.index == 3
    assert events.index_unit == "accelerated_odd_events"


def test_temporal_summary_is_a_compact_query_snapshot_without_projection(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    request = cli_requests.parse_request(
        [
            "collatz",
            "--seed",
            "27",
            "--nth-power10",
            "2",
            "--no-value",
            "--info",
            "temporal",
        ]
    )
    assert request is not None
    assert request.family is FamilyId.COLLATZ
    assert request.selector is SelectorId.NTH

    def forbidden(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("temporal summary projected an unrequested term")

    monkeypatch.setattr(NumberCompiler, "project", forbidden)
    monkeypatch.setattr(cli_context, "resolve_observation_adapter", forbidden)
    packet = QueryContext(request, NumberCompiler()).information()["temporal"]
    clocks = packet["clocks"]
    measurements = packet["measurements"]
    assert isinstance(clocks, dict) and isinstance(measurements, dict)
    requested_clock = clocks["requested"]
    assert isinstance(requested_clock, dict)
    assert packet["status"] == OutputStatus.SNAPSHOT.value
    assert packet["scope"] == "query_snapshot_only"
    assert packet["index"] == {"encoding": "power10", "exponent": 2}
    assert requested_clock["value"] == packet["index"]
    assert measurements["projection_published"] is False


def test_unknown_command_is_rejected() -> None:
    with pytest.raises(SystemExit) as stopped:
        cli_requests.parse_request(["unknown-family", "--nth", "1"])
    assert stopped.value.code == 2


def test_synthetic_registry_entry_builds_a_typed_request() -> None:
    spec = FamilySpec(
        FamilyCapability(IndexUnit.PRIME_INDEX, (), (ObservationId.METRICS,)),
        PrimeTermQuery,
        AdapterBinding("unused.module", "project"),
        ObservationAdapterBinding("unused.module", "prepare", "admit", "observe"),
        term_observation=ObservationValueBinding(PrimeObservationOptions),
    )
    registry: dict[FamilyId, FamilySpec] = {FamilyId.PRIME: spec}
    command = cli_requests.parser(registry=registry)
    with pytest.raises(SystemExit) as stopped:
        command.parse_args([FamilyId.PRIME.value, "--help"])
    assert stopped.value.code == 0
    request = cli_requests.parse_request(
        [FamilyId.PRIME.value, "--nth", "3", "--no-value", "--info", "metrics"],
        registry=registry,
    )
    assert request is not None
    assert type(request.execution) is PrimeTermQuery
    assert request.index == 3
    assert request.index_unit is IndexUnit.PRIME_INDEX

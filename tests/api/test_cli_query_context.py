"""Independent checks for demanded work and shared family query ownership."""

from __future__ import annotations

import json
from typing import Any, Never

import pytest

from number_compiler.api import cli, cli_context
from number_compiler.api.cylinder_observation import CollatzObservationContext
from number_compiler.api.number_api import NumberCompiler, ProjectedNumberTerm


def forbidden(*args: object, **kwargs: object) -> Never:
    raise AssertionError("unrequested execution was entered")


@pytest.mark.parametrize(
    "family,index,extra,expected",
    [
        ("196", 0, [], "196"),
        ("reverse-add", 0, ["--seed", "0"], "0"),
        ("collatz", 0, ["--seed", "27"], "27"),
        ("prime", 0, [], "2"),
        ("fermat", 0, [], "3"),
        ("mersenne", 1, [], "1"),
        ("antihydra", 0, [], "8"),
        ("196", 16, [], "897100798"),
        ("reverse-add", 1, ["--seed", "89"], "187"),
        ("collatz", 10, ["--seed", "27"], "214"),
        ("prime", 100, [], "547"),
        ("fermat", 5, [], "4294967297"),
        ("mersenne", 131, [], str(2**131 - 1)),
        ("antihydra", 10, [], "454"),
    ],
)
@pytest.mark.parametrize("output_format", ("value", "json"))
def test_plain_terms_do_not_request_information(
    family: str,
    index: int,
    extra: list[str],
    expected: str,
    output_format: str,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler
    from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm

    monkeypatch.setattr(cli_context.QueryContext, "_observe", forbidden)
    monkeypatch.setattr(cli_context, "_metrics_json", forbidden)
    monkeypatch.setattr(CanonicalSequenceCompiler, "resolve_special_theorem", forbidden)
    monkeypatch.setattr(AntihydraArithmeticTerm, "physical_run", forbidden)
    assert (
        cli.main([family, "--nth", str(index), *extra, "--format", output_format]) == 0
    )
    capture = capsys.readouterr()
    if output_format == "json":
        row = json.loads(capture.out)
        assert row["value"] == expected and row["info"] == {}
    else:
        assert capture.out == expected + "\n"
    assert capture.err == ""


def test_primality_only_does_not_construct_a_value(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    monkeypatch.setattr(NumberCompiler, "project_nth", forbidden)
    monkeypatch.setattr(cli, "_render_value", forbidden)
    assert (
        cli.main(
            [
                "fermat",
                "--nth",
                "4",
                "--no-value",
                "--info",
                "primality",
                "--format",
                "json",
            ]
        )
        == 3
    )
    row = json.loads(capsys.readouterr().out)
    assert row["value"] is None
    assert row["info"]["primality"]["status"] == "unknown"


def test_reverse_metrics_only_does_not_construct_reachable_image(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    from number_compiler.hashlife.execution.tile_scheduler import TileApplication

    monkeypatch.setattr(TileApplication, "complete", forbidden)
    monkeypatch.setattr(TileApplication, "point", forbidden)
    monkeypatch.setattr(TileApplication, "width", forbidden)
    monkeypatch.setattr(cli, "_render_value", forbidden)
    assert (
        cli.main(
            [
                "196",
                "--nth",
                "32",
                "--no-value",
                "--info",
                "metrics",
                "--format",
                "json",
            ]
        )
        == 0
    )
    capture = capsys.readouterr()
    row = json.loads(capture.out)
    assert row["value"] is None and capture.err == ""
    execution = row["info"]["metrics"]["execution_metrics"]
    assert execution["higher_concrete_operation_evaluations"] == 0
    assert execution["higher_action_continuation_requests"] == 0


def test_multiple_collatz_event_views_discover_one_prefix(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    constructor = CollatzObservationContext
    constructions = 0

    def counted(seed: int, events: int, *, max_events: int, max_digits: int) -> object:
        nonlocal constructions
        constructions += 1
        return constructor(seed, events, max_events=max_events, max_digits=max_digits)

    monkeypatch.setattr(cli_context, "_events_context", counted)
    monkeypatch.setattr(NumberCompiler, "project_nth", forbidden)
    assert (
        cli.main(
            [
                "collatz",
                "--events",
                "4",
                "--seed",
                "27",
                "--info",
                "clock",
                "--info",
                "modular",
                "--info",
                "clock",
                "--format",
                "json",
            ]
        )
        == 0
    )
    row = json.loads(capsys.readouterr().out)
    assert constructions == 1
    assert row["index_unit"] == "accelerated_odd_events" and row["value"] is None
    assert set(row["info"]) == {"clock", "modular"}
    assert row["info"]["clock"]["discovered_events"] == 4
    assert row["info"]["modular"]["discovered_events"] == 4


def test_collatz_event_cli_consumes_published_support_without_digit_replay(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    from number_compiler.sequences.collatz import raw_field

    monkeypatch.setattr(
        raw_field, "accelerated_collatz_sentinel_step_digits", forbidden
    )
    assert (
        cli.main(
            [
                "collatz",
                "--events",
                "4",
                "--seed",
                "27",
                "--info",
                "clock",
                "--info",
                "hasse",
                "--format",
                "json",
            ]
        )
        == 0
    )
    info = json.loads(capsys.readouterr().out)["info"]
    for name in ("clock", "hasse"):
        assert info[name]["source_support_ticks"] == 9  # valuations 1, 2, 1, 1
        assert (
            info[name]["source_work_counters"]["collatz_source_discovery_events"] == 4
        )


def test_collatz_context_rejects_substituted_published_root() -> None:
    from number_compiler.api.cylinder_observation import observe_collatz

    context = CollatzObservationContext(27, 4, max_events=4, max_digits=100)
    context.root = context.arena.identity
    with pytest.raises(ValueError, match="published source binding"):
        observe_collatz(
            27, 4, kind="clock", max_events=4, max_digits=100, _context=context
        )


def test_multiple_physical_views_use_one_term(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    original = NumberCompiler.project_nth
    projected: list[ProjectedNumberTerm] = []

    def capture(
        self: NumberCompiler,
        family: str,
        index: int,
        *,
        seed: int | None = None,
        base: int = 10,
        radix: int = 2,
        start: int = 2,
        max_steps: int = 4096,
        max_state_bits: int = 4096,
    ) -> ProjectedNumberTerm:
        term = original(
            self,
            family,
            index,
            seed=seed,
            base=base,
            radix=radix,
            start=start,
            max_steps=max_steps,
            max_state_bits=max_state_bits,
        )
        projected.append(term)
        return term

    monkeypatch.setattr(NumberCompiler, "project_nth", capture)
    assert (
        cli.main(
            [
                "collatz",
                "--nth",
                "4",
                "--seed",
                "27",
                "--info",
                "metrics",
                "--info",
                "clock",
                "--info",
                "clock",
                "--format",
                "json",
            ]
        )
        == 0
    )
    row = json.loads(capsys.readouterr().out)
    assert row["value"] == "62" and len(projected) == 1
    assert row["info"]["clock"]["value"]["physical_ticks"] == 4


def test_physical_budget_refusal_precedes_compiler_construction(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    monkeypatch.setattr(cli, "NumberCompiler", forbidden)
    assert (
        cli.main(
            [
                "collatz",
                "--nth",
                "8",
                "--seed",
                "27",
                "--info",
                "clock",
                "--max-events",
                "1",
            ]
        )
        == 2
    )
    assert "budget exceeded" in capsys.readouterr().err


def test_antihydra_value_and_ledger_do_not_build_physical_roofs(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm

    monkeypatch.setattr(AntihydraArithmeticTerm, "physical_run", forbidden)
    assert (
        cli.main(
            [
                "antihydra",
                "--nth",
                "10",
                "--info",
                "ledger",
                "--info",
                "modular",
                "--info",
                "metrics",
                "--format",
                "json",
            ]
        )
        == 0
    )
    row = json.loads(capsys.readouterr().out)
    assert row["value"] == "454"
    ledger = row["info"]["ledger"]["value"]
    assert ledger["ledger"] == 11 and ledger["odd_a_steps"] == 3
    assert ledger["centered_odd_events"] == 7
    work = row["info"]["metrics"]["execution_metrics"]["work_counters"]
    assert work["arithmetic_returns"] == 10
    assert work.get("physical_roof_evaluations", 0) == 0


def test_antihydra_output_budget_accepts_seed_exactly(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert cli.main(["antihydra", "--nth", "0", "--max-output-bits", "4"]) == 0
    assert capsys.readouterr().out == "8\n"


@pytest.mark.parametrize(
    "names",
    [
        ("tape", "twisted"),
        ("twisted", "tape"),
        ("mahler", "hensel"),
        ("hensel", "mahler"),
    ],
)
def test_antihydra_equivalent_information_reuses_the_demand(
    names: tuple[str, str],
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    from number_compiler.api import antihydra_observation
    from number_compiler.sequences.antihydra.runtime import Run

    observe = antihydra_observation.observe_run
    calls: list[str] = []

    def counted(
        result: Run,
        *,
        kind: str,
        modulus: int = 257,
        width: int = 2,
        sign: int = -1,
        precision: int = 8,
        time_width: int = 2,
        time_sign: int = 1,
        max_observer_terms: int = 1_000_000,
    ) -> dict[str, Any]:
        calls.append(kind)
        if len(calls) > 1:
            raise AssertionError("equivalent demand was evaluated again")
        return observe(
            result,
            kind=kind,
            modulus=modulus,
            width=width,
            sign=sign,
            precision=precision,
            time_width=time_width,
            time_sign=time_sign,
            max_observer_terms=max_observer_terms,
        )

    monkeypatch.setattr(antihydra_observation, "observe_run", counted)
    monkeypatch.setattr(cli, "_render_value", forbidden)
    assert (
        cli.main(
            [
                "antihydra",
                "--nth",
                "16",
                "--no-value",
                "--info",
                names[0],
                "--info",
                names[1],
                "--info",
                "metrics",
                "--format",
                "json",
            ]
        )
        == 0
    )
    row = json.loads(capsys.readouterr().out)
    first, second = (row["info"][name] for name in names)
    assert calls == [names[0]]
    assert first["kind"] == names[0] and second["kind"] == names[1]
    assert first["value"] == second["value"]
    assert row["value"] is None
    work = row["info"]["metrics"]["execution_metrics"]["work_counters"]
    assert work["query_observer_reuses"] == 1


@pytest.mark.parametrize("base", (2, 16, 36))
@pytest.mark.parametrize(
    "family,index,extra,expected",
    [
        ("196", 0, [], 196),
        ("reverse-add", 0, ["--seed", "31"], 31),
        ("collatz", 0, ["--seed", "27"], 27),
        ("prime", 0, [], 2),
        ("fermat", 0, [], 3),
        ("mersenne", 1, [], 1),
        ("antihydra", 0, [], 8),
    ],
)
def test_family_output_bases_preserve_values_and_json_units(
    base: int,
    family: str,
    index: int,
    extra: list[str],
    expected: int,
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [
                family,
                "--nth",
                str(index),
                *extra,
                "--output-base",
                str(base),
                "--format",
                "json",
            ]
        )
        == 0
    )
    capture = capsys.readouterr()
    row = json.loads(capture.out)
    assert row["output_base"] == base
    assert int(row["value"], base) == expected
    assert not capture.err

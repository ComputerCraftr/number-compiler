"""Public Collatz requests consume complete D68 macro actions."""

from __future__ import annotations

import json
from typing import Never, cast

import pytest

from number_compiler.api import cli as cli_module
from number_compiler.api.cli import main as cli_main
from number_compiler.api.number_api import (
    NumberCompiler,
    PoweredCollatzTermPayload,
    ProjectedNumberTerm,
)
from number_compiler.api.output_schema import JsonValue, QueryResult
from number_compiler.api.query_types import TermQuery
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.process_cache import CacheRecordIssuerMismatch
from number_compiler.sequences.collatz import (
    mixed_clock_macros,
    temporal_mixed_execution,
    temporal_run_executor,
)
from number_compiler.sequences.collatz.boundary_macros import (
    BoundaryActionTemplateMemo,
)
from number_compiler.sequences.collatz.mixed_clock_macros import MixedClockMacro
from number_compiler.sequences.collatz.temporal_dyadic import D8TemporalTable
from tests.support.reference_arithmetic import collatz_literal

_D68_SEED = (1 << 160) + 48_233_076_155_686_138_603
_D68_PHYSICAL_TICKS = 108


def _metrics_request(physical_ticks: int) -> list[str]:
    return [
        "collatz",
        "--seed",
        str(_D68_SEED),
        "--nth",
        str(physical_ticks),
        "--info",
        "metrics",
        "--format",
        "json",
    ]


def _read_metrics_response(
    capsys: pytest.CaptureFixture[str],
    physical_ticks: int,
    source: int = _D68_SEED,
) -> QueryResult:
    packet = cast(QueryResult, json.loads(capsys.readouterr().out))
    assert packet["value"] == str(collatz_literal(source, physical_ticks))
    return packet


def _collatz_macrocell(packet: QueryResult) -> dict[str, JsonValue]:
    execution = packet["info"]["metrics"]["execution_metrics"]
    if not isinstance(execution, dict):
        raise TypeError("execution metrics packet is malformed")
    macrocells = execution["macrocells"]
    if not isinstance(macrocells, list):
        raise TypeError("macrocell metrics are malformed")
    for row in macrocells:
        if isinstance(row, dict) and row.get("family") == "collatz":
            return row
    raise AssertionError("Collatz macrocell metrics are missing")


def _capture_projected_terms(
    monkeypatch: pytest.MonkeyPatch,
) -> list[ProjectedNumberTerm]:
    captured: list[ProjectedNumberTerm] = []

    class CapturingCompiler(NumberCompiler):
        def project(self, query: TermQuery) -> ProjectedNumberTerm:
            term = super().project(query)
            captured.append(term)
            return term

    monkeypatch.setattr(cli_module, "NumberCompiler", CapturingCompiler)
    return captured


@pytest.mark.usefixtures("isolated_process_cache")
def test_public_cli_consumes_d68_action_and_warm_hit_precedes_discovery(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    argv = _metrics_request(_D68_PHYSICAL_TICKS)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("warm public query rediscovered the D68 macro")

    cases = (
        (_D68_SEED, False),
        (_D68_SEED, True),
        (_D68_SEED + (1 << 68), True),
        (_D68_SEED + (1 << 4096), True),
    )
    for receiving_source, warmed in cases:
        if warmed:
            monkeypatch.setattr(mixed_clock_macros, "_expected_mixed_gain", forbidden)
            monkeypatch.setattr(
                mixed_clock_macros, "select_mixed_clock_macro", forbidden
            )
            monkeypatch.setattr(
                temporal_mixed_execution, "select_mixed_clock_macro", forbidden
            )
            monkeypatch.setattr(temporal_run_executor, "select_mixed_macro", forbidden)
            monkeypatch.setattr(D8TemporalTable, "select", forbidden)
        argv[2] = str(receiving_source)
        assert cli_main(argv) == 0
        packet = json.loads(capsys.readouterr().out)
        assert packet["value"] == str(
            collatz_literal(receiving_source, _D68_PHYSICAL_TICKS)
        )
        execution = packet["info"]["metrics"]["execution_metrics"]
        macrocell = next(
            row for row in execution["macrocells"] if row["family"] == "collatz"
        )
        # Admission counts retrieved-cache applications, not cold publication.
        assert macrocell["mixed_action"]["retrieved"] == int(warmed)
        assert macrocell["mixed_action"]["admitted"] == int(warmed)
        assert macrocell["mixed_action"]["publications"] == int(not warmed)
        assert macrocell["mixed_action"]["applied_hits"] == int(warmed)
        assert macrocell["joint_action"]["requests"] is None
        assert macrocell["width_projection"]["requests"] == 0
        family = next(
            row
            for row in execution["family_work"]
            if row["counter_prefix"] == "collatz_physical"
        )
        assert family["run_actions"] == 1


@pytest.mark.usefixtures("isolated_process_cache")
def test_long_root_tail_rejects_cached_partial_action_without_applying_it(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    argv = _metrics_request(_D68_PHYSICAL_TICKS)
    assert cli_main(argv) == 0
    _read_metrics_response(capsys, _D68_PHYSICAL_TICKS)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("a cached but route-inapplicable action was rediscovered")

    monkeypatch.setattr(mixed_clock_macros, "select_mixed_clock_macro", forbidden)
    monkeypatch.setattr(temporal_mixed_execution, "select_mixed_clock_macro", forbidden)
    monkeypatch.setattr(temporal_run_executor, "select_mixed_macro", forbidden)
    argv[4] = "128"
    assert cli_main(argv) == 0
    bounded_tail = json.loads(capsys.readouterr().out)
    assert bounded_tail["value"] == str(collatz_literal(_D68_SEED, 128))
    bounded_execution = bounded_tail["info"]["metrics"]["execution_metrics"]
    bounded_macrocell = next(
        row for row in bounded_execution["macrocells"] if row["family"] == "collatz"
    )
    assert bounded_macrocell["mixed_action"]["applied_hits"] == 1

    argv[4] = "256"
    assert cli_main(argv) == 0
    packet = json.loads(capsys.readouterr().out)
    assert packet["value"] == str(collatz_literal(_D68_SEED, 256))
    execution = packet["info"]["metrics"]["execution_metrics"]
    macrocell = next(
        row for row in execution["macrocells"] if row["family"] == "collatz"
    )
    action = macrocell["mixed_action"]
    assert action["retrieved"] == 1
    assert action["admitted"] == 0
    assert action["applied_hits"] == 0
    assert action["publications"] == 0
    family = next(
        row
        for row in execution["family_work"]
        if row["counter_prefix"] == "collatz_physical"
    )
    assert family["balanced_routes"] == 1


@pytest.mark.usefixtures("isolated_process_cache")
def test_root_route_checks_existing_dyadic_parent_before_mixed_discovery(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    argv = _metrics_request(32)
    assert cli_main(argv) == 0
    _read_metrics_response(capsys, 32)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("an admitted dyadic root parent lost route priority")

    monkeypatch.setattr(mixed_clock_macros, "select_mixed_clock_macro", forbidden)
    monkeypatch.setattr(temporal_mixed_execution, "select_mixed_clock_macro", forbidden)
    monkeypatch.setattr(temporal_run_executor, "select_mixed_macro", forbidden)
    argv[4] = "108"
    assert cli_main(argv) == 0
    packet = json.loads(capsys.readouterr().out)
    assert packet["value"] == str(collatz_literal(_D68_SEED, 108))


@pytest.mark.usefixtures("isolated_process_cache")
def test_cold_long_request_keeps_a_bounded_mixed_prefix_for_a_warm_short_request(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    original_macro_selector = mixed_clock_macros.select_mixed_clock_macro
    original_run_selector = temporal_mixed_execution.select_mixed_macro
    captured = _capture_projected_terms(monkeypatch)
    argv = _metrics_request(256)
    assert cli_main(argv) == 0
    _read_metrics_response(capsys, 256)
    ledger = cast(PoweredCollatzTermPayload, captured[0].payload).term.resource_ledger
    assert ledger.counters["collatz_mixed_clock_classifications"] <= 32
    assert ledger.counters["collatz_hashlife_primitive_steps"] == 32
    assert ledger.counters["collatz_hashlife_mixed_publications"] == 1
    assert ledger.counters.get("collatz_hashlife_mixed_applied_hits", 0) == 0

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("a retained exact prefix was rediscovered")

    with monkeypatch.context() as warm:
        warm.setattr(mixed_clock_macros, "select_mixed_clock_macro", forbidden)
        warm.setattr(temporal_mixed_execution, "select_mixed_clock_macro", forbidden)
        warm.setattr(temporal_run_executor, "select_mixed_macro", forbidden)
        argv[4] = str(_D68_PHYSICAL_TICKS)
        assert cli_main(argv) == 0
        short_packet = _read_metrics_response(capsys, _D68_PHYSICAL_TICKS)
        mixed_action = _collatz_macrocell(short_packet)["mixed_action"]
        assert isinstance(mixed_action, dict)
        assert mixed_action["applied_hits"] == 1

    colliding_source = _D68_SEED + (1 << 16)
    selector_calls = 0

    def counted_selector(
        source: int,
        available_physical_ticks: int,
        *,
        templates: BoundaryActionTemplateMemo,
        d8_table: D8TemporalTable | None = None,
        max_preview_bits: int = 96,
    ) -> MixedClockMacro | None:
        nonlocal selector_calls
        selector_calls += 1
        return original_macro_selector(
            source,
            available_physical_ticks,
            templates=templates,
            d8_table=d8_table,
            max_preview_bits=max_preview_bits,
        )

    def counted_run_selector(
        source: int,
        available_physical_ticks: int,
        *,
        templates: BoundaryActionTemplateMemo,
        ledger: ResourceLedger,
        d8_table: D8TemporalTable | None,
        max_preview_bits: int | None = None,
    ) -> tuple[MixedClockMacro | None, D8TemporalTable | None]:
        nonlocal selector_calls
        selector_calls += 1
        return original_run_selector(
            source,
            available_physical_ticks,
            templates=templates,
            ledger=ledger,
            d8_table=d8_table,
            max_preview_bits=max_preview_bits,
        )

    monkeypatch.setattr(
        temporal_mixed_execution, "select_mixed_clock_macro", counted_selector
    )
    monkeypatch.setattr(
        temporal_run_executor, "select_mixed_macro", counted_run_selector
    )
    argv[2] = str(colliding_source)
    argv[4] = "256"
    assert cli_main(argv) == 0
    _read_metrics_response(capsys, 256, colliding_source)
    assert selector_calls > 0


@pytest.mark.usefixtures("isolated_process_cache")
def test_root_mixed_preflight_skips_terminal_power_probe_for_even_source(
    capsys: pytest.CaptureFixture[str],
) -> None:
    source = _D68_SEED + 1
    packet_args = _metrics_request(108)
    packet_args[2] = str(source)
    assert cli_main(packet_args) == 0
    packet = cast(QueryResult, json.loads(capsys.readouterr().out))
    assert packet["value"] == str(collatz_literal(source, 108))


@pytest.mark.usefixtures("isolated_process_cache")
def test_selector_miss_falls_back_and_disposes_temporary_owners(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    captured = _capture_projected_terms(monkeypatch)

    def no_candidates(*_args: object, **_kwargs: object) -> tuple[()]:
        return ()

    # Let the real selector allocate its ledger-backed scratch scope and make
    # its ordinary bounded previews, while suppressing only candidate choice.
    monkeypatch.setattr(mixed_clock_macros, "_candidate_motifs", no_candidates)
    argv = _metrics_request(_D68_PHYSICAL_TICKS)

    assert cli_main(argv) == 0
    packet = _read_metrics_response(capsys, _D68_PHYSICAL_TICKS)
    mixed_action = _collatz_macrocell(packet)["mixed_action"]
    assert isinstance(mixed_action, dict)
    assert mixed_action["publications"] == 0
    term = captured[0]
    ledger = cast(PoweredCollatzTermPayload, term.payload).term.resource_ledger
    assert ledger.counters["collatz_physical_temporal_balanced_routes"] == 1
    assert ledger.counters.get("collatz_hashlife_mixed_publications", 0) == 0
    temporary = tuple(item for item in ledger.inventory() if item.role == "temporary")
    assert temporary
    assert all(item.disposed and item.entries == item.nodes == 0 for item in temporary)


@pytest.mark.parametrize(
    ("failure_site", "expected_message"),
    [
        ("selector", "injected mixed selector budget failure"),
        ("cache_authority", "injected mixed cache issuer mismatch"),
    ],
)
@pytest.mark.usefixtures("isolated_process_cache")
def test_mixed_route_failures_are_not_treated_as_selector_misses(
    failure_site: str,
    expected_message: str,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    def fail(*_args: object, **_kwargs: object) -> Never:
        if failure_site == "selector":
            raise BlockContextBudgetExceeded(expected_message)
        raise CacheRecordIssuerMismatch(expected_message)

    if failure_site == "selector":
        monkeypatch.setattr(temporal_mixed_execution, "select_mixed_clock_macro", fail)
    else:
        monkeypatch.setattr(temporal_mixed_execution, "lookup_mixed_action", fail)

    assert (
        cli_main(
            [
                "collatz",
                "--seed",
                str(_D68_SEED),
                "--nth",
                str(_D68_PHYSICAL_TICKS),
                "--format",
                "json",
            ]
        )
        == 2
    )
    assert capsys.readouterr().err.strip() == f"number-compiler: {expected_message}"

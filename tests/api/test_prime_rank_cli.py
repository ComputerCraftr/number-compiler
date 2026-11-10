from __future__ import annotations

import json
from typing import cast

import pytest

from number_compiler.api import cli
from number_compiler.api.cli_context import QueryContext
from number_compiler.api.cli_requests import parse_request
from number_compiler.api.cli_types import NoObservations, QueryRequest
from number_compiler.api.number_api import NumberCompiler, ProjectedNumberTerm
from number_compiler.api.query_types import PrimeTermQuery, TermQuery
from number_compiler.sequences.prime.select import PrimeRankSelectMetrics

pytestmark = pytest.mark.usefixtures("isolated_process_cache")


@pytest.mark.parametrize("invalid", (0, 1, None, "yes"))
def test_shared_cache_switch_requires_exact_bool(invalid: object) -> None:
    with pytest.raises(TypeError, match="shared_cache"):
        NumberCompiler(shared_cache=cast(bool, invalid))


def _forbidden(*args: object, **kwargs: object) -> None:
    raise AssertionError("prime request reached construction before admission")


def test_prime_budget_options_are_typed_and_prime_only() -> None:
    request = parse_request(
        [
            "prime",
            "--nth",
            "12",
            "--max-prime-states",
            "321",
            "--max-prime-work",
            "654",
            "--max-prime-stages",
            "7",
        ]
    )
    assert request is not None
    assert isinstance(request.execution, PrimeTermQuery)
    assert (
        request.execution.max_prime_states,
        request.execution.max_prime_work,
        request.execution.max_prime_stages,
    ) == (321, 654, 7)

    with pytest.raises(SystemExit) as unsupported:
        parse_request(["collatz", "--nth", "1", "--seed", "3", "--max-prime-work", "2"])
    assert unsupported.value.code == 2


@pytest.mark.parametrize(
    "option",
    ("--max-prime-states", "--max-prime-work", "--max-prime-stages"),
)
def test_nonpositive_prime_budget_is_rejected_before_construction(
    option: str, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr("number_compiler.api.number_api.NumberCompiler", _forbidden)
    assert cli.main(["prime", "--nth", "1", option, "0"]) == 2
    assert option in capsys.readouterr().err


def test_prime_query_context_forwards_only_prime_budgets(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls: list[TermQuery] = []

    def capture(self: NumberCompiler, query: TermQuery) -> ProjectedNumberTerm:
        calls.append(query)
        return cast(ProjectedNumberTerm, object())

    monkeypatch.setattr(NumberCompiler, "project", capture)
    request = QueryRequest(
        PrimeTermQuery(
            3,
            start=101,
            max_prime_states=11,
            max_prime_work=22,
            max_prime_stages=33,
        ),
        observations=NoObservations(),
    )
    _ = QueryContext(request, NumberCompiler()).term
    expected = PrimeTermQuery(
        3,
        start=101,
        max_prime_states=11,
        max_prime_work=22,
        max_prime_stages=33,
    )
    assert calls == [expected]


@pytest.mark.parametrize(
    ("option", "reason"),
    (
        ("--max-prime-states", "state budget exceeded"),
        ("--max-prime-work", "work budget exceeded"),
        ("--max-prime-stages", "stage budget exceeded"),
    ),
)
def test_prime_rank_query_fails_closed_at_each_resource_boundary(
    option: str,
    reason: str,
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert cli.main(["prime", "--nth", "10", option, "1"]) == 2
    assert reason in capsys.readouterr().err


def test_prime_cli_reports_real_descriptor_work_without_parent_gaps(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(["prime", "--nth", "10", "--info", "metrics", "--format", "json"]) == 0
    )
    row = json.loads(capsys.readouterr().out)
    metrics = row["info"]["metrics"]
    assert row["value"] == "31"
    assert metrics["prime_dag_states"] > 0
    assert metrics["prime_cache_hits"] > 0
    assert metrics["prime_factor_stages"] > 0
    assert metrics["prime_discovery_queries"] > 0
    assert metrics["prime_peak_pending_frames"] > 0
    assert metrics["prime_retained_entries"] >= metrics["prime_dag_states"]
    assert metrics["prime_arithmetic_bit_work"] > 0
    assert metrics["prime_parent_gap_positions_materialized"] == 0


def test_prime_api_surfaces_rank_workspace_metrics(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    report = PrimeRankSelectMetrics(
        block_compilations=5,
        projection_work=89,
        max_block_length=128,
        leaf_length=1,
        expansion_rounds=2,
        descent_rounds=7,
        dag_states=34,
        cache_hits=55,
        factor_stages=3,
        discovery_queries=8,
        peak_pending_frames=13,
        retained_entries=34,
        arithmetic_bit_work=144,
        parent_gap_positions_materialized=0,
        shared_cache_hits=21,
        shared_cache_misses=13,
        shared_cache_entries=34,
        shared_cache_bytes=8192,
        shared_cache_evictions=1,
        shared_cache_bypasses=2,
        shared_cache_publications=3,
        admission_work=8,
        request_allocations=5,
        scheduler_work=17,
        scheduler_allocations=23,
        scheduler_counters=(("source_image_primitive_applications", 3),),
        innovation_collapses=4,
        innovation_stages=18,
    )

    def select(
        start: int,
        index: int,
        *,
        leaf_length: int = 128,
        max_states: int = 131_072,
        max_work: int = 1_000_000,
        max_stages: int = 4096,
        shared_cache: bool = False,
    ) -> tuple[int, PrimeRankSelectMetrics]:
        assert (start, index, leaf_length) == (100, 3, 128)
        assert (max_states, max_work, max_stages) == (987, 876, 765)
        assert shared_cache is True
        return 109, report

    monkeypatch.setattr(
        "number_compiler.sequences.prime.select.nth_prime_at_or_after", select
    )
    metrics = (
        NumberCompiler()
        .project(
            PrimeTermQuery(
                3,
                start=100,
                max_prime_states=987,
                max_prime_work=876,
                max_prime_stages=765,
            )
        )
        .metrics
    )
    assert metrics.projection_work == 89
    assert metrics.prime_dag_states == 34
    assert metrics.prime_cache_hits == 55
    assert metrics.prime_factor_stages == 3
    assert metrics.prime_discovery_queries == 8
    assert metrics.prime_peak_pending_frames == 13
    assert metrics.prime_retained_entries == 34
    assert metrics.prime_arithmetic_bit_work == 144
    assert metrics.prime_birth_innovation_collapses == 4
    assert metrics.prime_birth_innovation_stages == 18
    assert metrics.prime_parent_gap_positions_materialized == 0
    assert metrics.shared_cache_hits == 21
    assert metrics.shared_cache_misses == 13
    assert metrics.shared_cache_entries == 34
    assert metrics.shared_cache_bytes == 8192
    assert metrics.shared_cache_evictions == 1
    assert metrics.shared_cache_bypasses == 2
    assert metrics.shared_cache_publications == 3
    assert metrics.prime_admission_work == 8
    assert metrics.prime_request_allocations == 5
    assert metrics.prime_scheduler_work == 17
    assert metrics.prime_scheduler_peak_entries == 23
    assert metrics.prime_scheduler_counters == (
        ("source_image_primitive_applications", 3),
    )

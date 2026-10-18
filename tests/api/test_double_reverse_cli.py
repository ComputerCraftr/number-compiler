"""Public CLI contract for the fixed-decimal double-reversal family."""

from __future__ import annotations

import json

import pytest

from number_compiler.api import cli, cli_render
from number_compiler.api.cli_requests import parse_request
from number_compiler.api.cli_types import NoObservations
from number_compiler.api.number_api import DoubleReverseTermPayload, NumberCompiler
from number_compiler.api.query_types import DoubleReverseTermQuery
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm


def _forbidden(*args: object, **kwargs: object) -> None:
    raise AssertionError("a value renderer ran for an information-only query")


@pytest.mark.parametrize(
    "seed,index,expected",
    (
        (10, 0, "10"),
        (10, 1, "2"),
        (10, 2, "4"),
        (10, 3, "8"),
        (10, 4, "16"),
        (10, 5, "122"),
        (10, 6, "442"),
        (12, 0, "12"),
        (12, 1, "42"),
        (12, 2, "48"),
        (12, 3, "168"),
        (12, 4, "1722"),
        (1001, 1, "2002"),
        (1001, 4, "16016"),
        (1001, 5, "122122"),
        (0, 0, "0"),
        (0, 3, "0"),
    ),
)
def test_literal_double_reverse_terms(
    seed: int, index: int, expected: str, capsys: pytest.CaptureFixture[str]
) -> None:
    assert cli.main(["2rev10", "--seed", str(seed), "--nth", str(index)]) == 0
    assert capsys.readouterr().out == expected + "\n"


def test_seed_is_required_and_nonnegative() -> None:
    with pytest.raises(ValueError, match="2rev10 requires --seed"):
        parse_request(["2rev10", "--nth", "1"])
    with pytest.raises(ValueError, match="seed"):
        parse_request(["2rev10", "--seed", "-1", "--nth", "1"])


@pytest.mark.parametrize(
    "unsupported",
    (
        ["--base", "2"],
        ["--radix", "2"],
        ["--events", "1"],
    ),
)
def test_double_reverse_has_no_source_radix_or_event_selector(
    unsupported: list[str],
) -> None:
    with pytest.raises(SystemExit) as stopped:
        parse_request(["2rev10", "--seed", "10", "--nth", "1", *unsupported])
    assert stopped.value.code == 2


def test_default_step_and_state_bit_budgets_are_stable() -> None:
    request = parse_request(["2rev10", "--seed", "10", "--nth", "1"])
    assert request is not None
    assert request.execution == DoubleReverseTermQuery(1, seed=10)
    assert isinstance(request.execution, DoubleReverseTermQuery)
    assert request.observations == NoObservations()
    assert request.execution.max_steps == 4096
    assert request.execution.max_state_bits == 4096


@pytest.mark.parametrize("base,specifier", ((2, "b"), (8, "o"), (10, "d"), (16, "x")))
def test_output_base_formats_the_exact_decimal_recurrence(
    base: int, specifier: str, capsys: pytest.CaptureFixture[str]
) -> None:
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "12",
                "--nth",
                "3",
                "--output-base",
                str(base),
            ]
        )
        == 0
    )
    assert capsys.readouterr().out.strip() == format(168, specifier)


def test_symbolic_and_json_formats_keep_the_family_contract(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "12",
                "--nth",
                "3",
                "--format",
                "symbolic",
            ]
        )
        == 0
    )
    assert capsys.readouterr().out == "double_reverse10(seed=12)[3]\n"

    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "12",
                "--nth",
                "3",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    assert packet == {
        "family": "2rev10",
        "index": 3,
        "index_unit": "iterations",
        "output_base": 10,
        "value": "168",
        "info": {},
    }


def test_power10_zero_matches_explicit_first_index_and_stays_compact(
    capsys: pytest.CaptureFixture[str],
) -> None:
    common = ["2rev10", "--seed", "12", "--info", "metrics", "--format", "json"]
    assert cli.main([*common[:3], "--nth", "1", *common[3:]]) == 0
    explicit = json.loads(capsys.readouterr().out)
    assert cli.main([*common[:3], "--nth-power10", "0", *common[3:]]) == 0
    compact = json.loads(capsys.readouterr().out)

    encoded = {"encoding": "power10", "exponent": 0}
    assert explicit["index"] == 1
    assert compact["index"] == encoded
    assert compact["info"]["metrics"]["index"] == encoded
    assert compact["index_unit"] == explicit["index_unit"] == "iterations"
    assert compact["value"] == explicit["value"] == "42"


def test_no_value_metrics_do_not_render_the_term(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr(cli_render, "_render_value", _forbidden)
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "12",
                "--nth",
                "4",
                "--no-value",
                "--info",
                "metrics",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    assert packet["value"] is None
    assert packet["info"]["metrics"]["family"] == "2rev10"
    assert packet["info"]["metrics"]["index"] == 4


def test_step_and_state_bit_budgets_refuse_without_publishing_values(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "10",
                "--nth",
                "0",
                "--max-steps",
                "0",
            ]
        )
        == 0
    )
    assert capsys.readouterr().out == "10\n"

    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "10",
                "--nth",
                "1",
                "--max-steps",
                "0",
            ]
        )
        == 2
    )
    refused = capsys.readouterr()
    assert refused.out == ""
    assert refused.err

    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "9",
                "--nth",
                "1",
                "--max-state-bits",
                "4",
            ]
        )
        == 2
    )
    refused = capsys.readouterr()
    assert refused.out == ""
    assert refused.err


def test_same_process_query_reuses_exact_bounded_term(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    compiler = NumberCompiler()
    query = DoubleReverseTermQuery(4, seed=12, max_steps=10, max_state_bits=64)
    first = compiler.project(query)
    assert isinstance(first.payload, DoubleReverseTermPayload)
    expected = first.materialize(max_bits=64)

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("warm 2rev10 query reconstructed its term owner")

    monkeypatch.setattr(DoubleReverseTerm, "__init__", forbidden)
    repeated = compiler.project(query)
    assert isinstance(repeated.payload, DoubleReverseTermPayload)
    assert repeated.payload.term is first.payload.term
    assert repeated.materialize(max_bits=64) == expected == 1722
    assert compiler.powered_cache_info() == {
        "capacity": 8,
        "retained_terms": 1,
        "hits": 1,
        "misses": 1,
        "evictions": 0,
    }


def test_double_reverse_cache_key_includes_source_and_both_budgets() -> None:
    compiler = NumberCompiler()
    queries = (
        DoubleReverseTermQuery(2, seed=10, max_steps=4, max_state_bits=16),
        DoubleReverseTermQuery(2, seed=11, max_steps=4, max_state_bits=16),
        DoubleReverseTermQuery(2, seed=10, max_steps=5, max_state_bits=16),
        DoubleReverseTermQuery(2, seed=10, max_steps=4, max_state_bits=17),
    )
    owners = []
    for query in queries:
        result = compiler.project(query)
        assert isinstance(result.payload, DoubleReverseTermPayload)
        owners.append(result.payload.term)
    assert len({id(owner) for owner in owners}) == len(queries)
    assert compiler.powered_cache_info()["misses"] == len(queries)


def test_disabled_double_reverse_cache_builds_independent_budgeted_owners() -> None:
    compiler = NumberCompiler(max_cached_terms=0, max_context_nodes=4096)
    query = DoubleReverseTermQuery(2, seed=10, max_steps=4, max_state_bits=16)
    first = compiler.project(query)
    second = compiler.project(query)
    assert isinstance(first.payload, DoubleReverseTermPayload)
    assert isinstance(second.payload, DoubleReverseTermPayload)
    assert first.payload.term is not second.payload.term
    assert first.payload.term._ledger.max_nodes == 4096
    assert second.payload.term._ledger.max_nodes == 4096
    assert compiler.powered_cache_info() == {
        "capacity": 0,
        "retained_terms": 0,
        "hits": 0,
        "misses": 2,
        "evictions": 0,
    }


def test_disposed_double_reverse_owner_is_evicted_before_reuse() -> None:
    compiler = NumberCompiler()
    query = DoubleReverseTermQuery(1, seed=10)
    first = compiler.project(query)
    assert isinstance(first.payload, DoubleReverseTermPayload)
    first.payload.term.dispose()

    replacement = compiler.project(query)
    assert isinstance(replacement.payload, DoubleReverseTermPayload)
    assert replacement.payload.term is not first.payload.term
    assert compiler.powered_cache_info() == {
        "capacity": 8,
        "retained_terms": 1,
        "hits": 0,
        "misses": 2,
        "evictions": 1,
    }

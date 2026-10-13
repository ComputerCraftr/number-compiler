"""Typed execution-query contracts and family adapter equivalence checks."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import FrozenInstanceError
from typing import cast

import pytest

import number_compiler
import number_compiler.api as public_api
from number_compiler.api.cli_types import (
    CollatzEventObservationOptions,
    CollatzTermObservationOptions,
    IndexPresentation,
    NoObservations,
    OutputFormat,
    PresentationOptions,
    QueryRequest,
)
from number_compiler.api.number_api import NumberCompiler
from number_compiler.api.query_types import (
    AntihydraTermQuery,
    AntihydraVerifyQuery,
    CollatzEventQuery,
    CollatzTermQuery,
    CommaTermQuery,
    DoubleReverseTermQuery,
    FermatTermQuery,
    MersenneTermQuery,
    PrimeTermQuery,
    QueryOptionError,
    ReverseAddTermQuery,
    TermQuery,
)


def _double_reverse_float_index() -> object:
    constructor = cast(Callable[..., DoubleReverseTermQuery], DoubleReverseTermQuery)
    return constructor(1.0, seed=10)


def _mutate_frozen_seed(query: ReverseAddTermQuery) -> None:
    assign = cast(Callable[..., object], setattr)
    assign(query, "seed", 295)


def test_family_queries_are_frozen_and_keep_only_family_parameters() -> None:
    query = ReverseAddTermQuery(5, seed=196)

    assert query.family == "reverse-add"
    assert query.selector == "nth"
    with pytest.raises(FrozenInstanceError):
        _mutate_frozen_seed(query)

    event = CollatzEventQuery(4, seed=27)
    assert event.index == event.events == 4
    assert event.selector == "events"
    assert not hasattr(event, "modulus")
    assert AntihydraVerifyQuery("proof.json").selector == "verify"


def test_execution_query_types_are_available_from_public_facades() -> None:
    query = ReverseAddTermQuery(2, seed=196)

    assert number_compiler.ReverseAddTermQuery is ReverseAddTermQuery
    assert public_api.ReverseAddTermQuery is ReverseAddTermQuery
    assert number_compiler.TermQuery == public_api.TermQuery
    assert isinstance(query, number_compiler.TermQuery)


@pytest.mark.parametrize(
    "factory",
    (
        lambda: ReverseAddTermQuery(True, seed=196),
        lambda: ReverseAddTermQuery(1, seed=196, base=1),
        _double_reverse_float_index,
        lambda: DoubleReverseTermQuery(1, seed=-1),
        lambda: CollatzTermQuery(1, seed=0),
        lambda: CollatzTermQuery(1, seed=27, radix=5),
        lambda: AntihydraTermQuery(1, max_state_bits=3),
        lambda: CommaTermQuery(0),
        lambda: PrimeTermQuery(0, max_prime_work=0),
        lambda: FermatTermQuery(True),
        lambda: MersenneTermQuery(0),
        lambda: CollatzEventQuery(1, seed=2),
        lambda: CollatzEventQuery(5, seed=27, max_events=4),
        lambda: AntihydraVerifyQuery(""),
    ),
)
def test_family_queries_reject_invalid_values_at_construction(
    factory: Callable[[], object],
) -> None:
    with pytest.raises((TypeError, ValueError)):
        factory()


def test_typed_query_validation_retains_the_canonical_cli_field() -> None:
    with pytest.raises(QueryOptionError) as invalid_budget:
        PrimeTermQuery(3, max_prime_work=0)
    assert invalid_budget.value.field == "max_prime_work"

    with pytest.raises(QueryOptionError) as invalid_seed:
        DoubleReverseTermQuery(1, seed=True)
    assert invalid_seed.value.field == "seed"


def test_typed_queries_reach_the_existing_exact_family_adapters() -> None:
    compiler = NumberCompiler()
    queries: tuple[tuple[TermQuery, int], ...] = (
        (ReverseAddTermQuery(5, seed=196), 52_514),
        (DoubleReverseTermQuery(1, seed=10), 2),
        (CollatzTermQuery(10, seed=27), 214),
        (AntihydraTermQuery(0), 8),
        (PrimeTermQuery(3), 7),
        (FermatTermQuery(4), 65_537),
        (MersenneTermQuery(13), 8_191),
    )

    for query, expected in queries:
        assert compiler.nth(query) == expected

    assert compiler.project_digit(FermatTermQuery(2), 0) == 1
    assert compiler.project_digit(FermatTermQuery(2), 4) == 1


def test_unregistered_query_type_is_rejected_before_family_work() -> None:
    compiler = NumberCompiler(max_cached_terms=0)
    with pytest.raises(TypeError, match="unsupported|query"):
        compiler.project(cast(TermQuery, object()))
    assert compiler.powered_cache_info()["misses"] == 0


@pytest.mark.parametrize("value", (True, 1.5, 0, -1))
def test_query_request_rejects_invalid_index_bit_budgets(value: object) -> None:
    with pytest.raises((TypeError, ValueError)):
        QueryRequest(CollatzTermQuery(1, seed=27), max_index_bits=cast(int, value))


def test_query_request_rejects_unregistered_and_selector_mismatched_authority() -> None:
    class SpoofedCollatzQuery(CollatzTermQuery):
        pass

    with pytest.raises(TypeError, match="registered exact query"):
        QueryRequest(SpoofedCollatzQuery(1, seed=27))
    with pytest.raises(TypeError, match="registered option type"):
        QueryRequest(
            CollatzTermQuery(1, seed=27),
            observations=CollatzEventObservationOptions(("clock",)),
        )
    with pytest.raises(TypeError, match="registered option type"):
        QueryRequest(
            CollatzEventQuery(1, seed=27),
            observations=CollatzTermObservationOptions(("metrics",)),
        )
    assert QueryRequest(CollatzTermQuery(1, seed=27), observations=NoObservations())


@pytest.mark.parametrize(
    "factory",
    (
        lambda: PresentationOptions(output_base=True),
        lambda: PresentationOptions(output_base=1),
        lambda: PresentationOptions(max_output_bits=0),
        lambda: PresentationOptions(max_output_bits=cast(int, 1.5)),
        lambda: PresentationOptions(format=cast(OutputFormat, "yaml")),
        lambda: PresentationOptions(no_value=cast(bool, 1)),
        lambda: PresentationOptions(index=IndexPresentation("power10", True)),
    ),
)
def test_presentation_options_reject_noncanonical_values(
    factory: Callable[[], object],
) -> None:
    with pytest.raises((TypeError, ValueError)):
        factory()

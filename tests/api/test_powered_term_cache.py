"""Public owner reuse preserves exact views and per-term HashLife accounting."""

from __future__ import annotations

from typing import Never, cast

import pytest

from number_compiler.api.number_api import (
    NumberCompiler,
    PoweredCollatzTermPayload,
    PoweredReverseAddTermPayload,
)
from number_compiler.api.query_types import CollatzTermQuery, ReverseAddTermQuery
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def test_alias_reuses_warm_hashlife_owner_without_recompiling(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    compiler = NumberCompiler()
    first = compiler.project(ReverseAddTermQuery(5, seed=196))
    assert isinstance(first.payload, PoweredReverseAddTermPayload)
    assert first.digit(0) == 4
    before = first.payload.power_metrics()

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("repeated public request rebuilt the powered owner")

    monkeypatch.setattr(ReverseAddPoweredTerm, "__init__", forbidden)
    repeat = compiler.project(ReverseAddTermQuery(5, seed=196, base=10))
    assert isinstance(repeat.payload, PoweredReverseAddTermPayload)
    assert repeat.payload.term is first.payload.term
    assert repeat.digit(0) == 4
    after = repeat.payload.power_metrics()
    assert after.completed_result_evaluations == before.completed_result_evaluations
    assert after.completed_result_entries == before.completed_result_entries
    assert after.point_queries == before.point_queries + 1
    assert compiler.powered_cache_info() == {
        "capacity": 8,
        "retained_terms": 1,
        "hits": 1,
        "misses": 1,
        "evictions": 0,
    }


def test_collatz_radix_views_share_the_binary_owner_not_the_payload() -> None:
    compiler = NumberCompiler()
    binary = compiler.project(CollatzTermQuery(4, seed=27, radix=2))
    ternary = compiler.project(CollatzTermQuery(4, seed=27, radix=3))
    assert isinstance(binary.payload, PoweredCollatzTermPayload)
    assert isinstance(ternary.payload, PoweredCollatzTermPayload)
    assert binary.payload.term is ternary.payload.term
    assert binary.source_radix == 2 and ternary.source_radix == 3
    assert binary.digit(0) == 0 and ternary.digit(0) == 2  # exact endpoint 62
    assert binary.materialize() == ternary.materialize() == 62
    assert compiler.powered_cache_info()["hits"] == 1


def test_seeds_powers_and_radices_keep_distinct_reverse_add_owners() -> None:
    compiler = NumberCompiler()
    requests = (
        ("reverse-add", 0, 6, 2),
        ("reverse-add", 0, 6, 10),
        ("reverse-add", 0, 7, 2),
        ("reverse-add", 1, 6, 2),
    )
    terms = [
        compiler.project(ReverseAddTermQuery(step, seed=seed, base=base))
        for _, step, seed, base in requests
    ]
    owners: list[ResourceLedger] = []
    for term in terms:
        assert isinstance(term.payload, PoweredReverseAddTermPayload)
        owners.append(term.payload.term.resource_ledger)
    assert len({id(owner) for owner in owners}) == len(requests)
    assert compiler.powered_cache_info()["misses"] == len(requests)


def test_lru_eviction_and_clear_leave_returned_owners_alive() -> None:
    compiler = NumberCompiler(max_cached_terms=2)
    old = compiler.project(ReverseAddTermQuery(2, seed=196))
    compiler.project(ReverseAddTermQuery(0, seed=196))
    assert compiler.project(ReverseAddTermQuery(2, seed=196)).payload == old.payload
    compiler.project(
        ReverseAddTermQuery(1, seed=196)
    )  # evicts generation zero, not generation two
    assert compiler.project(ReverseAddTermQuery(2, seed=196)).payload == old.payload
    assert compiler.powered_cache_info()["evictions"] == 1
    compiler.clear_powered_cache()
    assert compiler.powered_cache_info()["retained_terms"] == 0
    assert old.materialize() == 1675
    fresh = compiler.project(ReverseAddTermQuery(2, seed=196))
    assert fresh.payload != old.payload
    assert fresh.materialize() == 1675


def test_disabled_cache_and_invalid_requests_do_not_reuse_an_owner() -> None:
    compiler = NumberCompiler(max_cached_terms=0)
    assert (
        compiler.project(ReverseAddTermQuery(0, seed=196)).payload
        != compiler.project(ReverseAddTermQuery(0, seed=196)).payload
    )
    before = compiler.powered_cache_info()
    for bad in (True, 1.0, "1"):
        with pytest.raises((TypeError, ValueError)):
            compiler.project(ReverseAddTermQuery(cast(int, bad), seed=196))
    with pytest.raises(ValueError):
        compiler.project(CollatzTermQuery(0, seed=27, radix=5))
    assert compiler.powered_cache_info() == before
    assert before["retained_terms"] == 0 and before["misses"] == 2


def test_changed_source_parameters_cannot_poison_a_cached_request() -> None:
    compiler = NumberCompiler()
    old = compiler.project(ReverseAddTermQuery(0, seed=196))
    assert isinstance(old.payload, PoweredReverseAddTermPayload)
    old.payload.term.seed = 197
    replacement = compiler.project(ReverseAddTermQuery(0, seed=196))
    assert isinstance(replacement.payload, PoweredReverseAddTermPayload)
    assert replacement.payload.term is not old.payload.term
    assert replacement.materialize() == 196

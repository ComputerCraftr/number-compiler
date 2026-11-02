"""Adversarial snapshots and optional result-cache publication checks."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import reverse_add as metric_keys
from number_compiler.sequences.reverse_add import temporal_laurent_accumulator
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from number_compiler.sequences.reverse_add.temporal_accumulator99 import (
    RankOneAccumulatorAction99,
)
from number_compiler.sequences.reverse_add.temporal_laurent_accumulator import (
    SourceBoundLaurentResult,
)
from tests.support.reference_arithmetic import literal_reverse_add


def _assert_laurent_cache_released(term: ReverseAddPoweredTerm) -> None:
    assert (term.resource_ledger.entries, term.resource_ledger.nodes) == (0, 0)
    result_caches = tuple(
        owner
        for owner in term.resource_ledger.inventory()
        if owner.name.startswith("reverse-laurent-result-cache-")
    )
    assert result_caches
    assert all(
        owner.disposed and owner.entries == owner.nodes == 0 for owner in result_caches
    )


def test_accumulator_cache_detects_nested_state_mutation() -> None:
    term = ReverseAddPoweredTerm(196, 2048)
    result = term.temporal_accumulator99()
    state = result.state
    original = state.a
    object.__setattr__(state, "a", (original + 1) % 99)
    try:
        with pytest.raises(ValueError, match="source-bound result"):
            term.temporal_accumulator99()
    finally:
        object.__setattr__(state, "a", original)
        term.resource_ledger.evict_query_memos()


def test_accumulator_cache_detects_nested_action_mutation() -> None:
    term = ReverseAddPoweredTerm(196, 0)
    result = term.temporal_accumulator99()
    action = result.action
    original_multiplier = action.multiplier
    original_coupling = action.coupling
    assert original_multiplier == 1 and original_coupling == 0
    changed_coupling = (original_coupling + 1) % 99
    object.__setattr__(action, "coupling", changed_coupling)
    object.__setattr__(action, "multiplier", (1 + 3 * changed_coupling) % 99)
    try:
        with pytest.raises(ValueError, match="source-bound result"):
            term.temporal_accumulator99()
        object.__setattr__(action, "multiplier", original_multiplier)
        object.__setattr__(action, "coupling", original_coupling)
        object.__setattr__(action, "multiplier", True)
        with pytest.raises(TypeError, match="rank-one multiplier"):
            term.temporal_accumulator99()
    finally:
        object.__setattr__(action, "multiplier", original_multiplier)
        object.__setattr__(action, "coupling", original_coupling)
        term.resource_ledger.evict_query_memos()


def test_accumulator_cache_rejects_boolean_alias_in_nested_state() -> None:
    term = ReverseAddPoweredTerm(196, 0)
    result = term.temporal_accumulator99()
    state = result.state
    assert state.phase == 0 and type(state.phase) is int
    object.__setattr__(state, "phase", False)
    try:
        with pytest.raises(TypeError, match="accumulator phase"):
            term.temporal_accumulator99()
    finally:
        object.__setattr__(state, "phase", 0)
        term.resource_ledger.evict_query_memos()


def test_accumulator_warm_hit_does_not_construct_nested_actions(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = ReverseAddPoweredTerm(196, 2048)
    result = term.temporal_accumulator99()

    def forbidden_init(
        _action: RankOneAccumulatorAction99, _multiplier: int, _coupling: int
    ) -> None:
        raise AssertionError("warm mod-99 cache hit rebuilt its rank-one action")

    monkeypatch.setattr(RankOneAccumulatorAction99, "__init__", forbidden_init)
    assert term.temporal_accumulator99() is result


def test_laurent_cache_budget_refusal_returns_result_without_retention(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_reserve = ResourceLedger.reserve
    original_projection = temporal_laurent_accumulator.source_bound_laurent_projection
    projection_calls = 0

    def count_projection(
        seed: int,
        generation: int,
        *,
        ledger: ResourceLedger,
        scratch_owner: int,
    ) -> SourceBoundLaurentResult:
        nonlocal projection_calls
        projection_calls += 1
        return original_projection(
            seed,
            generation,
            ledger=ledger,
            scratch_owner=scratch_owner,
        )

    def refuse_optional_cache(
        ledger: ResourceLedger,
        owner: int,
        entries: int = 0,
        nodes: int = 0,
    ) -> None:
        if ledger.inventory_owner(owner).name.startswith(
            "reverse-laurent-result-cache-"
        ):
            raise BlockContextBudgetExceeded("injected optional cache refusal")
        original_reserve(ledger, owner, entries=entries, nodes=nodes)

    monkeypatch.setattr(
        temporal_laurent_accumulator,
        "source_bound_laurent_projection",
        count_projection,
    )
    monkeypatch.setattr(ResourceLedger, "reserve", refuse_optional_cache)

    term = ReverseAddPoweredTerm(196, 4)
    result = term.temporal_laurent_accumulator()
    expected = literal_reverse_add(196, 4)
    assert projection_calls == 1
    assert result.generation == 4
    assert (result.target_mod7, result.target_mod198) == (
        expected % 7,
        expected % 198,
    )
    _assert_laurent_cache_released(term)
    assert (
        term.resource_ledger.counters[
            metric_keys.REVERSE_LAURENT_CACHE_PUBLICATION_FAILURES
        ]
        == 1
    )


def test_laurent_warm_cache_hit_does_not_reconstruct_result(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = ReverseAddPoweredTerm(196, 16)
    result = term.temporal_laurent_accumulator()

    def forbidden_projection(
        *_args: object, **_kwargs: object
    ) -> SourceBoundLaurentResult:
        raise AssertionError("warm Laurent cache hit reconstructed its result")

    monkeypatch.setattr(
        temporal_laurent_accumulator,
        "source_bound_laurent_projection",
        forbidden_projection,
    )
    assert term.temporal_laurent_accumulator() is result
    assert term.resource_ledger.counters[metric_keys.REVERSE_LAURENT_CACHE_HITS] == 1


def test_laurent_cache_does_not_swallow_nonbudget_publication_errors(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_reserve = ResourceLedger.reserve
    construction_error = RuntimeError("injected invalid cache publication")

    def fail_optional_cache(
        ledger: ResourceLedger,
        owner: int,
        entries: int = 0,
        nodes: int = 0,
    ) -> None:
        if ledger.inventory_owner(owner).name.startswith(
            "reverse-laurent-result-cache-"
        ):
            raise construction_error
        original_reserve(ledger, owner, entries=entries, nodes=nodes)

    monkeypatch.setattr(ResourceLedger, "reserve", fail_optional_cache)
    term = ReverseAddPoweredTerm(196, 4)
    with pytest.raises(RuntimeError, match="invalid cache publication"):
        term.temporal_laurent_accumulator()
    _assert_laurent_cache_released(term)

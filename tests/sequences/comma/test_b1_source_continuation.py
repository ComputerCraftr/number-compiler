"""Contract tests for the production comma semantic continuation owner."""

from __future__ import annotations

from collections.abc import MutableMapping
from typing import cast

import pytest

import number_compiler.sequences.comma.semantic_continuation as semantic
from devtools.verification.comma_b1_quotient import offset_orbit, offset_representatives
from devtools.verification.comma_b1_source_continuation import (
    DifferentialResult,
    audit_complete_return_clock_quotient,
    differential_against_observe,
    production_semantic_owner,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.comma.arithmetic import CycleTransfer, cycle_transfer
from number_compiler.sequences.comma.boundary_chart import BoundaryChart
from number_compiler.sequences.comma.semantic_continuation import (
    ContinuationID,
    SemanticAction,
    SemanticContinuation,
    SemanticContinuationArena,
    TerminalWeight,
)


def _root(offset: int, delta: int = 0) -> BoundaryChart:
    return BoundaryChart("entry", 1, delta, offset)


def _resolver(root: int) -> BoundaryChart:
    return _root(offset_representatives()[offset_orbit(root)])


@pytest.fixture(scope="module")
def built_view() -> SemanticContinuation:
    return production_semantic_owner()


def test_source_delta_is_occurrence_rebase_data(
    built_view: SemanticContinuation,
) -> None:
    source = _root(offset_representatives()[0])
    shifted = _root(source.coordinate, 1849)
    source_identifier, source_shift = built_view.source_address(source)
    shifted_identifier, shifted_shift = built_view.source_address(shifted)
    assert shifted_identifier == source_identifier
    assert source_shift == 0
    assert shifted_shift == 1849
    assert (
        built_view.evaluate(shifted, 17).action
        == built_view.evaluate(source, (17 + 1849) % 924).action
    )


def test_compiled_ids_are_scoped_and_gotos_descend(
    built_view: SemanticContinuation,
) -> None:
    assert all(
        type(identifier) is ContinuationID for identifier in built_view.actions_by_id
    )
    for identifier, actions in built_view.actions_by_id.items():
        for action in actions:
            if action.kind == "goto":
                assert action.target is not None
                assert action.target.owner is identifier.owner
                assert action.target.local_id < identifier.local_id
    other_arena = SemanticContinuationArena()
    foreign = other_arena.compile(_root(offset_representatives()[1]))
    with pytest.raises(ValueError, match="different arena"):
        built_view.evaluate_id(foreign, 0)


def test_warm_lookup_skips_cold_source_work(monkeypatch: pytest.MonkeyPatch) -> None:
    arena = SemanticContinuationArena()
    source = _root(offset_representatives()[0])
    first = arena.compile(source)

    def cold_work_forbidden(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("warm source lookup rebuilt cold arithmetic")

    monkeypatch.setattr(semantic, "_raw_action", cold_work_forbidden)
    assert arena.compile(_root(source.coordinate, 3)) == first


def test_discovery_builds_one_cycle_transfer_per_entry_source(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena = SemanticContinuationArena()
    source = _root(offset_representatives()[0])
    original = cycle_transfer
    transfers: list[tuple[int, int]] = []

    def counted(leading: int, digit: int) -> CycleTransfer:
        transfers.append((leading, digit))
        return original(leading, digit)

    monkeypatch.setattr(semantic, "cycle_transfer", counted)
    arena.compile(source)
    entries = [state for state in arena._raw if state.kind == "entry"]
    assert len(transfers) == len(entries)
    assert arena.ledger.counters["comma_semantic_cycle_transfer_builds"] == len(entries)
    assert arena.ledger.counters["comma_semantic_action_evaluations"] == sum(
        len(actions) for actions in arena._raw.values()
    )
    assert set(transfers) == {
        (state.leading, state.coordinate % 10) for state in entries
    }


def test_failed_discovery_rolls_back_rows_and_reservations(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena = SemanticContinuationArena()
    source = _root(offset_representatives()[0])
    original = semantic._raw_action
    calls = 0

    def poison(
        source_value: BoundaryChart,
        phase: int,
        transfer: CycleTransfer | None,
    ) -> object:
        nonlocal calls
        calls += 1
        if calls == 3:
            raise RuntimeError("poisoned semantic action")
        return original(source_value, phase, transfer)

    monkeypatch.setattr(semantic, "_raw_action", poison)
    with pytest.raises(RuntimeError, match="poisoned"):
        arena.compile(source)
    assert not arena._raw
    assert not arena._transitions
    assert not arena._source_ids
    assert arena.ledger.entries == 0
    assert arena.ledger.nodes == 0
    assert arena.ledger.counters["comma_semantic_action_failures"] == 1
    monkeypatch.setattr(semantic, "_raw_action", original)
    identifier = arena.compile(source)
    assert arena.compile(source) == identifier
    assert arena.ledger.entries > 0
    assert arena.ledger.nodes > 0


def test_signature_publication_failure_restores_id_allocator(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena = SemanticContinuationArena()
    source = _root(offset_representatives()[0])
    original_store = arena._store
    failed = False

    def poison_signature_store(
        mapping: MutableMapping[object, object],
        owner: int,
        key: object,
        value: object,
        *,
        nodes: int = 1,
    ) -> None:
        nonlocal failed
        if mapping is arena._signatures and not failed:
            failed = True
            raise RuntimeError("poisoned signature publication")
        original_store(mapping, owner, key, value, nodes=nodes)

    monkeypatch.setattr(arena, "_store", poison_signature_store)
    with pytest.raises(RuntimeError, match="poisoned signature"):
        arena.compile(source)
    assert arena._next_id == 0
    assert not arena._raw
    assert not arena._source_ids
    monkeypatch.setattr(arena, "_store", original_store)
    identifier = arena.compile(source)
    clean_arena = SemanticContinuationArena()
    clean_identifier = clean_arena.compile(source)
    assert identifier.local_id == clean_identifier.local_id


def test_budget_failure_does_not_publish_partial_source() -> None:
    arena = SemanticContinuationArena(ledger=ResourceLedger(max_nodes=0))
    with pytest.raises(BlockContextBudgetExceeded):
        arena.compile(_root(offset_representatives()[0]))
    assert arena.ledger.entries == 0
    assert arena.ledger.nodes == 0
    assert not arena._raw
    assert not arena._source_ids


def test_powered_count_zero_is_identity_and_count_is_exact(
    built_view: SemanticContinuation,
) -> None:
    source = _root(offset_representatives()[0])
    application = built_view.powered_application(source_for_live_root=_resolver)
    try:
        zero = application.apply(source, 0, 0)
        assert zero.action.kind == "identity"
        assert zero.terminal is None
        assert zero.complete_decades == 0
        assert zero.exponent_advance == 0
        one = application.apply(source, 0, 1)
        assert one.complete_decades <= 1
        if one.terminal is None:
            assert one.complete_decades == 1
    finally:
        application.close()


def test_powered_delta_transport_and_repeated_parent_cache(
    built_view: SemanticContinuation,
) -> None:
    source = _root(offset_representatives()[0])
    application = built_view.powered_application(source_for_live_root=_resolver)
    try:
        first = application.apply(source, 17, 15)
        requests = application.requests
        second = application.apply(source, 17, 15)
        assert second == first
        assert application.requests > requests
        assert application.hits > 0
        assert application.misses > 0
        shifted = application.apply(source, 17, 3, delta=1849)
        rebased = application.apply(source, (17 + 1849) % 924, 3)
        assert shifted == rebased
        if first.terminal is not None:
            assert first.action.kind == "stop"
            assert first.action.stop_j is not None
            assert first.terminal.d == 9 * first.complete_decades + first.action.stop_j
    finally:
        retained = built_view.ledger.entries
        application.close()
        assert built_view.ledger.entries < retained


def test_equivalent_effective_phase_reuses_parent_without_one_step(
    built_view: SemanticContinuation,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = _root(offset_representatives()[0])
    application = built_view.powered_application(source_for_live_root=_resolver)
    try:
        first = application.apply(source, 1, 1, delta=2)

        def poison(*_args: object, **_kwargs: object) -> object:
            raise AssertionError("equivalent effective phase rebuilt B1")

        monkeypatch.setattr(application, "_one", poison)
        second = application.apply(source, 2, 1, delta=1)
        assert second == first
    finally:
        application.close()


def test_evaluate_charges_each_local_transition_visit(
    built_view: SemanticContinuation,
) -> None:
    source = _root(offset_representatives()[0])
    before = built_view.ledger.counters.get("comma_semantic_occurrence_visits", 0)
    built_view.evaluate(source, 0)
    after = built_view.ledger.counters["comma_semantic_occurrence_visits"]
    assert after > before


def test_live_root_binding_is_cached_with_the_application() -> None:
    arena = SemanticContinuationArena()
    roots = tuple(_root(offset) for offset in offset_representatives())
    arena.compile_many(roots)
    view = arena.publish(roots)
    calls = 0

    def resolver(root: int) -> BoundaryChart:
        nonlocal calls
        calls += 1
        return _resolver(root)

    application = view.powered_application(source_for_live_root=resolver)
    try:
        application.apply(roots[0], 0, 2)
        first_calls = calls
        application.apply(roots[0], 0, 2)
        assert calls == first_calls
    finally:
        application.close()


def test_sharp_b32_stop_weight_preserves_h26_and_j3() -> None:
    stop = TerminalWeight.local(3).after_complete_decades(26)
    assert stop.d == 237
    assert stop.height == 26
    assert stop.stop_j == 3
    assert stop.fork_a == 5


def test_source_alias_types_are_rejected() -> None:
    with pytest.raises(ValueError):
        semantic.normalize_source(_root(0, True))
    with pytest.raises(ValueError):
        semantic.normalize_source(_root(0, cast(int, 1.0)))
    with pytest.raises(ValueError):
        semantic.normalize_source(BoundaryChart("near", 1, 0, True))
    with pytest.raises(ValueError):
        SemanticAction("live", live_root=0, exponent_advance=True)


def test_production_differential_result_shape(built_view: SemanticContinuation) -> None:
    result = differential_against_observe(
        built_view, tuple(_root(x) for x in offset_representatives()[:1])
    )
    assert isinstance(result, DifferentialResult)
    assert result.checked == 924
    assert result.mismatches == ()


def test_differential_uses_root_orbit_for_nonconsecutive_subsets() -> None:
    roots = tuple(_root(offset_representatives()[index]) for index in (7, 23))
    result = differential_against_observe(production_semantic_owner(roots), roots)
    assert result.checked == 2 * 924
    assert result.mismatches == ()


@pytest.mark.validation
def test_common_return_shift_does_not_rebase_the_physical_successor_clock(
    built_view: SemanticContinuation,
) -> None:
    view = built_view
    audit = audit_complete_return_clock_quotient(view)
    by_id = {identifier.local_id: identifier for identifier in view.source_ids.values()}
    found_transport_difference = False
    for witness in audit.shift_witnesses:
        representative = by_id[witness.representative]
        member = by_id[witness.member]
        for phase in range(924):
            representative_action = view.evaluate_id(
                representative, (phase + witness.shift) % 924
            )
            member_action = view.evaluate_id(member, phase)
            if (
                representative_action.kind != "live"
                or member_action.kind != "live"
                or representative_action.live_root != member_action.live_root
            ):
                continue
            live_root = member_action.live_root
            assert live_root is not None
            physical_next = view.evaluate(_root(live_root), (phase + 1) % 924).action
            translated_next = view.evaluate(
                _root(live_root), (phase + witness.shift + 1) % 924
            ).action
            if physical_next != translated_next:
                found_transport_difference = True
                break
        if found_transport_difference:
            break
    assert found_transport_difference


@pytest.mark.validation
def test_production_owner_matches_independent_full_b1_observer(
    built_view: SemanticContinuation,
) -> None:
    result = differential_against_observe(built_view)
    assert result.checked == 46 * 924
    assert result.mismatches == ()

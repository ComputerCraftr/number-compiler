from __future__ import annotations

from dataclasses import replace
from typing import cast

import pytest

from number_compiler.arithmetic.automata.slp_walks import symbol_at
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.temporal_hashlife_slp import (
    _existing_part,
)


def _literal(seed: int, steps: int) -> int:
    value = seed
    for _ in range(steps):
        value = 2 * int(str(value)[::-1])
    return value


@pytest.mark.parametrize(
    "seed,steps",
    (
        (0, 0),
        (0, 6),
        (10, 0),
        (10, 1),
        (10, 6),
        (12, 4),
        (1001, 5),
        (4721, 8),
    ),
)
def test_scheduler_slp_matches_independent_literal_recurrence(
    seed: int, steps: int
) -> None:
    expected = _literal(seed, steps)
    with DoubleReverseTerm(seed, steps) as term:
        assert term.width() == len(str(expected))
        assert term.materialize(max_bits=expected.bit_length()) == expected
        assert term.digits() == tuple(
            int(character) for character in reversed(str(expected))
        )
        assert term.digit(0) == expected % 10


def test_trailing_zero_contraction_is_applied_on_every_step() -> None:
    with DoubleReverseTerm(10, 1) as term:
        assert term.materialize(max_bits=2) == 2
    with DoubleReverseTerm(100, 1) as term:
        assert term.materialize(max_bits=3) == 2


def test_uncertified_two_step_uses_direct_carry_quotient_without_scalar_replay(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with DoubleReverseTerm(12, 2) as term:

        def forbid_scalar_step(_adapter: object, _root: int) -> int:
            raise AssertionError("T² production route replayed a primitive step")

        monkeypatch.setattr(type(term._adapter), "_apply_word", forbid_scalar_step)
        assert term.materialize(max_bits=8) == _literal(12, 2)
        metrics = term.metrics()
        assert metrics["double_reverse_temporal_square_applications"] == 1
        assert metrics["double_reverse_completed_t2_publications"] == 1
        assert metrics["double_reverse_square_width_guards"] == 1


def test_powered_hashlife_action_and_engine_owners_pass_resource_audit() -> None:
    with DoubleReverseTerm(173488, 8) as term:
        term.prepare_endpoint()
        owners = term.resource_ledger.inventory()
        for suffix in (
            "-temporal-cones",
            "-temporal-slices",
            "-temporal-port-actions",
        ):
            owner = next(item for item in owners if item.name.endswith(suffix))
            assert owner.entries > 0
            if suffix == "-temporal-port-actions":
                assert owner.nodes > owner.entries
        assert collect_ledger_metrics(term.resource_ledger).resource_audit_complete == 1


@pytest.mark.parametrize("memo_name", ("_cone", "_slices"))
def test_same_width_corrupt_temporal_memo_value_fails_payload_audit(
    memo_name: str,
) -> None:
    with DoubleReverseTerm(173488, 8) as term:
        term.prepare_endpoint()
        engine = term._adapter.temporal_hashlife
        memo = getattr(engine, memo_name)
        key, original = next(iter(memo.items()))
        width = term._arena.nodes[original].length
        digits = [symbol_at(term._arena, original, index) for index in range(width)]
        digits[0] = (digits[0] + 1) % 10
        replacement = term._arena.word(digits)
        assert replacement != original
        assert term._arena.nodes[replacement].length == width
        memo[key] = replacement
        metrics = collect_ledger_metrics(term.resource_ledger)
        assert metrics.resource_audit_complete == 1
        assert metrics.forbidden_future_payloads > 0
        assert metrics.representation_boundary_complete == 0


def test_temporal_slice_audit_rejects_cyclic_grammar_in_bounded_work() -> None:
    with DoubleReverseTerm(173488, 2) as term:
        arena = term._arena
        left = arena.terminal(3)
        right = arena.terminal(4)
        cyclic = arena.concat(left, right)
        node = arena.nodes[cyclic]
        object.__setattr__(node, "left", cyclic)
        assert _existing_part(arena, cyclic, 0, 1) is None


@pytest.mark.parametrize("seed", (196, 4721))
def test_uncertified_two_step_square_handles_growth(seed: int) -> None:
    with DoubleReverseTerm(seed, 2) as term:
        assert term.materialize(max_bits=64) == _literal(seed, 2)
        metrics = term.metrics()
        assert metrics["double_reverse_temporal_square_applications"] == 1
        assert metrics.get("double_reverse_square_guard_refusals", 0) == 0


def test_contraction_uses_exact_normalized_temporal_square() -> None:
    with DoubleReverseTerm(10, 2) as term:
        assert term.materialize(max_bits=64) == _literal(10, 2)
        metrics = term.metrics()
        assert metrics["double_reverse_temporal_square_applications"] == 1
        assert metrics["double_reverse_temporal_square_normalizations"] >= 1
        assert metrics["double_reverse_temporal_square_shrink_seams"] >= 1
        assert metrics.get("double_reverse_spatial_transducer_applications", 0) == 0


@pytest.mark.parametrize("seed", (196, 173488))
@pytest.mark.parametrize("horizon", (32, 64, 128, 256))
def test_guarded_temporal_hashlife_matches_literal_long_horizons(
    seed: int, horizon: int
) -> None:
    expected = _literal(seed, horizon)
    with DoubleReverseTerm(seed, horizon) as term:
        assert term.materialize(max_bits=4096) == expected
        metrics = term.metrics()
        assert metrics["double_reverse_temporal_hashlife_publications"] > 0
        assert metrics["double_reverse_hashlife_cones"] > 0
        assert metrics["double_reverse_hashlife_tile_selections"] > 0


def test_certified_scheduler_route_does_not_replay_scalar_steps(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with DoubleReverseTerm(173488, 32) as term:

        def forbid_scalar(_adapter: object, _root: int) -> int:
            raise AssertionError("certified temporal route replayed a scalar step")

        monkeypatch.setattr(type(term._adapter), "_apply_word", forbid_scalar)
        monkeypatch.setattr(type(term._adapter), "_general_two_step", forbid_scalar)
        assert term.materialize(max_bits=4096) == _literal(173488, 32)
        metrics = term.metrics()
        assert metrics["double_reverse_hashlife_cones"] > 0
        assert metrics["double_reverse_spatial_transducer_applications"] == 0


def test_warm_parent_action_hit_skips_cone_discovery(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with DoubleReverseTerm(173488, 16) as term:
        engine = term._adapter.temporal_hashlife
        source = term._source.root
        phase = engine.certify(source)
        assert phase is not None
        first = engine.advance_action(source, 8, phase)

        def forbid_discovery(*_args: object) -> int:
            raise AssertionError("warm temporal action repeated cone discovery")

        monkeypatch.setattr(type(engine), "_power_action", forbid_discovery)
        monkeypatch.setattr(type(engine), "_power_of_two", forbid_discovery)
        visits_before = term.metrics()["double_reverse_boundary_node_visits"]
        assert engine.advance_action(source, 8, phase) is first
        metrics = term.metrics()
        assert metrics["double_reverse_temporal_port_action_cache_hits"] > 0
        assert metrics["double_reverse_boundary_node_visits"] > visits_before


def test_same_border_forged_and_mutated_target_are_rejected_by_issuer_binding() -> None:
    with DoubleReverseTerm(173488, 4) as term:
        engine = term._adapter.temporal_hashlife
        source = term._source.root
        phase = engine.certify(source)
        assert phase is not None
        action = engine.advance_action(source, 2, phase)
        target = engine.root_of(action.target)
        width = term._arena.nodes[target].length
        altered = [symbol_at(term._arena, target, index) for index in range(width)]
        altered[2] = (altered[2] + 1) % 10
        forged_root = term._arena.word(altered)
        assert term._arena.nodes[forged_root].length == width
        assert engine.certify(forged_root) == action.phase_out
        forged = replace(action, target=engine._handle(forged_root))
        with pytest.raises(ValueError, match="not published by this owner"):
            engine.validate_action(forged)
        original_local_id = action.target.local_id
        object.__setattr__(action.target, "local_id", forged_root)
        try:
            with pytest.raises(ValueError, match="not published by this owner"):
                engine.validate_action(action)
            with pytest.raises(ValueError, match="not published by this owner"):
                engine.advance_action(source, 2, phase)
        finally:
            object.__setattr__(action.target, "local_id", original_local_id)


def test_temporal_action_rejects_foreign_issuer_and_stale_memo() -> None:
    first = DoubleReverseTerm(173488, 4)
    second = DoubleReverseTerm(173488, 4)
    first_engine = first._adapter.temporal_hashlife
    second_engine = second._adapter.temporal_hashlife
    phase = first_engine.certify(first._source.root)
    assert phase is not None
    action = first_engine.advance_action(first._source.root, 2, phase)
    with pytest.raises(ValueError, match="different arena"):
        second_engine.validate_action(action)
    first.dispose()
    with pytest.raises(ValueError, match="outside its arena"):
        first_engine.validate_action(action)
    second.dispose()


def test_two_step_square_does_not_skip_intermediate_bit_budget_check() -> None:
    with DoubleReverseTerm(12, 2, max_state_bits=4) as term:
        with pytest.raises(BlockContextBudgetExceeded, match="state-bit budget"):
            term.prepare_endpoint()
        metrics = term.metrics()
        assert metrics.get("double_reverse_temporal_square_applications", 0) == 0
        assert metrics["double_reverse_square_bit_budget_guard_refusals"] > 0


def test_materialization_checks_the_exact_value_not_a_decimal_width_bound() -> None:
    with DoubleReverseTerm(10, 1) as term:
        assert term.materialize(max_bits=2) == 2
        with pytest.raises(BlockContextBudgetExceeded, match="materialization budget"):
            term.materialize(max_bits=1)


def test_state_bit_cap_uses_exact_value_when_decimal_bound_is_inconclusive() -> None:
    with DoubleReverseTerm(10, 1, max_state_bits=4) as term:
        assert term.materialize(max_bits=4) == 2

    with DoubleReverseTerm(60, 1, max_state_bits=6) as term:
        assert term.materialize(max_bits=6) == 12
        term.prepare_endpoint()
        assert term.metrics()["double_reverse_threshold_conversion_bytes"] > 0
        assert len(term._threshold_memo) == 1

    with (
        DoubleReverseTerm(9, 1, max_state_bits=4) as term,
        pytest.raises(BlockContextBudgetExceeded, match="state-bit budget"),
    ):
        term.prepare_endpoint()


def test_step_and_initial_state_limits_are_checked_before_execution() -> None:
    with pytest.raises(BlockContextBudgetExceeded, match="step budget"):
        DoubleReverseTerm(10, 2, max_steps=1)
    with pytest.raises(BlockContextBudgetExceeded, match="source"):
        DoubleReverseTerm(10, 0, max_state_bits=3)


def test_partial_stream_cancellation_releases_temporary_traversal_storage() -> None:
    term = DoubleReverseTerm(4721, 8)
    stream = term.iter_digits()
    next(stream)
    stream.close()

    scratch = next(
        item
        for item in term.resource_ledger.inventory()
        if item.name.endswith("-scratch")
    )
    assert scratch.entries == scratch.nodes == 0
    assert term.metrics()["double_reverse_output_stream_cancellations"] == 1
    term.dispose()
    assert (
        sum(item.accounting_delta or 0 for item in term.resource_ledger.inventory())
        == 0
    )


def test_output_stream_resumed_after_disposal_rejects_stale_arena() -> None:
    # This endpoint emits one digit, so resuming after disposal checks the
    # iterator's final-yield boundary rather than only a pending subtree.
    term = DoubleReverseTerm(10, 1)
    stream = term.iter_digits()
    assert next(stream) == 2
    term.dispose()

    with pytest.raises(ValueError, match="disposed double-reverse term"):
        next(stream)

    scratch = next(
        item
        for item in term.resource_ledger.inventory()
        if item.name.endswith("-scratch")
    )
    assert scratch.entries == scratch.nodes == 0


def test_cancelled_walk_defers_and_retries_scratch_retirement(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = DoubleReverseTerm(4721, 8)
    stream = term.iter_digits()
    next(stream)
    term.dispose()
    scratch = next(
        item
        for item in term.resource_ledger.inventory()
        if item.name.endswith("-scratch")
    )
    assert not term._cleanup_complete
    assert not scratch.disposed
    assert scratch.entries > 0

    original_mark_disposed = term.resource_ledger.mark_disposed
    failed_once = False

    def fail_scratch_once(owner: int) -> None:
        nonlocal failed_once
        if owner == scratch.owner and not failed_once:
            failed_once = True
            raise RuntimeError("injected deferred scratch disposal failure")
        original_mark_disposed(owner)

    monkeypatch.setattr(term.resource_ledger, "mark_disposed", fail_scratch_once)
    stream.close()
    after_close = next(
        item for item in term.resource_ledger.inventory() if item.owner == scratch.owner
    )
    assert failed_once
    assert not term._cleanup_complete
    assert not after_close.disposed
    assert after_close.entries == after_close.nodes == 0

    monkeypatch.setattr(term.resource_ledger, "mark_disposed", original_mark_disposed)
    term.dispose()
    assert term._cleanup_complete
    accounts = term.resource_ledger.inventory()
    assert term.resource_ledger.entries == term.resource_ledger.nodes == 0
    assert all(item.entries == item.nodes == 0 for item in accounts)
    assert all(
        item.accounting_delta == 0
        for item in accounts
        if item.accounting_delta is not None
    )


def test_closed_term_rejects_endpoint_and_context_access() -> None:
    term = DoubleReverseTerm(12, 2)
    term.dispose()
    with pytest.raises(ValueError, match="disposed"):
        term.prepare_endpoint()
    with pytest.raises(ValueError, match="disposed"):
        term.width()
    with pytest.raises(ValueError, match="disposed"):
        term.__enter__()


def test_successful_construction_keeps_scheduler_and_memos_live() -> None:
    with DoubleReverseTerm(10, 1) as term:
        assert not term._arena._closed
        assert not term._adapter._closed
        assert not term._threshold_memo._disposed
        assert term.materialize(max_bits=4) == 2


@pytest.mark.parametrize("phase", (True, 1.0, -1, 4))
@pytest.mark.parametrize("warm", (False, True))
@pytest.mark.parametrize("method", ("advance_action", "_power_action"))
def test_temporal_phase_rejects_numeric_alias_before_lookup(
    phase: object, warm: bool, method: str
) -> None:
    with DoubleReverseTerm(173488, 0) as term:
        engine = term._adapter.temporal_hashlife
        root = term._arena.word((1, 7, 3, 4, 4, 2))
        assert engine.certify(root) == 1
        if warm:
            engine.advance_action(root, 1, 1)
        hits = term.resource_ledger.counters.get(
            "double_reverse_temporal_port_action_cache_hits", 0
        )
        action = (
            engine.advance_action
            if method == "advance_action"
            else engine._power_action
        )
        with pytest.raises(ValueError):
            action(root, 1, cast(int, phase))
        assert (
            term.resource_ledger.counters.get(
                "double_reverse_temporal_port_action_cache_hits", 0
            )
            == hits
        )

"""Finite source-word scalar weights over exact spatial ``2rev10`` steps."""

from __future__ import annotations

from collections.abc import Callable, Generator, Iterable
from contextlib import contextmanager
from dataclasses import replace
from typing import Never

import pytest

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp import SLPArena, SLPNode
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.resources.ledger import LedgerReservation, ResourceLedger
from number_compiler.resources.metric_keys import double_reverse as _double_reverse_keys
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.temporal_alternating_carry import (
    fold_two_step_slp,
)
from number_compiler.sequences.double_reverse.temporal_hashlife import (
    DoubleReverseTemporalHashlife,
)
from number_compiler.sequences.double_reverse.temporal_weighted_laurent import (
    ExactSourceWordCocycle,
)


def _digits(value: int) -> tuple[int, ...]:
    return tuple(int(digit) for digit in str(value))


def _integer(arena: SLPArena, root: int) -> int:
    return int("".join(str(digit) for digit in arena.materialize(root)))


def _reverse(value: int) -> int:
    reversed_value = 0
    while value:
        value, digit = divmod(value, 10)
        reversed_value = 10 * reversed_value + digit
    return reversed_value


def _f(value: int) -> int:
    return 2 * _reverse(2 * _reverse(value))


@contextmanager
def _reservation_scope(
    ledger: ResourceLedger, name: str
) -> Generator[tuple[int, LedgerReservation], None, None]:
    owner = ledger.register(name, "workspace")
    try:
        with LedgerReservation(ledger, owner) as reservation:
            yield owner, reservation
    finally:
        ledger.retire_unpublished_owner(owner)


def _spatial_step(
    arena: SLPArena, source_root: int, reservation: LedgerReservation
) -> ExactSourceWordCocycle:
    projection = fold_two_step_slp(arena, source_root)
    return ExactSourceWordCocycle.from_spatial(
        projection,
        arena,
        expected_source_root=source_root,
        reservation=reservation,
    )


def test_spatial_cocycle_carries_exact_source_sum_and_root_seams() -> None:
    arena = SLPArena()
    ledger = ResourceLedger()
    try:
        with _reservation_scope(ledger, "nc19-source-word") as (
            owner,
            reservation,
        ):
            first_source = arena.word(_digits(168))
            first = _spatial_step(arena, first_source, reservation)
            first_target = first.target_root
            assert _integer(arena, first_target) == _f(168) == 4542
            assert ledger.account_usage(owner) == (6, 6)

            second = _spatial_step(arena, first_target, reservation)
            second_target = second.target_root
            assert _integer(arena, second_target) == _f(4542) == 16188
            assert ledger.account_usage(owner) == (12, 12)

            joined = first.then(second)
            assert ledger.account_usage(owner) == (15, 15)
            assert joined.source_root == first_source
            assert joined.target_root == second_target
            assert joined.f_steps == 2
            assert joined.source_increment_mod(arena, 198) == (168 + 4542) % 198
            assert ledger.account_usage(owner) == (15, 15)
        assert ledger.account_usage(owner) == (0, 0)
    finally:
        arena.clear()


def test_unequal_ordered_sources_with_equal_residues_do_not_join() -> None:
    arena = SLPArena()
    ledger = ResourceLedger()
    try:
        with _reservation_scope(ledger, "nc19-unequal-words") as (_, reservation):
            first = _spatial_step(arena, arena.word(_digits(168)), reservation)
            wrong_source = arena.word(_digits(6522))
            wrong = _spatial_step(arena, wrong_source, reservation)
            assert (
                arena.nodes[first.target_root].length
                == arena.nodes[wrong_source].length
            )
            for modulus in (198, 1980):
                assert _integer(arena, first.target_root) % modulus == (
                    _integer(arena, wrong_source) % modulus
                )

            with pytest.raises(ValueError, match="exact source seam"):
                first.then(wrong)
    finally:
        arena.clear()


def test_spatial_cocycle_requires_full_canonical_source_not_a_zero_suffixed_word() -> (
    None
):
    arena = SLPArena()
    ledger = ResourceLedger()
    try:
        with _reservation_scope(ledger, "nc19-canonical-source") as (_, reservation):
            source = arena.word(_digits(1680))
            projection = fold_two_step_slp(arena, source)
            with pytest.raises(ValueError, match="trailing-zero-free"):
                ExactSourceWordCocycle.from_spatial(
                    projection,
                    arena,
                    expected_source_root=source,
                    reservation=reservation,
                )
    finally:
        arena.clear()


def test_spatial_cocycle_refuses_the_next_step_at_a_trailing_zero_seam() -> None:
    arena = SLPArena()
    ledger = ResourceLedger()
    try:
        with _reservation_scope(ledger, "nc19-zero-seam") as (_, reservation):
            first_source = arena.word(_digits(52))
            first = _spatial_step(arena, first_source, reservation)
            assert _integer(arena, first.target_root) == _f(52) == 10

            with pytest.raises(ValueError, match="trailing-zero-free"):
                _spatial_step(arena, first.target_root, reservation)
    finally:
        arena.clear()


def test_spatial_cocycle_requires_the_expected_source_root() -> None:
    arena = SLPArena()
    ledger = ResourceLedger()
    try:
        with _reservation_scope(ledger, "nc19-expected-source") as (_, reservation):
            source = arena.word(_digits(168))
            projection = fold_two_step_slp(arena, source)
            equal_width = arena.word(_digits(169))
            assert arena.nodes[equal_width].length == arena.nodes[source].length
            with pytest.raises(ValueError, match="another or stale source"):
                ExactSourceWordCocycle.from_spatial(
                    projection,
                    arena,
                    expected_source_root=equal_width,
                    reservation=reservation,
                )
    finally:
        arena.clear()


def test_cocycle_temporary_reservation_is_released_after_refusal() -> None:
    arena = SLPArena()
    ledger = ResourceLedger(max_nodes=11, max_cache_entries=11)
    try:
        with _reservation_scope(ledger, "nc19-refused-source-word") as (
            owner,
            reservation,
        ):
            cocycle = _spatial_step(arena, arena.word(_digits(168)), reservation)
            assert ledger.account_usage(owner) == (6, 6)
            with pytest.raises(BlockContextBudgetExceeded):
                cocycle.source_increment_mod(arena, 198)
            assert ledger.account_usage(owner) == (6, 6)
    finally:
        arena.clear()


def test_cocycle_unwinds_all_temporary_reservations_after_fold_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena = SLPArena()
    ledger = ResourceLedger()
    try:
        with _reservation_scope(ledger, "nc19-failed-source-word-fold") as (
            owner,
            reservation,
        ):
            source = arena.word(_digits(168))
            cocycle = _spatial_step(arena, source, reservation)

            def fail_after_partial_fold_reservations(
                _arena: object,
                root: int,
                *,
                on_schedule: Callable[[int], None],
                on_pending: Callable[[SLPNode], None],
                on_reduce: Callable[[int], None],
                **_kwargs: object,
            ) -> Never:
                on_schedule(3)
                on_pending(arena.nodes[root])
                on_reduce(root)
                raise RuntimeError("simulated SLP fold failure")

            from number_compiler.sequences.double_reverse import (
                temporal_weighted_laurent,
            )

            monkeypatch.setattr(
                temporal_weighted_laurent,
                "fold_slp_dag",
                fail_after_partial_fold_reservations,
            )
            with pytest.raises(RuntimeError, match="SLP fold failure"):
                cocycle.source_increment_mod(arena, 198)
            assert ledger.account_usage(owner) == (6, 6)
    finally:
        arena.clear()


def test_cocycle_unwinds_other_groups_after_release_commits_then_raises(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena = SLPArena()
    ledger = ResourceLedger()
    try:
        with _reservation_scope(ledger, "nc19-post-commit-source-word-fold") as (
            owner,
            reservation,
        ):
            cocycle = _spatial_step(arena, arena.word(_digits(168)), reservation)
            original_release = ResourceLedger.release
            raised_after_commit = False

            def release_then_fail_once(
                current_ledger: ResourceLedger,
                current_owner: int,
                entries: int = 0,
                nodes: int = 0,
            ) -> None:
                nonlocal raised_after_commit
                original_release(
                    current_ledger,
                    current_owner,
                    entries=entries,
                    nodes=nodes,
                )
                if (
                    not raised_after_commit
                    and current_owner == owner
                    and entries > 1
                    and nodes > 1
                ):
                    raised_after_commit = True
                    raise RuntimeError("simulated post-commit fold release failure")

            monkeypatch.setattr(ResourceLedger, "release", release_then_fail_once)
            with pytest.raises(RuntimeError, match="post-commit fold release"):
                cocycle.source_increment_mod(arena, 198)
            assert raised_after_commit
            assert ledger.account_usage(owner) == (6, 6)
    finally:
        arena.clear()


def test_repeat_source_word_is_folded_by_the_shared_ordered_power() -> None:
    arena = SLPArena()
    ledger = ResourceLedger()
    try:
        with _reservation_scope(ledger, "nc19-repeat-source-word") as (
            owner,
            reservation,
        ):
            block = arena.word((1, 6, 8, 2))
            source = arena.repeat(block, 64)
            assert arena.nodes[source].kind == "REPEAT"
            cocycle = _spatial_step(arena, source, reservation)

            expected = 0
            for _ in range(64):
                expected = (expected * 10_000 + 1682) % 1009
            assert cocycle.source_increment_mod(arena, 1009) == expected
            assert ledger.account_usage(owner) == (6, 6)
    finally:
        arena.clear()


def test_replaced_slp_node_invalidates_a_source_word_authority() -> None:
    arena = SLPArena()
    ledger = ResourceLedger()
    try:
        with _reservation_scope(ledger, "nc19-replaced-node") as (_, reservation):
            source = arena.word(_digits(168))
            cocycle = _spatial_step(arena, source, reservation)
            original = arena.nodes[source]
            arena.nodes[source] = replace(original)

            with pytest.raises(ValueError, match="node binding is stale"):
                cocycle.validate(arena)
    finally:
        arena.clear()


def test_closed_reservation_invalidates_retained_source_word() -> None:
    arena = SLPArena()
    ledger = ResourceLedger()
    try:
        with _reservation_scope(ledger, "nc19-closed-source-word") as (
            owner,
            reservation,
        ):
            cocycle = _spatial_step(arena, arena.word(_digits(168)), reservation)
            assert ledger.account_usage(owner) == (6, 6)

        with pytest.raises(ValueError, match="reservation scope is closed"):
            cocycle.validate(arena)
        with pytest.raises(ValueError, match="reservation scope is closed"):
            cocycle.source_increment_mod(arena, 198)
    finally:
        arena.clear()


def test_join_rejects_a_foreign_reservation_scope_even_at_exact_seam() -> None:
    arena = SLPArena()
    ledger = ResourceLedger()
    try:
        with _reservation_scope(ledger, "nc19-source-word-left") as (
            _,
            left_reservation,
        ):
            first = _spatial_step(arena, arena.word(_digits(168)), left_reservation)
            with _reservation_scope(ledger, "nc19-source-word-right") as (
                _,
                right_reservation,
            ):
                second = _spatial_step(arena, first.target_root, right_reservation)
                with pytest.raises(ValueError, match="foreign reservation scope"):
                    first.then(second)
    finally:
        arena.clear()


def test_ledgered_source_arena_rejects_a_reservation_from_another_ledger() -> None:
    source_ledger = ResourceLedger()
    foreign_ledger = ResourceLedger()
    arena = LedgerSLPArena(source_ledger, "nc19-source-owner", "test")
    try:
        with _reservation_scope(foreign_ledger, "nc19-foreign-source") as (
            owner,
            reservation,
        ):
            source = arena.word(_digits(168))
            projection = fold_two_step_slp(arena, source)
            with pytest.raises(ValueError, match="another SLP ledger"):
                ExactSourceWordCocycle.from_spatial(
                    projection,
                    arena,
                    expected_source_root=source,
                    reservation=reservation,
                )
            assert foreign_ledger.account_usage(owner) == (0, 0)
    finally:
        arena.dispose()


def test_failed_leaf_publication_refunds_its_reservation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena = SLPArena()
    ledger = ResourceLedger()
    try:
        with _reservation_scope(ledger, "nc19-failed-source-word") as (
            owner,
            reservation,
        ):
            source = arena.word(_digits(168))
            projection = fold_two_step_slp(arena, source)

            def fail_concat(
                _arena: SLPArena,
                _nodes: Iterable[int],
            ) -> Never:
                raise RuntimeError("simulated source-word publication failure")

            monkeypatch.setattr(SLPArena, "concat_many", fail_concat)
            with pytest.raises(RuntimeError, match="publication failure"):
                ExactSourceWordCocycle.from_spatial(
                    projection,
                    arena,
                    expected_source_root=source,
                    reservation=reservation,
                )
            assert ledger.account_usage(owner) == (0, 0)
    finally:
        arena.clear()


def test_issued_temporal_unit_step_reuses_action_without_repowering(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with DoubleReverseTerm(173488, 0, max_steps=4) as term:
        engine = term.temporal_engine
        source = term.source_root
        phase = engine.certify(source)
        assert phase is not None
        action = engine.advance_action(source, 1, phase)
        powered_action = engine.advance_action(source, 2, phase)
        ledger = term.resource_ledger
        with _reservation_scope(ledger, "nc19-temporal-source-word") as (
            owner,
            reservation,
        ):
            with pytest.raises(ValueError, match="one issued F step"):
                ExactSourceWordCocycle.from_issued_temporal_action(
                    engine, powered_action, reservation=reservation
                )

            def forbidden_repower(
                _engine: DoubleReverseTemporalHashlife,
                _root: int,
                _steps: int,
                _phase: int,
            ) -> Never:
                raise AssertionError("issued temporal action was powered again")

            monkeypatch.setattr(
                DoubleReverseTemporalHashlife,
                "advance_action",
                forbidden_repower,
            )
            cocycle = ExactSourceWordCocycle.from_issued_temporal_action(
                engine, action, reservation=reservation
            )
            assert cocycle.source_root == source
            assert cocycle.target_root == engine.root_of(action.target)
            assert (
                cocycle.source_increment_mod(term.source_arena, 198) == term.seed % 198
            )
            assert ledger.account_usage(owner) == (6, 6)
            for counter in (
                _double_reverse_keys.DOUBLE_REVERSE_SOURCE_WORD_FOLD_NODE_VISITS,
                _double_reverse_keys.DOUBLE_REVERSE_SOURCE_WORD_FOLD_OPERAND_BITS,
                _double_reverse_keys.DOUBLE_REVERSE_SOURCE_WORD_FOLD_OPERATIONS,
            ):
                assert ledger.counters[counter] > 0

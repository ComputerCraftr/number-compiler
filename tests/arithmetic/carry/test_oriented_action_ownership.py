"""Oriented action and mapping handles retain arena identity across eviction."""

from collections.abc import Callable
from typing import cast

import pytest

from number_compiler.arithmetic.automata.symmetry_powering import (
    ActionTransform,
    FiniteKernel,
    OrientedActionRef,
    OrientedFiniteActionArena,
)
from number_compiler.arithmetic.carry.carry_symmetry import (
    collatz_mul3_carry_action_arena,
    reverse_add_carry_action_arena,
    reverse_add_carry_word_action,
)
from number_compiler.arithmetic.contracts.scoped_handles import TransferSummaryID


@pytest.mark.parametrize("warm", (False, True))
def test_oriented_actions_reject_foreign_handles_before_every_shortcut(
    warm: bool,
) -> None:
    arena = reverse_add_carry_action_arena(10)
    other = reverse_add_carry_action_arena(10)
    local, foreign = arena.leaf(9), other.leaf(9)
    assert local.action_id == foreign.action_id
    if warm:
        arena.compose(local, local)
        arena.transformed(local, ActionTransform.IDENTITY)
    before = arena.metrics(), arena.retained_entries
    invalid = OrientedActionRef(local.owner, local.kind, arena.metrics().action_count)
    wrong_kind = OrientedActionRef(local.owner, "wrong-kind", local.local_id)
    for bad in (foreign, invalid, wrong_kind):
        for operation in (
            lambda: arena.compose(local, bad),
            lambda: arena.compose(bad, local),
            lambda: arena.transformed(bad, ActionTransform.IDENTITY),
            lambda: arena.apply(bad, 0),
            lambda: arena.raw_action(bad),
            lambda: arena.oriented_pair(bad),
        ):
            with pytest.raises(ValueError):
                operation()
            assert (arena.metrics(), arena.retained_entries) == before


def test_finite_mapping_boundaries_are_scoped_and_reject_negative_state() -> None:
    arena, other = reverse_add_carry_action_arena(), reverse_add_carry_action_arena()
    action, other_action = arena.leaf(9), other.leaf(9)
    local, _ = arena.oriented_pair(action)
    foreign, _ = other.oriented_pair(other_action)
    invalid = TransferSummaryID(local.owner, local.kind, arena.metrics().mapping_count)
    before = arena.metrics(), arena.retained_entries
    for bad in (
        foreign,
        invalid,
        TransferSummaryID(local.owner, "wrong-kind", local.local_id),
    ):
        for operation in (
            lambda: arena.mapping(bad),
            lambda: arena.compose_mapping(local, bad),
            lambda: arena.conjugate_mapping(bad),
            lambda: arena.intern_oriented(local, bad),
        ):
            with pytest.raises(ValueError):
                operation()
            assert (arena.metrics(), arena.retained_entries) == before
    with pytest.raises(TypeError):
        arena.mapping(cast("TransferSummaryID", local.local_id))
    with pytest.raises(ValueError):
        arena.apply(action, -1)


def test_oriented_canonical_ids_survive_memo_eviction_and_kernel_is_fixed() -> None:
    arena = OrientedFiniteActionArena(
        FiniteKernel(2, 2, lambda q, a: q ^ a), compose_cache_limit=1
    )
    first = arena.leaf(0)
    old_mapping = arena.oriented_pair(first)[0]
    other = arena.leaf(1)
    assert other.local_id > first.local_id
    for a, b in ((first, first), (first, other), (other, first), (other, other)):
        arena.compose(a, b)
    assert tuple(arena.apply(first, state) for state in range(2)) == (0, 1)
    assert arena.mapping(old_mapping) == (0, 1)
    assert arena.leaf(0) == first
    with pytest.raises(AttributeError):
        setattr(arena, "kernel", FiniteKernel(2, 2, lambda q, a: 1 - (q ^ a)))


def test_carry_helpers_share_only_immutable_kernels_and_require_explicit_owner() -> (
    None
):
    first, second = reverse_add_carry_action_arena(), reverse_add_carry_action_arena()
    assert first is not second
    assert first.kernel is second.kernel
    first.leaf(0)
    assert second.metrics().action_count == 0
    with pytest.raises(TypeError):
        cast("Callable[[tuple[int, ...]], object]", reverse_add_carry_word_action)(
            (1, 2, 3)
        )
    with pytest.raises(ValueError, match="different finite kernel"):
        reverse_add_carry_word_action(
            (1, 2, 3), arena=collatz_mul3_carry_action_arena()
        )

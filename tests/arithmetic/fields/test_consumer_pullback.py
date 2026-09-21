from __future__ import annotations

import pytest

from number_compiler.arithmetic.fields.consumer_pullback import (
    AssociatedActionArena,
    ExactRational,
    MonotoneSurvivalClock,
    SaturatingAffineAction,
    SurvivalAggregation,
    ThresholdDemand,
    power_action,
)
from number_compiler.resources.ledger import ResourceLedger


def test_rationals_normalize_and_reject_inexact_packets() -> None:
    assert ExactRational(6, -8) == ExactRational(-3, 4)
    assert ExactRational(1, 3) + ExactRational(1, 6) == ExactRational(1, 2)
    assert ExactRational(2, 3) / ExactRational(4, 5) == ExactRational(5, 6)
    with pytest.raises(ValueError, match="denominator"):
        ExactRational(1, 0)
    with pytest.raises(TypeError, match="integers"):
        ExactRational(True)


def test_affine_composition_pullback_and_power_are_exact() -> None:
    first = SaturatingAffineAction(ExactRational(2), ExactRational(1), ExactRational(9))
    second = SaturatingAffineAction(
        ExactRational(3), ExactRational(-4), ExactRational(20)
    )
    composed = first.then(second)
    value = ExactRational(7, 5)
    assert composed.apply(value) == second.apply(first.apply(value))
    assert composed == SaturatingAffineAction(
        ExactRational(6), ExactRational(-1), ExactRational(20)
    )
    assert first.pullback(ThresholdDemand(True, ExactRational(5), True)) == (
        ThresholdDemand(True, ExactRational(2), True)
    )
    assert first.pullback(ThresholdDemand(True, ExactRational(9), True)) == (
        ThresholdDemand(False, ExactRational(0), True)
    )
    shift = SaturatingAffineAction(offset=ExactRational(1))
    assert power_action(shift, 0) == SaturatingAffineAction.identity()
    assert power_action(shift, 13).apply(ExactRational(2)) == ExactRational(15)


def test_infinity_stays_distinct_until_a_finite_cap() -> None:
    assert SaturatingAffineAction.identity().apply(None) is None
    capped = SaturatingAffineAction(cap=ExactRational(-2))
    assert capped.apply(None) == ExactRational(-2)
    assert ThresholdDemand().evaluate(None)


def test_survival_clocks_use_nonempty_min_max_and_exact_boundaries() -> None:
    all_clock = MonotoneSurvivalClock.from_depths((9, 3, 7), SurvivalAggregation.ALL)
    any_clock = MonotoneSurvivalClock.from_depths((9, 3, 7), SurvivalAggregation.ANY)
    assert all_clock.output(3) and not all_clock.output(4)
    assert all_clock.first_failure_level() == 4
    assert any_clock.output(9) and not any_clock.output(10)
    empty = MonotoneSurvivalClock.from_depths((), SurvivalAggregation.ANY)
    assert not empty.output(0) and empty.first_failure_level() == 0
    huge = MonotoneSurvivalClock(SurvivalAggregation.ALL, 2**200)
    assert huge.first_failure_level() == 2**200 + 1


def test_arena_preserves_distinct_histories_with_one_shared_semantic() -> None:
    arena = AssociatedActionArena(ResourceLedger())
    decrement = arena.admit(
        SaturatingAffineAction(offset=ExactRational(-1)), logical_extent=1
    )
    wait = arena.admit(SaturatingAffineAction.identity(), logical_extent=1)
    early = arena.compose(decrement, wait)
    late = arena.compose(wait, decrement)
    assert early != late
    assert arena.semantic(early) == arena.semantic(late)
    assert arena.action_children(early) == (decrement, wait)
    assert arena.action_children(late) == (wait, decrement)
    assert arena.record(early).logical_extent == 2


def test_arena_close_releases_resources_and_invalidates_ids() -> None:
    ledger = ResourceLedger()
    arena = AssociatedActionArena(ledger)
    identity = arena.identity
    assert ledger.entries > 0 and ledger.nodes > 0
    arena.close()
    assert ledger.entries == ledger.nodes == 0
    with pytest.raises(ValueError, match="disposed"):
        arena.record(identity)

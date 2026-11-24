"""Finite Mahler guard projection remains tied to its issued source."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.fields.consumer_pullback import (
    ExactRational,
    HalfOpenInterval,
)
from number_compiler.sequences.antihydra.mahler_joint_future import (
    MahlerJointFutureAction,
)
from number_compiler.sequences.antihydra.mahler_source_actions import (
    MahlerSourceBoundSafetyAction,
)
from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm


@pytest.mark.parametrize("steps", (0, 1, 2, 8, 24, 65, 128))
def test_issued_finite_safety_guard_preserves_source_and_completeness(
    steps: int,
) -> None:
    term = AntihydraArithmeticTerm(steps, shared_cache=False)
    result = term.result()
    guard = result.finite_safety_guard()
    assert guard.steps == steps
    assert guard.gain == 3**steps
    assert guard.source_modulus == 1 << steps
    assert guard.source_residue == 7 % guard.source_modulus
    assert (
        guard.gain * 7 + guard.weighted_innovation
        == (result.h - 1) * guard.source_modulus
    )
    assert guard.complete
    assert guard.admitted_interval is not None
    reference = MahlerJointFutureAction.from_source_prefix(7, steps, max_steps=128)
    assert guard.admitted_interval == reference.guard
    assert guard.admitted_interval.empty is (steps >= 2)


def test_empty_guard_uses_published_root_without_replaying_future(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = AntihydraArithmeticTerm(128, shared_cache=False)
    result = term.result()

    def reject_replay(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("fractional guard replayed source occurrences")

    monkeypatch.setattr(MahlerJointFutureAction, "from_source_prefix", reject_replay)
    monkeypatch.setattr(MahlerJointFutureAction, "bit", reject_replay)
    guard = result.finite_safety_guard()
    assert guard.complete
    assert guard.admitted_interval is not None and guard.admitted_interval.empty
    assert (guard.gain * 7 + guard.weighted_innovation) == (result.h - 1) * (
        1 << guard.steps
    )


def test_empty_guard_composition_does_not_rebuild_fractional_pullbacks(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    action = MahlerJointFutureAction.bit(1).then(MahlerJointFutureAction.bit(1))
    tail = MahlerJointFutureAction.bit(0)

    def forbidden(*_args: object, **_kwargs: object) -> HalfOpenInterval:
        raise AssertionError("empty guard recomputed an interval intersection")

    monkeypatch.setattr(HalfOpenInterval, "intersect", forbidden)
    combined = action.then(tail)
    assert combined.guard.empty
    assert combined.innovation == (
        tail.gain * action.innovation + action.source_modulus * tail.innovation
    )
    assert combined.gain == action.gain * tail.gain


def test_guard_projection_rejects_a_nonphysical_gain() -> None:
    action = MahlerJointFutureAction.with_gain(
        1,
        1,
        1,
        HalfOpenInterval(ExactRational(1, 3), ExactRational(1, 2)),
        MahlerSourceBoundSafetyAction.one_bit(1),
        5,
    )
    with pytest.raises(ValueError, match="physical gain"):
        action.finite_safety_projection(interval_complete=True)


def test_exact_empty_interval_and_unavailable_interval_are_distinct() -> None:
    action = MahlerJointFutureAction.bit(1).then(MahlerJointFutureAction.bit(1))
    exact = action.finite_safety_projection(interval_complete=True)
    unavailable = action.finite_safety_projection(interval_complete=False)
    assert exact.admitted_interval is not None and exact.admitted_interval.empty
    assert exact.complete
    assert unavailable.admitted_interval is None and not unavailable.complete


def test_guard_rejects_a_mutated_published_source() -> None:
    term = AntihydraArithmeticTerm(8, shared_cache=False)
    result = term.result()
    original = result.h
    try:
        object.__setattr__(result, "h", original + 1)
        with pytest.raises(ValueError, match="changed"):
            result.finite_safety_guard()
    finally:
        object.__setattr__(result, "h", original)

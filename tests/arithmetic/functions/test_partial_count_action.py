"""Conditional action algebra does not confer physical source authority."""

from dataclasses import replace

import pytest

from number_compiler.arithmetic.functions.partial_count_action import (
    ActionUniverse,
    PartialCountAction,
)


def test_chronological_counts_refusal_and_power() -> None:
    owner = ActionUniverse(3, 2)
    first = PartialCountAction(1, (1, 2, None), ((1, 0), (0, 1), None), owner)
    after = PartialCountAction(2, (2, 0, 1), ((2, 3), (5, 7), (11, 13)), owner)
    joined = first.then(after)
    assert joined.targets == (0, 1, None)
    assert joined.counts == ((6, 7), (11, 14), None)
    assert joined.steps == 3
    assert first.power(3).targets == (None, None, None)
    assert first.power(0) == PartialCountAction.identity(owner)
    accumulated = PartialCountAction.identity(owner)
    for exponent in range(19):
        assert after.power(exponent) == accumulated
        assert first.then(after).then(accumulated) == first.then(
            after.then(accumulated)
        )
        accumulated = accumulated.then(after)


def test_universe_and_shape_authority_precedes_identity() -> None:
    owner = ActionUniverse(1, 1)
    action = PartialCountAction(1, (0,), ((1,),), owner)
    foreign = PartialCountAction.identity(ActionUniverse(1, 1))
    with pytest.raises(ValueError, match="universes"):
        action.then(foreign)
    with pytest.raises(ValueError, match="target"):
        replace(action, targets=(True,))
    with pytest.raises(ValueError, match="emission"):
        replace(action, targets=(None,))
    object.__setattr__(action, "counts", ((-1,),))
    with pytest.raises(ValueError, match="observation"):
        action.power(0)


def test_large_declared_power_uses_binary_composition() -> None:
    owner = ActionUniverse(1, 1)
    action = PartialCountAction(7, (0,), ((3,),), owner)
    power = action.power(10**30)
    assert power.targets == (0,)
    assert power.steps == 7 * 10**30
    assert power.counts == ((3 * 10**30,),)


def test_composition_preflights_output_storage(monkeypatch: pytest.MonkeyPatch) -> None:
    import number_compiler.arithmetic.functions.partial_count_action as owner

    universe = ActionUniverse(1, 2)
    action = PartialCountAction(1, (0,), ((128, 128),), universe)
    monkeypatch.setattr(owner, "MAX_ACTION_PAYLOAD_BYTES", 227)
    action.validate()
    with pytest.raises(ValueError, match="composition exceeds"):
        action.then(action)


def test_duration_preflight_precedes_power_composition(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    universe = ActionUniverse(1, 1)
    action = PartialCountAction(1 << 65_535, (0,), ((0,),), universe)
    with pytest.raises(ValueError, match="duration budget"):
        action.then(action)

    def forbidden(
        self: PartialCountAction, after: PartialCountAction
    ) -> PartialCountAction:
        raise AssertionError("duration exhaustion must precede composition")

    monkeypatch.setattr(PartialCountAction, "then", forbidden)
    with pytest.raises(ValueError, match="duration budget"):
        action.power(2)

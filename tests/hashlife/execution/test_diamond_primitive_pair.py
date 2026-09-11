from dataclasses import replace
from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.hashlife.execution.diamond_primitive_pair import (
    PrimitivePairActions,
)
from tests.support.diamond_boundary import boundary


@pytest.mark.parametrize("side", [0, 1])
@pytest.mark.parametrize("symbol", [0, 9, 10, 19])
def test_primitive_pair_substitution_matches_complete_interface(
    side: int, symbol: int
) -> None:
    _, actions, _, boundaries, first, second = boundary()
    pair = actions.compose(first, second)
    a = boundaries.kernels.kernel(boundaries.kernels.intern(actions.primitive(first)))
    b = boundaries.kernels.kernel(boundaries.kernels.intern(actions.primitive(second)))
    opposite_size = len(a.domain(BoundarySide(1 - side)))
    values = [
        boundaries.literal(second, side, index % len(b.domain(BoundarySide(side))))
        for index in range(opposite_size)
    ]
    function = boundaries.finite_function(values, first, 1 - side)
    anchor_value = a.initial(BoundarySide(side))
    anchor = boundaries.literal(first, side, anchor_value)
    state = boundaries.pair(pair, side, anchor, function)
    fast = PrimitivePairActions(boundaries)
    result = boundaries.state(fast.advance(pair, state, side, symbol))
    assert result.anchor is not None and result.continuation is not None
    assert boundaries.state(result.anchor).literal == a.advance(
        BoundarySide(side), anchor_value, symbol
    )
    for argument in range(opposite_size):
        previous_argument = a.advance(BoundarySide(1 - side), argument, symbol)
        previous = boundaries.state(values[previous_argument]).literal
        left, right = (
            (anchor_value, argument) if side == 0 else (argument, anchor_value)
        )
        emitted = a.emit(left, symbol, right)
        expected = b.advance(BoundarySide(side), previous, emitted)
        selected = boundaries.select(
            result.continuation, boundaries.literal(first, 1 - side, argument)
        )
        assert selected is not None and boundaries.state(selected).literal == expected


def test_primitive_pair_cache_reuses_canonical_result_before_function_work(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.hashlife.execution.diamond_primitive_pair as module

    ledger, actions, _, boundaries, first, second = boundary()
    pair = actions.compose(first, second)
    anchor = boundaries.literal(first, 0, 0)
    function = boundaries.constant(boundaries.literal(second, 0, 0), first, 1)
    state = boundaries.pair(pair, 0, anchor, function)
    fast = PrimitivePairActions(boundaries)
    expected = fast.advance(pair, state, 0, 10)

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("warm primitive-pair transition expanded a function")

    monkeypatch.setattr(module, "to_expression", forbidden)
    assert fast.advance(pair, state, 0, 10) == expected
    before = ledger.snapshot()
    with pytest.raises(ValueError):
        fast.advance(pair, replace(state, owner=actions.token), 0, 10)
    with pytest.raises(ValueError):
        fast.advance(pair, state, 1, 10)
    assert ledger.snapshot() == before

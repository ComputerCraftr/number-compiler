from itertools import product
from typing import cast

import pytest

from number_compiler.arithmetic.carry.reverse_port_functions import (
    ReverseLeftTransfer,
    ReversePortCodec,
    ReverseRightTransfer,
)
from number_compiler.arithmetic.contracts.block_effect import (
    BoundarySide,
    BoundaryState,
)
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger


@pytest.mark.parametrize("symbols", [(0, 9, 18), (9, 9, 0), (18, 0, 9)])
def test_bound_reverse_output_matches_sequential_carry_domains(
    symbols: tuple[int, ...],
) -> None:
    ledger = ResourceLedger()
    pieces = tuple(ReverseBoundOutput.leaf(10, symbol) for symbol in symbols)
    summary = pieces[0]
    for piece in pieces[1:]:
        summary = summary.then(piece, ledger)
    codec = ReversePortCodec(10)
    for state in range(codec.left_count):
        expected = state
        for piece in pieces:
            expected = piece.apply(0, expected)
        assert summary.apply(0, state) == expected
    for state in range(codec.right_count):
        expected = state
        for piece in reversed(pieces):
            expected = piece.apply(1, expected)
        assert summary.apply(1, state) == expected


def test_bound_reverse_output_is_spatially_associative() -> None:
    ledger = ResourceLedger()
    first, second, third = (
        ReverseBoundOutput.leaf(10, symbol) for symbol in (8, 9, 10)
    )
    assert first.then(second, ledger).then(third, ledger) == first.then(
        second.then(third, ledger), ledger
    )


def test_distinct_interiors_share_complete_bound_consumer_behavior() -> None:
    ledger = ResourceLedger()
    first = ReverseBoundOutput.leaf(10, 0).then(ReverseBoundOutput.leaf(10, 0), ledger)
    second = ReverseBoundOutput.leaf(10, 1).then(ReverseBoundOutput.leaf(10, 0), ledger)
    assert first == second


def test_bound_reverse_output_is_not_a_successor_identity() -> None:
    """A carry summary alone cannot authorize another output-producing step."""
    ledger = ResourceLedger()
    first_word = (0, 1)
    second_word = (1, 1)

    def summarize(symbols: tuple[int, ...]) -> ReverseBoundOutput:
        summary = ReverseBoundOutput.leaf(3, symbols[0])
        for symbol in symbols[1:]:
            summary = summary.then(ReverseBoundOutput.leaf(3, symbol), ledger)
        return summary

    effect = BaseBlockEffect(3)

    def literal_step(symbols: tuple[int, ...]) -> tuple[int, ...]:
        left = effect.initial(BoundarySide.LEFT)
        right = effect.initial(BoundarySide.RIGHT)
        left_states: list[BoundaryState] = []
        right_states: list[BoundaryState] = []
        for symbol in symbols:
            left_states.append(left)
            left = effect.advance(BoundarySide.LEFT, left, symbol)
        for symbol in reversed(symbols):
            right_states.append(right)
            right = effect.advance(BoundarySide.RIGHT, right, symbol)
        return tuple(
            effect.emit(left_state, symbol, right_state)
            for left_state, symbol, right_state in zip(
                left_states,
                symbols,
                reversed(right_states),
                strict=True,
            )
        )

    assert summarize(first_word) == summarize(second_word)
    first_successor = literal_step(first_word)
    second_successor = literal_step(second_word)
    assert first_successor == (0, 2)
    assert second_successor == (2, 2)
    assert summarize(first_successor) != summarize(second_successor)


def test_bound_reverse_output_rejects_numeric_aliases() -> None:
    summary = ReverseBoundOutput.leaf(10, 9)
    with pytest.raises((TypeError, ValueError)):
        summary.apply(False, 0)
    with pytest.raises((TypeError, ValueError)):
        summary.apply(0, cast(int, 0.0))


def test_bound_reverse_output_rejects_unissued_payload() -> None:
    with pytest.raises(ValueError, match="not issued"):
        ReverseBoundOutput(
            ReverseLeftTransfer.leaf(10, 9),
            ReverseRightTransfer.leaf(10, 9),
        )


@pytest.mark.parametrize("symbols", tuple(product((0, 9, 18, 19), repeat=2)))
@pytest.mark.parametrize("side", (0, 1))
def test_bound_reverse_output_matches_digit_terminal(
    symbols: tuple[int, int], side: int
) -> None:
    ledger = ResourceLedger()
    summary = ReverseBoundOutput.leaf(10, symbols[0]).then(
        ReverseBoundOutput.leaf(10, symbols[1]), ledger
    )
    terminal = DigitNormalizeBlockEffect(10)
    boundary_side = BoundarySide(side)
    universe = terminal.boundary_universe(boundary_side)
    for ordinal, initial in enumerate(universe):
        state = initial
        scan = reversed(symbols) if side else symbols
        for symbol in scan:
            state = terminal.advance(boundary_side, state, symbol)
        assert summary.apply_digit_normalize(side, ordinal) == universe.index(state)

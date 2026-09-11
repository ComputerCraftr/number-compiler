from itertools import product

import pytest

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.carry.reverse_port_functions import (
    ReverseLeftTransfer,
    ReversePortCodec,
    ReverseRightTransfer,
)
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


def test_bound_reverse_output_rejects_numeric_aliases() -> None:
    summary = ReverseBoundOutput.leaf(10, 9)
    with pytest.raises((TypeError, ValueError)):
        summary.apply(False, 0)
    with pytest.raises((TypeError, ValueError)):
        summary.apply(0, 0.0)  # type: ignore[arg-type]


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

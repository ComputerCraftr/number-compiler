"""Complete boundary-state synchronization, including nonconstant functions."""

from itertools import product

import pytest

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.hashlife.execution.continuations.diamond_tasks import (
    Initial,
    Transfer,
)
from number_compiler.hashlife.interfaces.diamond_boundary import ImageBinding
from number_compiler.hashlife.interfaces.diamond_resets import RightResetCertificates
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from number_compiler.sequences.collatz.physical_kernel import (
    PhysicalCollatzFourBlockEffect,
)
from tests.support.collatz_diamond_fixtures import build_collatz_diamond_runtime
from tests.support.diamond_halos import suffix_parity
from tests.support.diamond_runtime import build


def test_verified_four_step_reset_covers_every_original_state_and_every_word() -> None:
    kernel = PhysicalCollatzFourBlockEffect()
    for word in product(range(3), repeat=4):
        targets: set[object] = set()
        for initial in range(90):
            state = initial
            for symbol in word:
                state = kernel.advance(BoundarySide.RIGHT, state, symbol)
            targets.add(state)
        assert len(targets) == 1
    # The certificate cannot be tightened merely because some words reset early.
    states: set[int] = set()
    for initial in range(90):
        state = initial
        for symbol in (0, 0, 0):
            state = kernel.advance(BoundarySide.RIGHT, state, symbol)
        states.add(state)
    assert len(states) > 1


def test_composed_reset_erases_every_reachable_and_an_arbitrary_nonconstant_state() -> (
    None
):
    runtime, action = build_collatz_diamond_runtime(
        CollatzPhysicalBlockEffect(), (0, 1), 8, 2
    )
    arena = RightResetCertificates(runtime)
    assert arena.radius(action) == 2
    first = runtime.actions.reference(runtime.actions.node(action).first)
    second = runtime.actions.reference(runtime.actions.node(action).second)
    left = runtime.execute(Initial(runtime.actions.identity, 0))
    right = runtime.execute(Initial(runtime.actions.identity, 1))
    initial = runtime.execute(Initial(action, 1))
    states = [initial]
    seen = {initial}
    for state in states:
        for symbol in range(3):
            provider = ImageBinding(
                runtime.actions.identity,
                runtime.cells.formal_symbol(symbol),
                left,
                right,
            )
            following = runtime.execute(Transfer(provider, action, state, 1))
            if following not in seen:
                seen.add(following)
                states.append(following)
        assert len(states) <= 10
    assert len(states) == 10
    # This valid continuation is not required to be reachable from a source.
    outputs = [runtime.boundaries.literal(second, 1, i % 3) for i in range(6)]
    function = runtime.boundaries.finite_function(outputs, first, 0)
    assert runtime.boundaries.action(function).kind == "decision"
    arbitrary = runtime.boundaries.pair(
        action, 1, runtime.boundaries.literal(first, 1, 1), function
    )
    states.append(arbitrary)
    for word in product(range(3), repeat=2):
        targets: set[object] = set()
        for state in states:
            for symbol in word:
                provider = ImageBinding(
                    runtime.actions.identity,
                    runtime.cells.formal_symbol(symbol),
                    left,
                    right,
                )
                state = runtime.execute(Transfer(provider, action, state, 1))
            targets.add(state)
        assert len(targets) == 1


def test_unknown_kernel_and_short_or_left_scans_cannot_reset() -> None:
    runtime, action = build_collatz_diamond_runtime(
        CollatzPhysicalBlockEffect(), (1,), 8, 4
    )
    arena = RightResetCertificates(runtime)
    left = runtime.execute(Initial(runtime.actions.identity, 0))
    right = runtime.execute(Initial(runtime.actions.identity, 1))
    short = ImageBinding(
        runtime.actions.identity, runtime.cells.source_span(0, 2)[0][1], left, right
    )
    enough = ImageBinding(
        runtime.actions.identity, runtime.cells.source_span(0, 4)[0][1], left, right
    )
    assert not arena.can_reset(short, action, 1)
    assert arena.can_reset(enough, action, 1)
    assert not arena.can_reset(enough, action, 0)
    other, unknown = build(suffix_parity(), (1,), 8, 2)
    assert RightResetCertificates(other).radius(unknown) is None
    before = runtime.ledger.snapshot()
    with pytest.raises(ValueError):
        arena.can_reset(enough, unknown, 1)
    with pytest.raises(ValueError):
        arena.can_reset(enough, action, True)
    assert runtime.ledger.snapshot() == before


def test_two_step_reset_on_every_admissible_composite_right_state_without_runtime() -> (
    None
):
    # This quantifies the whole C² port: 3 anchors times all 3**6 functions.
    # It uses primitive bimachine equations, independently of reset scheduling.
    kernel = CollatzPhysicalBlockEffect()
    for anchor, continuation, word in product(
        range(3), product(range(3), repeat=6), product(range(3), repeat=2)
    ):
        current, function = anchor, continuation
        for symbol in word:
            following = tuple(
                kernel.advance(
                    BoundarySide.RIGHT,
                    function[kernel.advance(BoundarySide.LEFT, left, symbol)],
                    kernel.emit(left, symbol, current),
                )
                for left in range(6)
            )
            current = kernel.advance(BoundarySide.RIGHT, current, symbol)
            function = following
        expected = tuple(kernel.emit(left, word[1], word[0]) for left in range(6))
        assert (current, function) == (word[1], expected)

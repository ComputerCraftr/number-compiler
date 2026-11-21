"""Periodic source words stay ordered and compact in the shared SLP."""

import pytest

from number_compiler.arithmetic.automata.periodic_slp import periodic_word
from number_compiler.arithmetic.automata.slp import SLPArena
from number_compiler.arithmetic.automata.slp_walks import symbol_at


@pytest.mark.parametrize("period", ((1,), (1, 2, 3), (1, 2, 1, 2)))
def test_periodic_word_matches_literal_phase_and_tail(period: tuple[int, ...]) -> None:
    arena = SLPArena()
    for phase in range(-2, len(period) + 2):
        for length in range(15):
            root = periodic_word(arena, period, length, phase=phase)
            assert arena.materialize(root) == tuple(
                period[(phase + index) % len(period)] for index in range(length)
            )


def test_periodic_word_remains_compact_at_large_length() -> None:
    arena = SLPArena()
    count = 10**18 + 2
    root = periodic_word(arena, (2, 4, 6), count, phase=1)
    assert arena.nodes[root].length == count
    assert symbol_at(arena, root, count - 1) == (2, 4, 6)[count % 3]
    assert len(arena.nodes) < 20

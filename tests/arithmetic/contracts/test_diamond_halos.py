"""Right-context clipping is a certified dependency bound, not a width guess."""

from itertools import product
from random import Random

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockEffect
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from tests.support.diamond_halos import suffix_parity
from tests.support.diamond_runtime import build, oracle


@pytest.mark.parametrize(
    "effect",
    [
        CollatzPhysicalBlockEffect(),
        BaseBlockEffect(2),
        DigitNormalizeBlockEffect(2),
        suffix_parity(),
    ],
)
def test_primitive_and_composed_halos_preserve_all_small_binary_inputs(
    effect: BlockEffect,
) -> None:
    for values in product((0, 1), repeat=3):
        for count in (0, 1, 2, 3):
            runtime, action = build(effect, values, 8, count)
            expected = oracle(effect, values, 8, count)
            assert [runtime.point(action, position) for position in (0, 2, 3, 7)] == [
                expected[p] for p in (0, 2, 3, 7)
            ]
            if type(effect) is CollatzPhysicalBlockEffect:
                assert runtime.halos.right(action) == count


def test_unknown_suffix_memory_keeps_the_distant_original_context() -> None:
    effect = suffix_parity()
    for final in (0, 1):
        source = (0,) * 31 + (final,)
        runtime, action = build(effect, source, 32, 1)
        assert runtime.halos.right(action) is None
        assert runtime.point(action, 0) == final
        assert runtime.point(action, 30) == final
        assert runtime.point(action, 31) == final


def test_random_distant_queries_preserve_composed_midpoint_contexts() -> None:
    random = Random(913)
    for effect in (CollatzPhysicalBlockEffect(), BaseBlockEffect(3), suffix_parity()):
        for count in (1, 2, 4):
            source = tuple(random.randrange(effect.blank) for _ in range(13))
            runtime, action = build(effect, source, 24, count)
            expected = oracle(effect, source, 24, count)
            for position in (0, 7, 12, 13, 22, 23):
                assert runtime.point(action, position) == expected[position]


def test_halo_rejects_foreign_root_before_any_observation() -> None:
    runtime, action = build(CollatzPhysicalBlockEffect(), (1,), 8, 4)
    foreign, other = build(CollatzPhysicalBlockEffect(), (1,), 8, 4)
    assert runtime.halos.right(action) == 4
    before = runtime.ledger.snapshot()
    with pytest.raises(ValueError):
        runtime.halos.right(other)
    assert runtime.ledger.snapshot() == before
    assert foreign.halos.right(other) == 4

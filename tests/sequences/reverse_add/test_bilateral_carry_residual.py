"""Exact boundaries for a pulled carry fold; no temporal closure is assumed.

The independent integer oracle and expanded words here are bounded references,
never a production constructor. Both opposite contexts are needed at a join.
There is one physical carry direction, LSD to MSD. The right context summarizes
the same carry-domain law under reflected coordinates; it is not a second carry.
"""

from itertools import product

import pytest

from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    apply_carry_fn,
    compose_carry_fn,
    value_carry_fn,
)
from number_compiler.arithmetic.carry.reverse_port_functions import (
    ReversePortCodec,
    ReversePortFunction,
)
from number_compiler.arithmetic.contracts.block_effect import (
    BoundarySide,
    BoundaryState,
)
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.interfaces.tile_reverse_functions import (
    reverse_leaf_components,
    reverse_parent_components,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.primitive_output_morphism import PORTS
from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts
from tests.sequences.reverse_add.test_source_ports import _source


def _pairs(value: int) -> tuple[int, ...]:
    digits = tuple(int(d) for d in reversed(str(value)))
    return tuple(a + b for a, b in zip(digits, reversed(digits), strict=True))


def _advance(
    kernel: BaseBlockEffect,
    side: BoundarySide,
    port: BoundaryState,
    word: tuple[int, ...],
) -> BoundaryState:
    for symbol in word if side is BoundarySide.LEFT else reversed(word):
        port = kernel.advance(side, port, symbol)
    return port


def _emit_between(
    kernel: BaseBlockEffect,
    word: tuple[int, ...],
    left: BoundaryState,
    right: BoundaryState,
) -> tuple[int, ...]:
    suffixes = [right]
    for symbol in reversed(word):
        suffixes.append(kernel.advance(BoundarySide.RIGHT, suffixes[-1], symbol))
    suffixes.reverse()
    output = []
    for index, symbol in enumerate(word):
        output.append(kernel.emit(left, symbol, suffixes[index + 1]))
        left = kernel.advance(BoundarySide.LEFT, left, symbol)
    return tuple(output)


def _fold(word: tuple[int, ...]) -> CarryFn:
    result = CarryFn.ID
    for symbol in word:
        if symbol != 19:
            result = compose_carry_fn(value_carry_fn(symbol, 10), result)
    return result


@pytest.mark.parametrize("seed", (1, 196, 909, 1593, 12003))
def test_residual_join_cross_feeds_both_full_primitive_ports(seed: int) -> None:
    kernel, codec = BaseBlockEffect(10), ReversePortCodec(10)
    word = (*_pairs(seed), 19)
    # All admitted primitive port states, including sink and publication blank.
    for left_id, right_id in product(range(codec.left_count), range(codec.right_count)):
        left, right = codec.decode_left(left_id), codec.decode_right(right_id)
        expected = _emit_between(kernel, word, left, right)
        for cut in range(len(word) + 1):
            a, b = word[:cut], word[cut:]
            middle_left = _advance(kernel, BoundarySide.LEFT, left, a)
            middle_right = _advance(kernel, BoundarySide.RIGHT, right, b)
            left_output = _emit_between(kernel, a, left, middle_right)
            right_output = _emit_between(kernel, b, middle_left, right)
            assert left_output + right_output == expected
            assert compose_carry_fn(_fold(right_output), _fold(left_output)) == (
                _fold(expected)
            )


def test_1593_omitting_reflected_domain_context_changes_next_growth() -> None:
    kernel = BaseBlockEffect(10)
    word = (*_pairs(1593), 19)
    assert word == (4, 14, 14, 4, 19)
    left, right = kernel.initial(BoundarySide.LEFT), kernel.initial(BoundarySide.RIGHT)
    emitted = _emit_between(kernel, word, left, right)
    assert 1593 + 3951 == 5544
    assert emitted == (*_pairs(5544), 19) == (9, 9, 9, 9, 19)
    untransported = []
    for symbol in word:
        untransported.append(kernel.emit(left, symbol, right))
        left = kernel.advance(BoundarySide.LEFT, left, symbol)
    assert tuple(untransported) == (8, 9, 10, 9, 19)
    assert _fold(emitted) is CarryFn.ID
    assert _fold(tuple(untransported)) is CarryFn.CONST1
    assert apply_carry_fn(_fold(emitted), 0) == 0
    assert apply_carry_fn(_fold(tuple(untransported)), 0) == 1
    assert 5544 + 4455 == 9999
    # The live source-port consumer already has the correct two-step boundary.
    ports = SourceCarryPorts(_source(1593, 10), ResourceLedger())
    assert ports.second_width() == 4
    assert ports.range_transfer(2, 0, 4) is CarryFn.ID


def test_existing_closed_parent_supplies_missing_right_context() -> None:
    ledger = ResourceLedger()
    word = (*_pairs(1593), 19)
    root = reverse_leaf_components(PORTS, 10, word[0], ledger)
    original = root.functions()[2]
    for symbol in word[1:]:
        root = reverse_parent_components(
            root, reverse_leaf_components(PORTS, 10, symbol, ledger), ledger
        )
    joined = root.functions()[2]
    assert type(original) is ReversePortFunction
    assert type(joined) is ReversePortFunction
    assert original.evaluate((0, 0), ledger) == 8
    assert joined.evaluate((0, 0), ledger) == 9


def test_temporal_hiding_cannot_reuse_unchanged_primitive_port_binding() -> None:
    """A narrow collision of original ports, not a full-cylinder counterexample."""
    kernel, codec, ledger = BaseBlockEffect(10), ReversePortCodec(10), ResourceLedger()
    words = (_pairs(1041), _pairs(1051))
    assert words == ((2, 4, 4, 2), (2, 5, 5, 2))
    right_ports = tuple(
        _advance(kernel, BoundarySide.RIGHT, kernel.initial(BoundarySide.RIGHT), w[1:])
        for w in words
    )
    assert right_ports[0] == right_ports[1] == codec.decode_right(1)
    # Full original primitive port binding and all thirteen local channels agree.
    channels = reverse_leaf_components(PORTS, 10, 2, ledger).functions()
    values = []
    for right_port in right_ports:
        assert right_port == codec.decode_right(1)
        binding = (0, 1)
        row = []
        for channel in channels:
            assert type(channel) is ReversePortFunction
            row.append(channel.evaluate(binding, ledger))
        values.append(tuple(row))
    assert values[0] == values[1]
    expected_values = ((1041, 2442, 4884), (1051, 2552, 5104))
    results = []
    for word, (seed, first, second) in zip(words, expected_values, strict=True):
        assert seed + int(str(seed)[::-1]) == first
        assert first + int(str(first)[::-1]) == second
        output: tuple[int, ...] = (*word, 19, 19)
        for expected in (first, second):
            output = _emit_between(
                kernel,
                output,
                kernel.initial(BoundarySide.LEFT),
                kernel.initial(BoundarySide.RIGHT),
            )
            assert tuple(x for x in output if x != 19) == _pairs(expected)
            assert len(str(expected)) == 4  # No growth or chart difference.
        results.append(value_carry_fn(output[0], 10))
    assert results == [CarryFn.CONST0, CarryFn.ID]

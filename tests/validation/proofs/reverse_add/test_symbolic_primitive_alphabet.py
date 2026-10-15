"""Symbolic cell pullback is local closure, not a temporal powering claim."""

from itertools import product
from typing import Never

import pytest

from number_compiler.arithmetic.carry.reverse_port_functions import ReversePortFunction
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
)
from number_compiler.hashlife.interfaces.tile_reverse_functions import (
    reverse_leaf_components,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.primitive_output_morphism import (
    CHANNEL_SYMBOL,
    LEFT,
    LEFT_STATE,
    PORTS,
    RIGHT,
    RIGHT_STATE,
    SYMBOL,
    ReversePrimitiveOutputMorphism,
)


def _forbidden(*_args: object, **_kwargs: object) -> Never:
    raise AssertionError("symbolic construction evaluated a source assignment")


def test_all_symbolic_channels_match_closed_primitive_including_blank(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    bits = BitFunctionArena(ledger)
    arena = ReversePrimitiveOutputMorphism(bits)
    inputs = tuple(sorted((*PORTS, SYMBOL), key=lambda p: p.variable))
    symbol = bits.variable(inputs, SYMBOL, CHANNEL_SYMBOL)
    left = bits.variable(inputs, LEFT, LEFT_STATE)
    right = bits.variable(inputs, RIGHT, RIGHT_STATE)
    with monkeypatch.context() as poison:
        poison.setattr(bits, "evaluate", _forbidden)
        poison.setattr(ReversePortFunction, "evaluate", _forbidden)
        result = arena.pullback_channels(symbol, left, right)
    assert len(result) == 13
    for value in range(20):
        raw = reverse_leaf_components(PORTS, 10, value, ledger).functions()
        expected = tuple(f for f in raw if type(f) is ReversePortFunction)
        assert len(expected) == 13
        assert tuple(bits.resolve(f).signature.output for f in result) == tuple(
            f.signature.output for f in expected
        )
        for left_value, right_value in product(range(43), range(5)):
            binding = {
                SYMBOL.variable: value,
                LEFT.variable: left_value,
                RIGHT.variable: right_value,
            }
            # Repeated roles share IDs; evaluate each demanded function once.
            actual = {f: bits.evaluate(f, binding) for f in set(result)}
            assert tuple(actual[f] for f in result) == tuple(
                f.evaluate((left_value, right_value), ledger) for f in expected
            )

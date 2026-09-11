"""Independent finite oracles for bounded algebraic division interfaces."""

from __future__ import annotations

from itertools import product

import pytest

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.functions.finite_function_types import FinitePort
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.radix_division import SymbolicBinaryDivisionEffect
from number_compiler.arithmetic.radix_port_functions import (
    DivisionCarry,
    RadixPortFunction,
)
from number_compiler.hashlife.interfaces.tile_radix_functions import (
    division_leaf_components,
    division_parent_components,
)
from number_compiler.resources.ledger import ResourceLedger


@pytest.mark.parametrize("radix", (2, 3, 5, 12))
def test_carry_composition_matches_every_small_word_and_incoming_state(
    radix: int,
) -> None:
    ledger = ResourceLedger()
    law = SymbolicBinaryDivisionEffect(radix)
    for word in product((0, 1, 2), repeat=4):
        scan = DivisionCarry.identity(radix)
        for symbol in reversed(word):
            scan = scan.then(DivisionCarry.leaf(radix, symbol), ledger)
        for incoming in range(2 * radix):
            state = incoming
            for symbol in reversed(word):
                state = law.advance(BoundarySide.RIGHT, state, symbol)
            assert scan.apply(incoming, ledger) == state


@pytest.mark.parametrize("radix", (3, 6, 257, (1 << 63) - 25))
def test_all_interval_channels_match_independent_division(radix: int) -> None:
    ledger = ResourceLedger()
    ports = (
        FinitePort(PortVariable(0, 0, "tile-left", 0), 1),
        FinitePort(PortVariable(0, 1, "tile-right", 0), 2 * radix),
    )
    law = SymbolicBinaryDivisionEffect(radix)
    for word in ((0, 1, 1, 0), (1, 0, 2, 2), (2, 0, 1, 2), (2, 2, 2, 2)):
        leaves = [division_leaf_components(ports, radix, symbol) for symbol in word]
        left = division_parent_components(leaves[0], leaves[1], ledger)
        right = division_parent_components(leaves[2], leaves[3], ledger)
        parent = division_parent_components(left, right, ledger)
        for incoming in (0, 1, 2, radix, 2 * radix - 2, 2 * radix - 1):
            state = incoming
            emitted = []
            for symbol in reversed(word):
                emitted.append(law.emit(0, symbol, state))
                state = law.advance(BoundarySide.RIGHT, state, symbol)
            emitted.reverse()
            active = int(any(symbol != 2 for symbol in emitted))
            expected = (
                0,
                state,
                emitted[0],
                active,
                int(any(symbol != 2 for symbol in emitted[:2])),
                int(any(symbol != 2 for symbol in emitted[2:])),
                active,
                emitted[0],
                emitted[-1],
                active,
                1 - active,
                0,
                0,
            )
            functions = parent.functions()
            assert all(type(function) is RadixPortFunction for function in functions)
            observed = tuple(
                function.evaluate((0, incoming), ledger)
                for function in functions
                if type(function) is RadixPortFunction
            )
            assert observed == expected
    assert ledger.counters.get("semantic_function_staged_nodes", 0) == 0
    assert ledger.counters.get("tile_radix_affine_compositions", 0) > 0
    assert 0 < ledger.counters.get("maximum_arithmetic_bits", 0) <= 64


def test_carry_composition_order_and_associativity() -> None:
    ledger = ResourceLedger()
    zero, one = DivisionCarry.leaf(7, 0), DivisionCarry.leaf(7, 1)
    assert zero.then(one, ledger) != one.then(zero, ledger)
    assert zero.then(one, ledger).then(one, ledger) == zero.then(
        one.then(one, ledger), ledger
    )


def test_activation_functions_forget_unobserved_remainder_coefficients() -> None:
    radix = 258
    ports = (
        FinitePort(PortVariable(0, 0, "tile-left", 0), 1),
        FinitePort(PortVariable(0, 1, "tile-right", 0), 2 * radix),
    )
    zero, one = (division_leaf_components(ports, radix, symbol) for symbol in (0, 1))
    assert zero.activity == one.activity
    assert zero.termination == one.termination
    assert zero.boundary_right != one.boundary_right
    assert zero.output != one.output

"""Factored products/functions preserve wide ports and lexical scope."""

from __future__ import annotations

from itertools import product
from typing import TYPE_CHECKING, Literal

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.semantic_bits import BitFunctionArena
from number_compiler.hashlife.interfaces.semantic_structures import (
    StructureArena,
    StructureID,
)
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.semantic_bits import (
        FactoredFunctionID,
    )


def setup(
    width: int = 3,
) -> tuple[
    BitFunctionArena,
    StructureArena,
    FinitePort,
    FinitePort,
    AtomSort,
    FactoredFunctionID,
    FactoredFunctionID,
    StructureID,
]:
    bits = BitFunctionArena(ResourceLedger(max_cache_entries=180_000))
    structures = StructureArena(bits)
    x = FinitePort(PortVariable(0, 0, "x", 0), 1 << width)
    y = FinitePort(PortVariable(0, 0, "y", 0), 2)
    word = AtomSort("word", 1 << width)
    vx = bits.variable((x, y), x, word)
    vy = bits.variable((x, y), y, BOOL)
    summed = bits.add(vx, vy, word)
    body = structures.atom(summed)
    return bits, structures, x, y, word, vx, vy, body


def test_curried_wide_output_remains_bit_factored_without_outer_terminal_tables() -> (
    None
):
    bits, arena, x, y, word, vx, vy, body = setup(64)
    function = arena.curry(body, (y,))
    outer = arena.atom(bits.variable((x,), x, word))
    pair = arena.product((outer, function))
    assert len(arena.nodes) < 20
    assert len(bits.nodes) < 20
    assert len(bits.functions.nodes) < 15_000
    fn = arena.component(pair, 1)
    for amount in (0, 1):
        argument = bits.constant(FunctionSignature((), BOOL), amount)
        applied = arena.apply(fn, {y.variable: argument})
        for value in (0, 1, (1 << 63), (1 << 64) - 2, (1 << 64) - 1):
            expected = value + amount
            assert arena.evaluate_atom(applied, {x.variable: value}) == (
                expected if expected < 1 << 64 else None
            )
    # Commuting equivalent finite arithmetic yields the identical lambda/pair.
    alternate = arena.atom(bits.add(vy, vx, word))
    assert arena.curry(alternate, (y,)) == function
    assert arena.product((outer, arena.curry(alternate, (y,)))) == pair


def test_nested_application_avoids_capture_by_an_inner_declared_port_name() -> None:
    bits, arena, x, y, word, _, _, body = setup()
    inner = arena.curry(body, (y,))
    outer = arena.curry(inner, (x,))
    # Free argument y has the same name as the declared inner binder y.
    argument = bits.variable((y,), y, BOOL)
    # x has cardinality8, so embed y into an x-domain atom without enumerating8.
    zero = bits.constant(FunctionSignature((y,), word), 0)
    lifted = bits.add(zero, argument, word)
    specialized = arena.apply(outer, {x.variable: lifted})
    inner_argument = bits.constant(FunctionSignature((), BOOL), 1)
    result = arena.apply(specialized, {y.variable: inner_argument})
    for value in (0, 1):
        assert arena.evaluate_atom(result, {y.variable: value}) == value + 1


def test_product_validity_masks_all_components_and_keeps_function_partiality() -> None:
    bits, arena, x, y, word, _, _, body = setup(2)
    fn = arena.curry(body, (y,))
    # Partial inner sum at x=3,y=1 does not make the function itself absent.
    assert bits.functions.evaluate(arena.resolve(fn).valid, {x.variable: 3}).value == 1
    argument = bits.constant(FunctionSignature((), BOOL), 1)
    result = arena.apply(fn, {y.variable: argument})
    first = arena.atom(bits.variable((x,), x, word))
    pair = arena.product((first, result))
    for value in range(4):
        assert arena.evaluate_atom(arena.component(pair, 0), {x.variable: value}) == (
            value if value < 3 else None
        )
        assert arena.evaluate_atom(arena.component(pair, 1), {x.variable: value}) == (
            value + 1 if value < 3 else None
        )


def test_bitwise_substitution_is_simultaneous_and_preserves_invalid_arguments() -> None:
    bits = BitFunctionArena(ResourceLedger())
    x = FinitePort(PortVariable(0, 0, "x", 0), 3)
    y = FinitePort(PortVariable(0, 0, "y", 0), 3)
    word = AtomSort("three", 3)
    vx, vy = (bits.variable((x, y), port, word) for port in (x, y))
    swapped = bits.substitute(vx, {x.variable: vy, y.variable: vx})
    for a, b in product(range(4), repeat=2):
        assert bits.evaluate(swapped, {x.variable: a, y.variable: b}) == (
            b if max(a, b) < 3 else None
        )


def test_structured_root_failure_retains_no_partial_leaf_or_boolean_publication() -> (
    None
):
    bits, arena, _, y, _, _, _, body = setup()
    before = arena.ledger.snapshot()
    arena.ledger.tighten_limits(None, before.entries)
    with pytest.raises(BlockContextBudgetExceeded):
        arena.curry(body, (y,))
    after = arena.ledger.snapshot()
    assert (
        after.entries,
        after.nodes,
        after.peak_entries,
        after.peak_nodes,
        after.inventory,
    ) == (
        before.entries,
        before.nodes,
        before.peak_entries,
        before.peak_nodes,
        before.inventory,
    )
    assert len(arena.nodes) == 1
    assert all(row.accounting_delta == 0 for row in bits.ledger.inventory())


@pytest.mark.parametrize(
    "field,value",
    [
        ("local_id", True),
        ("local_id", 0.0),
        ("local_id", -1),
        ("owner", ArenaToken()),
        ("kind", "semantic-function"),
    ],
)
def test_structured_handles_validate_before_product_or_curry(
    field: str, value: ArenaToken | Literal["semantic-function"] | bool | float
) -> None:
    _, arena, _, y, _, _, _, body = setup()
    arena.curry(body, (y,))
    forged = object.__new__(StructureID)
    for name in ("owner", "kind", "local_id"):
        object.__setattr__(
            forged, name, value if name == field else getattr(body, name)
        )
    before = arena.ledger.snapshot()
    with pytest.raises(ValueError):
        arena.product((body, forged))
    with pytest.raises(ValueError):
        arena.curry(forged, (y,))
    assert arena.ledger.snapshot() == before


def test_eta_roundtrip_and_unused_invalid_argument_preserve_partial_function_semantics() -> (
    None
):
    bits, arena, x, y, word, _, vy, body = setup()
    function = arena.curry(body, (y,))
    assert arena.curry(arena.apply(function, {y.variable: vy}), (y,)) == function
    assert arena.substitute(function, {}) == function
    # A function with a constant body still rejects a partial argument outside
    # its declared admissibility; the ignored value cannot hide undefinedness.
    constant = arena.atom(bits.constant(FunctionSignature((x, y), word), 1))
    fn = arena.curry(constant, (x,))
    z = FinitePort(PortVariable(0, 0, "z", 0), 8)
    variable = bits.variable((z,), z, word)
    plus = bits.constant(FunctionSignature((z,), word), 1)
    partial_argument = bits.add(variable, plus, word)
    result = arena.apply(fn, {x.variable: partial_argument})
    for zvalue in range(8):
        assert arena.evaluate_atom(result, {y.variable: 0, z.variable: zvalue}) == (
            1 if zvalue < 7 else None
        )

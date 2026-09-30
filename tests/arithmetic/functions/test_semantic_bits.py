"""Bounded arithmetic truth checks independent of Boolean circuit construction."""

from __future__ import annotations

from itertools import product
from typing import Literal

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.functions.finite_function_types import (
    AtomSort,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
    FactoredFunctionID,
)
from number_compiler.resources.ledger import ResourceLedger
from tests.support.assertions import assert_rejected_atomically


def ports(
    radix: int,
) -> tuple[FinitePort, FinitePort]:
    return (
        FinitePort(PortVariable(0, 0, "carry", 0), radix),
        FinitePort(PortVariable(0, 0, "symbol", 0), 2),
    )


def test_unary_atom_maps_compose_canonically_and_preserve_invalid_inputs() -> None:
    arena = BitFunctionArena(ResourceLedger())
    port = FinitePort(PortVariable(0, 0, "atom", 0), 5)
    output = AtomSort("F5", 5)
    source = arena.variable((port,), port, output)
    inverse = arena.map_atoms(source, output, (0, 4, 3, 2, 1))
    assert arena.map_atoms(inverse, output, (0, 4, 3, 2, 1)) == source
    constant = arena.map_atoms(source, output, (2,) * 5)
    for value in range(8):
        assert arena.evaluate(constant, {port.variable: value}) == (
            2 if value < 5 else None
        )
    for table in ((0,), (0, 1, 2, 3, 5), (0, 1, 2, 3, True)):
        with pytest.raises(ValueError):
            arena.map_atoms(source, output, table)
    foreign = BitFunctionArena(ResourceLedger()).constant(
        FunctionSignature((), output), 0
    )
    with pytest.raises(ValueError):
        arena.map_atoms(foreign, output, tuple(range(5)))


def test_unary_map_does_not_enumerate_wide_input_profiles() -> None:
    arena = BitFunctionArena(ResourceLedger(max_nodes=2000))
    ports = tuple(FinitePort(PortVariable(0, i, "wide", 0), 1 << 40) for i in range(2))
    output = AtomSort("small", 5)
    source = arena.constant(FunctionSignature(ports, output), 3)
    result = arena.map_atoms(source, output, (0, 4, 3, 2, 1))
    assert arena.evaluate(result, {p.variable: (1 << 40) - 1 for p in ports}) == 2
    assert arena.ledger.nodes < 100
    too_wide = arena.constant(FunctionSignature((), AtomSort("large", 65)), 0)
    with pytest.raises(ValueError, match="bounded"):
        arena.map_atoms(too_wide, output, (0,) * 65)


@pytest.mark.parametrize("radix", range(1, 18))
def test_complete_binary_division_all_small_codes(radix: int) -> None:
    arena = BitFunctionArena(ResourceLedger())
    carry, symbol = ports(radix)
    result = arena.divide_binary(radix, carry, symbol)
    for c, b in product(range(1 << carry.bits), range(2)):
        inputs = {carry.variable: c, symbol.variable: b}
        assert arena.evaluate(result.remainder, inputs) == (
            (2 * c + b) % radix if c < radix else None
        )
        assert arena.evaluate(result.quotient, inputs) == (
            (2 * c + b) // radix if c < radix else None
        )
    nodes = len(arena.functions.nodes), len(arena.nodes)
    assert arena.divide_binary(radix, carry, symbol) == result
    assert (len(arena.functions.nodes), len(arena.nodes)) == nodes


@pytest.mark.parametrize("radix", (1 << 63, (1 << 63) - 1, (1 << 62) + 19))
def test_wide_radix_uses_bit_functions_without_enumerating_atom_domain(
    radix: int,
) -> None:
    arena = BitFunctionArena(ResourceLedger(max_cache_entries=180_000))
    carry, symbol = ports(radix)
    function = arena.variable((carry, symbol), carry)
    division = arena.divide_binary(radix, carry, symbol)
    for c, b in product((0, 1, radix // 2, radix - 2, radix - 1), (0, 1)):
        inputs = {carry.variable: c, symbol.variable: b}
        assert arena.evaluate(function, inputs) == c
        assert arena.evaluate(division.remainder, inputs) == (2 * c + b) % radix
        assert arena.evaluate(division.quotient, inputs) == (2 * c + b) // radix
    assert len(arena.functions.nodes) < 20_000
    assert len(arena.nodes) == 3


def test_equivalent_arithmetic_derivations_have_identical_bit_function_ids() -> None:
    arena = BitFunctionArena(ResourceLedger())
    a = FinitePort(PortVariable(0, 0, "a", 0), 8)
    b = FinitePort(PortVariable(0, 0, "b", 0), 8)
    output = AtomSort("word", 8)
    aa = arena.variable((a, b), a, output)
    bb = arena.variable((a, b), b, output)
    zero = arena.constant(FunctionSignature((a, b), output), 0)
    assert arena.add(aa, bb, output) == arena.add(bb, aa, output)
    assert arena.add(aa, zero, output) == aa
    summed = arena.add(aa, bb, output)
    for x, y in product(range(8), repeat=2):
        assert arena.evaluate(summed, {a.variable: x, b.variable: y}) == (
            x + y if x + y < 8 else None
        )


def test_failed_factored_publication_is_atomic_across_boolean_and_numeric_arenas() -> (
    None
):
    arena = BitFunctionArena(ResourceLedger(max_cache_entries=0))
    before = arena.ledger.snapshot()
    carry, symbol = ports(3)
    with pytest.raises(BlockContextBudgetExceeded):
        arena.divide_binary(3, carry, symbol)
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
    assert (
        not arena.nodes
        and not arena.keys
        and not arena.functions.nodes
        and not arena.functions.keys
    )


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
def test_foreign_or_forged_factored_handles_reject_before_any_circuit_work(
    field: str, value: ArenaToken | Literal["semantic-function"] | bool | float
) -> None:
    arena = BitFunctionArena(ResourceLedger())
    carry, symbol = ports(3)
    division = arena.divide_binary(3, carry, symbol)
    handle = division.remainder
    forged = object.__new__(FactoredFunctionID)
    for name in ("owner", "kind", "local_id"):
        object.__setattr__(
            forged, name, value if name == field else getattr(handle, name)
        )
    assert_rejected_atomically(
        arena.ledger,
        lambda: arena.add(forged, handle, AtomSort("carry", 3)),
        ValueError,
    )


def test_finite_addition_rejects_overflow_instead_of_wrapping_through_domain_holes() -> (
    None
):
    arena = BitFunctionArena(ResourceLedger())
    output = AtomSort("three", 3)
    two = arena.constant(FunctionSignature((), output), 2)
    assert arena.evaluate(arena.add(two, two, output), {}) is None
    word = AtomSort("word", 4)
    word_two = arena.constant(FunctionSignature((), word), 2)
    assert arena.evaluate(arena.add(word_two, word_two, word, wrap=True), {}) == 0
    assert_rejected_atomically(
        arena.ledger,
        lambda: arena.add(two, two, output, wrap=True),
        ValueError,
        match="power-of-two",
    )
    # Truncating higher input bits must not make an unrepresentable sum valid.
    wide = arena.constant(FunctionSignature((), AtomSort("wide", 16)), 8)
    zero = arena.constant(FunctionSignature((), word), 0)
    assert arena.evaluate(arena.add(wide, zero, word), {}) is None


def test_select_checks_invalid_codes_of_every_common_input_even_in_unused_branch() -> (
    None
):
    arena = BitFunctionArena(ResourceLedger())
    x = FinitePort(PortVariable(0, 0, "x", 0), 2)
    y = FinitePort(PortVariable(0, 0, "y", 0), 3)
    bit = AtomSort("bit", 2)
    condition = arena.variable((x,), x, bit)
    yes = arena.constant(FunctionSignature((x,), bit), 1)
    no = arena.constant(FunctionSignature((y,), bit), 0)
    selected = arena.select(condition, yes, no)
    for xv, yv in product(range(2), range(4)):
        assert arena.evaluate(selected, {x.variable: xv, y.variable: yv}) == (
            xv if yv < 3 else None
        )
    # The same common-input function is canonical when domains are explicit.
    yes_all = arena.constant(FunctionSignature((x, y), bit), 1)
    no_all = arena.constant(FunctionSignature((x, y), bit), 0)
    assert selected == arena.select(condition, yes_all, no_all)


@pytest.mark.parametrize("cardinality", (3, 8))
def test_local_and_joint_substitution_share_complete_behavior_without_memo(
    cardinality: int,
) -> None:
    arena = BitFunctionArena(ResourceLedger())
    a = FinitePort(PortVariable(0, 0, "a", 0), cardinality)
    b = FinitePort(PortVariable(0, 1, "b", 0), cardinality)
    output = AtomSort("bounded-word", cardinality)
    aa, bb = (arena.variable((a, b), item, output) for item in (a, b))
    total = arena.add(aa, bb, output)
    replacements = {a.variable: total, b.variable: aa}
    joint = arena.substitute(total, replacements)
    arena._compositions.clear()
    before = arena.ledger.counters.get("semantic_bit_composition_evaluations", 0)
    local = arena.substitute(total, replacements, joint=False)
    assert arena.ledger.counters["semantic_bit_composition_evaluations"] == before + 1
    assert local == joint
    for x, y in product(range(1 << a.bits), range(1 << b.bits)):
        expected = 2 * x + y
        valid = x < cardinality and y < cardinality and expected < cardinality
        assert arena.evaluate(local, {a.variable: x, b.variable: y}) == (
            expected if valid else None
        )


def test_total_boolean_identities_avoid_shannon_construction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.hashlife.interfaces.semantic_bits import _Circuit

    arena = BitFunctionArena(ResourceLedger())
    port = FinitePort(PortVariable(0, 0, "carry", 0), 2)
    circuit = _Circuit(arena.functions, (port,))
    condition = circuit.tx.bit((port,), port.variable)

    def forbidden(*_args: object, **_kwargs: object) -> int:
        raise AssertionError("Boolean identity entered the Shannon scheduler")

    try:
        monkeypatch.setattr(circuit.tx, "choose", forbidden)
        zero, one = circuit.zero, circuit.one
        assert circuit.choose(condition, one, zero) == condition
        assert circuit.choose(condition, condition, zero) == condition
        assert circuit.choose(condition, one, condition) == condition
        assert circuit.choose(condition, zero, condition) == zero
        assert circuit.choose(condition, condition, one) == one
        assert arena.ledger.counters["semantic_bit_boolean_identity_reductions"] == 3
        assert arena.ledger.counters["semantic_bit_boolean_absorption_reductions"] == 2
    finally:
        circuit.tx.close()

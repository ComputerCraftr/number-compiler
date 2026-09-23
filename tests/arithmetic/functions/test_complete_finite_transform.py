"""Complete finite output identity, simultaneous composition and domain retention."""

from dataclasses import replace
from itertools import product

import pytest

from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.semantic_bits import BitFunctionArena
from number_compiler.hashlife.interfaces.semantic_bit_transforms import (
    CompleteFiniteTransform,
)
from number_compiler.resources.ledger import ResourceLedger


@pytest.mark.parametrize("cardinality,divisor", ((1, 1), (7, 1), (95, 5), (19, 32)))
def test_atom_division_is_bitwise_and_preserves_partiality(
    cardinality: int,
    divisor: int,
) -> None:
    bits = BitFunctionArena(ResourceLedger())
    port = FinitePort(PortVariable(0, 0, "atom", 0), cardinality)
    value = bits.variable((port,), port, AtomSort("atom", cardinality))
    q, r = bits.divmod_atoms(
        value,
        divisor,
        AtomSort("quotient", (cardinality - 1) // divisor + 1),
        AtomSort("remainder", divisor),
    )
    for i in range(1 << port.bits):
        result = tuple(bits.evaluate(f, {port.variable: i}) for f in (q, r))
        assert result == (divmod(i, divisor) if i < cardinality else (None, None))


def test_complete_swap_is_simultaneous_and_composition_is_canonical(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    bits = BitFunctionArena(ResourceLedger())
    ports = tuple(FinitePort(PortVariable(0, i, "value", 0), 2) for i in range(2))
    x, y = (bits.variable(ports, port, BOOL) for port in ports)
    allowed = bits.constant(FunctionSignature(ports, BOOL), 1)
    identity, _ = bits.complete_transform(ports, (x, y), allowed)
    swap, retained = bits.complete_transform(ports, (y, x), allowed, retained=(x,))
    with monkeypatch.context() as patch:

        def forbidden(*_args: object) -> int:
            raise AssertionError("composition evaluated a midpoint")

        patch.setattr(bits, "evaluate", forbidden)
        square, pulled = bits.compose_complete_transform(swap, swap, retained=retained)
        left, _ = bits.compose_complete_transform(square, swap)
        right, _ = bits.compose_complete_transform(swap, square)
    assert square == identity
    assert left == right == swap
    normalized, _ = bits.complete_transform(
        square.ports, square.outputs, square.admissible
    )
    assert normalized == square
    for a, b in product(range(2), repeat=2):
        binding = {ports[0].variable: a, ports[1].variable: b}
        assert tuple(bits.evaluate(f, binding) for f in square.outputs) == (a, b)
        assert bits.evaluate(pulled[0], binding) == b


def test_ignored_output_domain_is_not_erased_by_a_later_constant() -> None:
    bits = BitFunctionArena(ResourceLedger())
    port = FinitePort(PortVariable(0, 0, "value", 0), 3)
    sort = AtomSort("three", 3)
    source = bits.variable((port,), port, sort)
    one = bits.constant(FunctionSignature((), sort), 1)
    allowed = bits.constant(FunctionSignature((port,), BOOL), 1)
    increment = bits.add(source, one, sort)  # Undefined at input 2.
    before, _ = bits.complete_transform((port,), (increment,), allowed)
    zero = bits.constant(FunctionSignature((port,), sort), 0)
    after, _ = bits.complete_transform((port,), (zero,), allowed)
    result, _ = bits.compose_complete_transform(before, after)
    for value in range(3):
        binding = {port.variable: value}
        assert bits.evaluate(result.outputs[0], binding) == (0 if value < 2 else None)
        assert bits.evaluate(result.admissible, binding) == int(value < 2)


def test_retained_consumer_partiality_contributes_to_joint_admission() -> None:
    bits = BitFunctionArena(ResourceLedger())
    port = FinitePort(PortVariable(0, 0, "value", 0), 2)
    value = bits.variable((port,), port, BOOL)
    allowed = bits.constant(FunctionSignature((port,), BOOL), 1)
    partial = bits.add(value, value, BOOL)  # Only defined at 0.
    result, retained = bits.complete_transform(
        (port,), (value,), allowed, retained=(partial,)
    )
    bits.validate_complete_transform(result)
    assert bits.evaluate(result.outputs[0], {port.variable: 1}) is None
    assert bits.evaluate(retained[0], {port.variable: 1}) is None
    assert bits.evaluate(result.outputs[0], {port.variable: 0}) == 0


def test_foreign_or_inconsistent_transform_is_not_admitted() -> None:
    bits = BitFunctionArena(ResourceLedger())
    port = FinitePort(PortVariable(0, 0, "value", 0), 2)
    value = bits.variable((port,), port, BOOL)
    allowed = bits.constant(FunctionSignature((port,), BOOL), 1)
    identity, _ = bits.complete_transform((port,), (value,), allowed)
    foreign = BitFunctionArena(ResourceLedger())
    with pytest.raises(ValueError):
        foreign.validate_complete_transform(identity)
    forged = replace(identity, admissible=value)
    with pytest.raises(ValueError, match="domain"):
        bits.compose_complete_transform(forged, identity)
    extra = FinitePort(PortVariable(0, 1, "foreign", 0), 2)
    undeclared = bits.variable((extra,), extra, BOOL)
    with pytest.raises(ValueError, match="undeclared"):
        bits.complete_transform((port,), (undeclared,), allowed)


def test_partial_guard_and_false_guard_have_one_semantic_identity() -> None:
    bits = BitFunctionArena(ResourceLedger())
    port = FinitePort(PortVariable(0, 0, "value", 0), 2)
    value = bits.variable((port,), port, BOOL)
    one = bits.constant(FunctionSignature((port,), BOOL), 1)
    partial_guard = bits.add(value, one, BOOL)  # True at 0, undefined at 1.
    total_guard = bits.domain_predicate(partial_guard)
    partial, _ = bits.complete_transform((port,), (value,), partial_guard)
    total, _ = bits.complete_transform((port,), (value,), total_guard)
    assert partial == total
    bits.validate_complete_transform(partial)
    assert bits.evaluate(partial.admissible, {port.variable: 1}) == 0
    with pytest.raises(ValueError, match="total"):
        bits.validate_complete_transform(replace(total, admissible=partial_guard))


@pytest.mark.parametrize("partial", (False, True))
def test_constant_and_subset_guards_extend_to_the_complete_port_domain(
    partial: bool, monkeypatch: pytest.MonkeyPatch
) -> None:
    bits = BitFunctionArena(ResourceLedger())
    ports = tuple(FinitePort(PortVariable(0, i, "value", 0), 2) for i in range(2))
    outputs = tuple(bits.variable(ports, port, BOOL) for port in ports)
    one = bits.constant(FunctionSignature((), BOOL), 1)
    subset = bits.variable((ports[0],), ports[0], BOOL)
    guard = bits.add(subset, one, BOOL) if partial else subset

    def forbidden(*_args: object) -> int:
        raise AssertionError("admission used scalar restriction")

    monkeypatch.setattr(bits, "restrict", forbidden)
    identity, _ = bits.complete_transform(ports, outputs, one)
    restricted, _ = bits.complete_transform(ports, outputs, guard)
    bits.validate_complete_transform(identity)
    bits.validate_complete_transform(restricted)
    for a, b in product(range(2), repeat=2):
        binding = dict(zip((p.variable for p in ports), (a, b), strict=True))
        assert bits.evaluate(identity.admissible, binding) == 1
        assert bits.evaluate(restricted.admissible, binding) == int(a != partial)
        expected = (a, b) if a != partial else (None, None)
        assert tuple(bits.evaluate(f, binding) for f in restricted.outputs) == expected


@pytest.mark.parametrize("table", tuple(product((None, 0, 1), repeat=2)))
def test_partial_action_identity_survives_every_boolean_future_and_squaring(
    table: tuple[int | None, int | None], monkeypatch: pytest.MonkeyPatch
) -> None:
    """Exhaust the partial one-bit algebra, not a recursive source constructor."""
    bits = BitFunctionArena(ResourceLedger())
    port = FinitePort(PortVariable(0, 0, "value", 0), 2)
    value = bits.variable((port,), port, BOOL)
    one = bits.constant(FunctionSignature((port,), BOOL), 1)

    def action(
        entries: tuple[int | None, ...], *, partial_guard: bool
    ) -> CompleteFiniteTransform:
        output = bits.map_atoms(
            value, BOOL, tuple(0 if x is None else x for x in entries)
        )
        guard = bits.map_atoms(value, BOOL, tuple(int(x is not None) for x in entries))
        if partial_guard:
            guard = bits.restrict(one, guard)
        return bits.complete_transform((port,), (output,), guard)[0]

    before = action(table, partial_guard=False)
    equivalent = action(table, partial_guard=True)
    assert before == equivalent
    for future in product((None, 0, 1), repeat=2):
        after = action(future, partial_guard=False)
        with monkeypatch.context() as patch:

            def forbidden(*_args: object) -> int:
                raise AssertionError("saturation evaluated a midpoint")

            patch.setattr(bits, "evaluate", forbidden)
            patch.setattr(bits, "restrict", forbidden)
            left, _ = bits.compose_complete_transform(before, after)
            right, _ = bits.compose_complete_transform(equivalent, after)
            assert left == right
            expected = tuple(None if x is None else future[x] for x in table)
            for _ in range(3):  # D2, D4, D8 of each composed partial action.
                left, _ = bits.compose_complete_transform(left, left)
                right, _ = bits.compose_complete_transform(right, right)
                assert left == right
                expected = tuple(None if x is None else expected[x] for x in expected)
        for source in range(2):
            binding = {port.variable: source}
            assert bits.evaluate(left.outputs[0], binding) == expected[source]
            assert bits.evaluate(left.admissible, binding) == int(
                expected[source] is not None
            )

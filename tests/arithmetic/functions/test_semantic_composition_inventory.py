"""Actual complete-function substitutions must agree beyond record types."""

from __future__ import annotations

from dataclasses import replace
from typing import TYPE_CHECKING, Never, cast

import pytest

from number_compiler.arithmetic.functions.finite_function_types import (
    AtomSort,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.semantic_bit_records import BitSubstitutionKey
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
)
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.semantic_bit_records import (
        BitSubstitutionKey,
    )
from number_compiler.hashlife.interfaces.semantic_bits import (
    FactoredFunctionID,
)


def _compositions(
    arena: BitFunctionArena,
) -> OwnedMemo[BitSubstitutionKey, FactoredFunctionID]:
    return cast(
        OwnedMemo[BitSubstitutionKey, FactoredFunctionID],
        object.__getattribute__(arena, "_compositions"),
    )


def _replace_composition(
    arena: BitFunctionArena, key: BitSubstitutionKey, value: FactoredFunctionID
) -> None:
    storage = cast(
        dict[BitSubstitutionKey, FactoredFunctionID],
        object.__getattribute__(_compositions(arena), "_data"),
    )
    storage[key] = value


def fixture() -> tuple[
    BitFunctionArena,
    tuple[FinitePort, ...],
    AtomSort,
    FactoredFunctionID,
    FactoredFunctionID,
    FactoredFunctionID,
]:
    arena = BitFunctionArena(ResourceLedger())
    ports = tuple(
        FinitePort(PortVariable(index, 0, "input", 0), 3) for index in range(2)
    )
    sort = AtomSort("three", 3)
    x, y = (arena.variable(ports, port, sort) for port in ports)
    function = arena.add(x, y, sort)
    return arena, ports, sort, function, x, y


@pytest.mark.parametrize(
    "mode", ("swap", "correlated", "partial", "constant", "unused-partial")
)
def test_complete_composition_audit_handles_correlations_and_simultaneous_partial_inputs(
    mode: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    arena, ports, sort, function, x, y = fixture()
    two = arena.constant(FunctionSignature((), sort), 2)
    invalid = arena.add(two, two, sort)
    if mode == "swap":
        args = {ports[0].variable: y, ports[1].variable: x}
    elif mode == "correlated":
        args = {ports[0].variable: y, ports[1].variable: y}
    elif mode == "partial":
        args = {ports[0].variable: invalid}
    elif mode == "constant":
        args = {ports[0].variable: two}
    else:
        function = arena.constant(FunctionSignature(ports, sort), 1)
        args = {ports[0].variable: invalid}
    arena.substitute(function, args)
    before = arena.ledger.snapshot()

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("audit used production composition or point evaluation")

    monkeypatch.setattr(arena, "substitute", forbidden)
    monkeypatch.setattr(arena, "evaluate", forbidden)
    monkeypatch.setattr(arena.functions, "evaluate", forbidden)
    report = collect_ledger_metrics(arena.ledger)
    assert report.resource_audit_complete == 1
    assert report.forbidden_future_payloads == 0
    assert arena.ledger.snapshot() == before


@pytest.mark.parametrize(
    "mode",
    (
        "wrong-value",
        "foreign-target",
        "foreign-source",
        "duplicate-port",
        "unknown-port",
    ),
)
def test_memo_injection_rejects_wrong_semantics_scope_and_replacement_declarations(
    mode: str,
) -> None:
    arena, ports, _sort, function, x, y = fixture()
    arena.substitute(function, {ports[0].variable: y})
    key, result = next(iter(_compositions(arena).items()))
    if mode == "wrong-value":
        result = arena.constant(arena.resolve(result).signature, 0)
    elif mode == "foreign-target":
        foreign = BitFunctionArena(arena.ledger, arena.functions)
        result = foreign.constant(arena.resolve(result).signature, 0)
    elif mode == "foreign-source":
        foreign = BitFunctionArena(arena.ledger, arena.functions)
        key = replace(
            key, function=foreign.constant(arena.resolve(function).signature, 0)
        )
    elif mode == "duplicate-port":
        key = replace(key, replacements=key.replacements * 2)
    else:
        key = replace(key, replacements=((PortVariable(10, 0, "not-a-port", 0), x),))
    if key not in _compositions(arena):
        arena.ledger.reserve(_compositions(arena).owner, entries=1)
    _replace_composition(arena, key, result)
    before = arena.ledger.snapshot()
    report = collect_ledger_metrics(arena.ledger)
    assert report.forbidden_future_payloads > 0
    assert report.representation_boundary_complete == 0
    assert arena.ledger.snapshot() == before


def test_late_source_bit_arguments_are_cofactored_in_external_variable_order(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.functions.finite_function_types import BOOL
    from number_compiler.hashlife.interfaces.semantic_bits import BooleanCircuit

    arena = BitFunctionArena(ResourceLedger())
    left = FinitePort(PortVariable(0, 0, "a", 0), 6)
    right = FinitePort(PortVariable(0, 1, "b", 0), 3)
    ports = (left, right)
    a = arena.variable(ports, left, AtomSort("a-value", 6))
    b = arena.variable(ports, right, AtomSort("b-value", 3))
    zero = arena.constant(FunctionSignature(ports, AtomSort("b-value", 3)), 0)
    circuit = BooleanCircuit(arena.functions, ports)
    aa, av = circuit.imported(arena.resolve(a))
    bb, bv = circuit.imported(arena.resolve(b))
    a_is_one = circuit.conjunction(
        aa[0], circuit.conjunction(circuit.negate(aa[1]), circuit.negate(aa[2]))
    )
    b_is_two = circuit.conjunction(circuit.negate(bb[0]), bb[1])
    predicate = circuit.negate(circuit.conjunction(a_is_one, b_is_two))
    signature = FunctionSignature(ports, BOOL)
    function = arena.publish_circuit(
        circuit,
        (circuit.normalized(signature, (predicate,), circuit.conjunction(av, bv)),),
    )[0]
    # f(a,b)=not(a==1 and b==2); f(a,0) is true on all18 legal inputs.
    # Masked later a-bits can depend on an earlier external variable; the old
    # audit revisited that variable and invented a contradictory invalid cube.
    target = arena.substitute(function, {left.variable: a, right.variable: zero})
    before = arena.ledger.snapshot()

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("inventory performed semantic execution")

    monkeypatch.setattr(arena.functions, "evaluate", forbidden)
    monkeypatch.setattr(arena, "substitute", forbidden)
    assert collect_ledger_metrics(arena.ledger).forbidden_future_payloads == 0
    assert arena.ledger.snapshot() == before

    # Keep the strict padding contract: an everywhere-true extension has the
    # same legal values but is not a normalized result on undeclared codes.
    bad_circuit = BooleanCircuit(arena.functions, ports)
    bad = arena.publish_circuit(
        bad_circuit,
        (bad_circuit.normalized(signature, (bad_circuit.one,), bad_circuit.one),),
    )[0]
    key = next(
        key
        for key, value in _compositions(arena).items()
        if key.function == function and value == target
    )
    _replace_composition(arena, key, bad)
    before = arena.ledger.snapshot()
    assert collect_ledger_metrics(arena.ledger).forbidden_future_payloads > 0
    assert arena.ledger.snapshot() == before

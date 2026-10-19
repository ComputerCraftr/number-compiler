"""Padding predicates need threshold decisions, never numeric output words."""

from __future__ import annotations

import itertools
from typing import Never

import pytest

from number_compiler.arithmetic.functions.finite_function_types import FinitePort
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_function_transactions import (
    _Transaction,
)
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
    BooleanCircuit,
)
from number_compiler.resources.ledger import ResourceLedger


def raw_boolean(
    circuit: BooleanCircuit,
    root: int,
    values: dict[PortVariable, int],
) -> int:
    """Observe every binary code, including codes outside the declared domain."""
    node = circuit.tx.node(root)
    while node.terminal is None:
        variable = node.variable
        assert variable is not None
        original = PortVariable(variable.time, variable.side, variable.role, 0)
        assert variable is not None
        node = circuit.tx.node(
            node.high if (values[original] >> variable.bit) & 1 else node.low
        )
    assert node.terminal.kind == "atom"
    return node.terminal.value


@pytest.mark.parametrize("cardinality", range(1, 66))
def test_threshold_matches_all_small_codes_without_subtraction_or_ite(
    cardinality: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    bits = BitFunctionArena(ResourceLedger())
    port = FinitePort(PortVariable(0, 0, "input", 0), cardinality)
    circuit = BooleanCircuit(bits.functions, (port,))

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError(
            "admission constructed a numeric subtraction or generic ITE"
        )

    monkeypatch.setattr(BooleanCircuit, "subtract_constant", forbidden)
    monkeypatch.setattr(_Transaction, "choose", forbidden)
    root = circuit.admitted()
    for value in range(1 << port.bits):
        assert raw_boolean(circuit, root, {port.variable: value}) == int(
            value < cardinality
        )
    count = len(circuit.tx.staged)
    assert circuit.admitted() == root
    assert len(circuit.tx.staged) == count
    assert (
        bits.ledger.counters.get("semantic_bit_admissibility_threshold_decisions", 0)
        <= 2 * port.bits
    )


def test_joint_padding_preserves_each_port_domain_and_order(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    bits = BitFunctionArena(ResourceLedger())
    ports = tuple(
        FinitePort(PortVariable(i, i % 2, "input", 0), n)
        for i, n in enumerate((3, 5, 8, 1))
    )
    circuit = BooleanCircuit(bits.functions, ports)

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("joint admission performed ITE composition")

    monkeypatch.setattr(_Transaction, "choose", forbidden)
    root = circuit.admitted()
    for values in itertools.product(*(range(1 << p.bits) for p in ports)):
        actual = raw_boolean(
            circuit, root, dict(zip((p.variable for p in ports), values, strict=True))
        )
        assert actual == int(
            all(
                value < port.cardinality
                for port, value in zip(ports, values, strict=True)
            )
        )
    assert bits.ledger.counters[
        "semantic_bit_admissibility_threshold_decisions"
    ] <= 2 * sum(p.bits for p in ports)


@pytest.mark.parametrize("cardinality", ((1 << 64) - 1, (1 << 63) + 1, (1 << 32) + 17))
def test_wide_threshold_work_scales_with_encoded_bits(cardinality: int) -> None:
    bits = BitFunctionArena(ResourceLedger())
    port = FinitePort(PortVariable(0, 0, "wide", 0), cardinality)
    circuit = BooleanCircuit(bits.functions, (port,))
    root = circuit.admitted()
    for value in (0, 1, cardinality - 1, cardinality, (1 << port.bits) - 1):
        assert raw_boolean(circuit, root, {port.variable: value}) == int(
            value < cardinality
        )
    assert (
        bits.ledger.counters["semantic_bit_admissibility_threshold_decisions"]
        <= 2 * port.bits
    )
    assert (
        bits.ledger.counters["semantic_bit_admissibility_threshold_frames"]
        <= 6 * port.bits + 1
    )

"""Ordered reconstruction reuses nodes; moved variables still reorder exactly."""

from itertools import product
from typing import Never

import pytest

from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_function_transactions import (
    _Transaction,
)
from number_compiler.hashlife.interfaces.semantic_bits import BitFunctionArena
from number_compiler.resources.ledger import ResourceLedger


def test_unchanged_decision_rebuild_does_not_enter_generic_shannon_apply(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    bits = BitFunctionArena(ResourceLedger())
    x = FinitePort(PortVariable(0, 0, "x", 0), 2)
    value = bits.variable((x,), x, BOOL)
    tx = _Transaction(bits.functions)
    root = bits.resolve(value).bits[0].local_id

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("unchanged split unnecessarily replayed generic apply")

    monkeypatch.setattr(tx, "choose", forbidden)
    result = tx.map_terminals(
        root,
        FunctionSignature((x,), BOOL),
        lambda leaf: tx.terminal(FunctionSignature((x,), BOOL), leaf),
    )
    assert result == root
    assert bits.ledger.counters["semantic_direct_decision_rebuilds"] > 0
    assert not tx.staged


def test_replacement_that_moves_a_variable_earlier_keeps_shannon_reordering() -> None:
    bits = BitFunctionArena(ResourceLedger())
    x, y, z = (FinitePort(PortVariable(0, 0, name, 0), 2) for name in ("x", "y", "z"))
    vx = bits.variable((x,), x, BOOL)
    vy = bits.variable((y, z), y, BOOL)
    vz = bits.variable((y, z), z, BOOL)
    expression = bits.add(vy, vz, BOOL, wrap=True)
    result = bits.substitute(expression, {z.variable: vx})
    for a, b in product(range(2), repeat=2):
        assert bits.evaluate(result, {x.variable: a, y.variable: b}) == a ^ b
    assert bits.ledger.counters["semantic_reordered_decision_rebuilds"] > 0


def test_canonical_child_ids_hit_before_derived_support_work(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    bits = BitFunctionArena(ResourceLedger())
    port = FinitePort(PortVariable(0, 0, "x", 0), 2)
    value = bits.variable((port,), port, BOOL)
    identity = bits.resolve(value).bits[0].local_id
    node = bits.functions.nodes[identity]
    tx = _Transaction(bits.functions)

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("known decision rebuilt dependency metadata")

    monkeypatch.setattr(tx, "_decision_support", forbidden)
    assert node.variable is not None
    assert tx.decision(node.signature, node.variable, node.low, node.high) == identity
    assert not tx.staged
    assert bits.ledger.counters["semantic_decision_early_hits"] > 0


def test_support_metadata_cannot_change_semantic_identity_but_is_audited() -> None:
    from dataclasses import replace

    from number_compiler.hashlife.execution.diamond_payload import (
        DiamondPayloadRegistry,
    )
    from number_compiler.resources.semantic_payload import SemanticPayloadRegistry

    bits = BitFunctionArena(ResourceLedger())
    port = FinitePort(PortVariable(0, 0, "x", 0), 2)
    value = bits.variable((port,), port, BOOL)
    identity = bits.resolve(value).bits[0].local_id
    node = bits.functions.nodes[identity]
    assert replace(node, support=()) == node
    original = node.support
    object.__setattr__(node, "support", ())
    try:
        diamond = DiamondPayloadRegistry(bits.ledger)
        registry = SemanticPayloadRegistry(
            bits.ledger, lambda item: False, diamond._handle
        )
        assert not registry.valid(bits.functions._handle(identity))
    finally:
        object.__setattr__(node, "support", original)

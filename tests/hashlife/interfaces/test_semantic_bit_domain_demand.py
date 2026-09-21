"""Admission demands consume validity support without importing output roots."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_function_transactions import (
    _Transaction,
)
from number_compiler.hashlife.interfaces.semantic_bits import BitFunctionArena
from number_compiler.resources.ledger import ResourceLedger


@pytest.mark.parametrize("width", (8, 32, 64))
def test_domain_demand_does_not_import_value_roots(
    width: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    ledger = ResourceLedger()
    bits = BitFunctionArena(ledger)
    sort = AtomSort("wide-domain-demand", 1 << width)
    number = FinitePort(PortVariable(0, 0, "value", 0), sort.cardinality)
    admitted = FinitePort(PortVariable(0, 1, "admitted", 0), 2)
    ports = (number, admitted)
    value = bits.variable(ports, number, sort)
    guard = bits.variable(ports, admitted, BOOL)
    partial = bits.restrict(value, guard)
    node = bits.resolve(partial)
    value_roots = {root.local_id for root in node.bits if root != node.valid}
    assert len(value_roots) == width
    original = _Transaction.resign

    def validity_only(
        transaction: _Transaction, root: int, signature: FunctionSignature
    ) -> int:
        assert root not in value_roots, "domain demand imported an output root"
        return original(transaction, root, signature)

    requests = ledger.counters.get("semantic_function_resign_requests", 0)
    with monkeypatch.context() as patch:
        patch.setattr(_Transaction, "resign", validity_only)
        domain = bits.domain_predicate(partial)
    assert ledger.counters["semantic_function_resign_requests"] - requests == 1
    assert bits.resolve(domain).signature == FunctionSignature(ports, BOOL)
    for number_value in (0, 1, (1 << width) - 1):
        for is_admitted in (0, 1):
            inputs = {number.variable: number_value, admitted.variable: is_admitted}
            assert bits.evaluate(domain, inputs) == is_admitted
            assert bits.evaluate(partial, inputs) == (
                number_value if is_admitted else None
            )


def test_domain_demand_rejects_foreign_validity_before_construction() -> None:
    ledger = ResourceLedger()
    bits = BitFunctionArena(ledger)
    foreign = BitFunctionArena(ResourceLedger())
    signature = FunctionSignature((), BOOL)
    value = bits.constant(signature, 0)
    node = bits.resolve(value)
    valid = node.valid
    alien = foreign.resolve(foreign.constant(signature, 1)).valid
    before = dict(ledger.counters)
    object.__setattr__(node, "valid", alien)
    try:
        with pytest.raises(ValueError):
            bits.domain_predicate(value)
        assert dict(ledger.counters) == before
    finally:
        object.__setattr__(node, "valid", valid)

"""Port padding reuse must precede decision construction and remain evictable."""

from __future__ import annotations

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FinitePort,
    FunctionSignature,
    SemanticRequest,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.interfaces.semantic_bits import BitFunctionArena, _Circuit
from number_compiler.hashlife.interfaces.semantic_publication import PreparedFunctions
from number_compiler.resources.ledger import ResourceLedger


def _arena() -> tuple[ResourceLedger, BitFunctionArena, FinitePort]:
    ledger = ResourceLedger()
    functions = SemanticFunctionArena(ledger, cache_construction_reductions=True)
    bits = BitFunctionArena(ledger, functions)
    port = FinitePort(PortVariable(0, 0, "carry", 0), 43)
    return ledger, bits, port


def test_new_circuit_reuses_complete_admission_without_threshold_descent(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, bits, port = _arena()
    signature = FunctionSignature((port,), BOOL)
    first = bits.constant(signature, 0)
    assert SemanticRequest("bit-admissibility", (), (port,)) in bits.functions.memo

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("warm port admission rebuilt its threshold function")

    monkeypatch.setattr(_Circuit, "_admitted_port", forbidden)
    second = bits.constant(signature, 1)
    assert ledger.counters["semantic_bit_admissibility_early_hits"] > 0
    for value in range(64):
        assignment = {port.variable: value}
        assert bits.evaluate(first, assignment) == (0 if value < 43 else None)
        assert bits.evaluate(second, assignment) == (1 if value < 43 else None)
    assert all(row.accounting_delta == 0 for row in ledger.inventory())


def test_admission_eviction_rebuilds_and_keeps_canonical_function_identity() -> None:
    ledger, bits, port = _arena()
    signature = FunctionSignature((port,), BOOL)
    first = bits.constant(signature, 1)
    before = ledger.counters["semantic_bit_admissibility_evaluations"]
    bits.functions._evict()
    assert bits.constant(signature, 1) == first
    assert ledger.counters["semantic_bit_admissibility_evaluations"] == before + 1
    assert all(row.accounting_delta == 0 for row in ledger.inventory())


def test_admission_publication_failure_releases_transient_and_retained_charge() -> None:
    ledger, bits, port = _arena()
    before = ledger.snapshot()
    ledger.max_cache_entries = before.entries
    with pytest.raises(BlockContextBudgetExceeded):
        bits.constant(FunctionSignature((port,), BOOL), 1)
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    assert not bits.functions.memo
    assert all(row.accounting_delta == 0 for row in after.inventory)


def test_admission_lookup_rejects_another_signature_before_reuse() -> None:
    ledger, bits, port = _arena()
    bits.constant(FunctionSignature((port,), BOOL), 1)
    key = SemanticRequest("bit-admissibility", (), (port,))
    other_port = FinitePort(PortVariable(0, 0, "other", 0), 3)
    other = bits.constant(FunctionSignature((other_port,), BOOL), 1)
    bits.functions.memo[key] = bits.resolve(other).valid
    before = ledger.snapshot()
    circuit = _Circuit(bits.functions, (port,))
    try:
        with pytest.raises(ValueError, match="another signature"):
            circuit.admitted()
    finally:
        circuit.tx.close()
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)


def test_commit_failure_removes_published_admission_and_function_nodes(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, bits, port = _arena()
    before = ledger.snapshot()

    def fail(_prepared: PreparedFunctions) -> Never:
        raise RuntimeError("injected semantic commit failure")

    monkeypatch.setattr(PreparedFunctions, "_commit", fail)
    with pytest.raises(RuntimeError, match="injected semantic commit"):
        bits.constant(FunctionSignature((port,), BOOL), 1)
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    assert not bits.functions.memo
    assert not bits.functions.nodes
    assert not bits.functions.keys
    assert not bits.nodes
    assert all(row.accounting_delta == 0 for row in after.inventory)

"""Canonical construction reductions reuse work without retaining staged nodes."""

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FinitePort,
    FunctionSignature,
    SemanticRequest,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_function_transactions import (
    _Transaction,
)
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.resources.ledger import ResourceLedger


def _construction() -> tuple[SemanticFunctionArena, tuple[int, int, int]]:
    arena = SemanticFunctionArena(ResourceLedger(), cache_construction_reductions=True)
    ports = tuple(FinitePort(PortVariable(0, 0, name, 0), 2) for name in ("a", "b"))
    a, b = (arena.variable(ports, port, BOOL) for port in ports)
    zero = arena.atom(FunctionSignature(ports, BOOL), 0)
    return arena, (a.local_id, b.local_id, zero.local_id)


def test_constructed_choice_hits_before_descendant_reduction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena, operands = _construction()
    transaction = _Transaction(arena)
    result = transaction.finish(transaction.choose(*operands))
    assert arena.ledger.counters["semantic_ite_reduction_publications"] > 0
    frames = arena.ledger.counters["semantic_function_ite_frames"]

    def forbidden(*_args: object) -> int:
        raise AssertionError("warm canonical reduction visited descendants")

    monkeypatch.setattr(_Transaction, "decision", forbidden)
    warm = _Transaction(arena)
    assert warm.choose(*operands) == result.local_id
    assert arena.ledger.counters["semantic_function_ite_frames"] == frames
    assert arena.ledger.counters["semantic_ite_canonical_early_hits"] > 0


def test_reduction_failure_publishes_neither_nodes_nor_memo_entries() -> None:
    arena, operands = _construction()
    transaction = _Transaction(arena)
    root = transaction.choose(*operands)
    arena.ledger.max_cache_entries = arena.ledger.entries
    before = (
        tuple(arena.nodes),
        dict(arena.keys),
        dict(arena.memo),
    )
    with pytest.raises(BlockContextBudgetExceeded):
        transaction.finish(root)
    assert before == (
        tuple(arena.nodes),
        dict(arena.keys),
        dict(arena.memo),
    )
    workspace = next(
        row
        for row in arena.ledger.inventory()
        if row.role == "semantic_function_workspace"
    )
    assert workspace.entries == workspace.nodes == 0
    assert workspace.accounting_delta == 0


def test_reduction_eviction_preserves_canonical_nodes_and_charges_recomputation() -> (
    None
):
    arena, operands = _construction()
    transaction = _Transaction(arena)
    result = transaction.finish(transaction.choose(*operands))
    node_count = len(arena.nodes)
    frames = arena.ledger.counters["semantic_function_ite_frames"]
    arena.ledger.evict_query_memos()
    assert not arena.memo
    again = _Transaction(arena)
    assert again.finish(again.choose(*operands)) == result
    assert len(arena.nodes) == node_count
    assert arena.ledger.counters["semantic_function_ite_frames"] > frames
    inventory = arena.ledger.inventory()
    assert sum(item.entries for item in inventory) == arena.ledger.entries
    assert all(item.accounting_delta in (0, None) for item in inventory)


def test_total_circuit_choice_cannot_poison_public_padding_semantics() -> None:
    arena = SemanticFunctionArena(ResourceLedger(), cache_construction_reductions=True)
    port = FinitePort(PortVariable(0, 0, "ternary", 0), 3)
    signature = FunctionSignature((port,), BOOL)
    transaction = _Transaction(arena)
    condition = transaction.bit((port,), PortVariable(0, 0, "ternary", 0))
    # Circuit internals are total on encoded padding, unlike public functions.
    from number_compiler.arithmetic.functions.finite_function_types import (
        SemanticTerminal,
    )

    one = transaction.terminal(signature, SemanticTerminal("atom", 1))
    zero = transaction.terminal(signature, SemanticTerminal("atom", 0))
    c = transaction.finish(condition)
    one, zero = (
        arena.keys[
            next(
                n
                for n in arena.nodes
                if n.signature == signature
                and n.terminal == SemanticTerminal("atom", v)
            )
        ]
        for v in (1, 0)
    )
    raw = _Transaction(arena)
    output = raw.finish(raw.choose(c.local_id, zero, one))
    assert arena.evaluate(output, {port.variable: 3}).kind == "atom"
    public = arena.ite(c, arena._handle(zero), arena._handle(one))
    assert arena.evaluate(public, {port.variable: 3}).kind == "invalid"
    assert any(key.operation == "construction-ite" for key in arena.memo)
    assert (
        SemanticRequest("ite", (c, arena._handle(zero), arena._handle(one)))
        in arena.memo
    )

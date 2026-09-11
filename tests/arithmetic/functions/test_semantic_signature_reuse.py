"""Declaration changes share canonical child work within one transaction."""

from itertools import product
from typing import Never

import pytest

from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FinitePort,
    FunctionSignature,
    SemanticTerminal,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_function_transactions import (
    _Transaction,
)
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.resources.ledger import ResourceLedger


def test_shared_redeclaration_is_checked_before_descending(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    arena = SemanticFunctionArena(ledger)
    x, y = (FinitePort(PortVariable(0, 0, name, 0), 2) for name in ("x", "y"))
    original = arena.variable((x,), x, BOOL)
    tx = _Transaction(arena)
    signature = FunctionSignature((x, y), BOOL)
    first = tx.resign(original.local_id, signature)
    retained = ledger.snapshot()
    count = len(tx.staged)

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("known declaration descended into its semantic DAG")

    monkeypatch.setattr(tx, "rebuilt_decision", forbidden)
    assert tx.resign(original.local_id, signature) == first
    assert len(tx.staged) == count
    assert ledger.snapshot().entries == retained.entries
    assert ledger.counters["semantic_function_resign_cache_hits"] == 1
    result = tx.finish(first)
    for xx, yy in product(range(2), repeat=2):
        assert arena.evaluate(
            result, {x.variable: xx, y.variable: yy}
        ) == SemanticTerminal("atom", xx)


def test_redeclaration_shares_internal_children_and_preserves_partial_values() -> None:
    ledger = ResourceLedger()
    arena = SemanticFunctionArena(ledger)
    x = FinitePort(PortVariable(0, 0, "x", 0), 3)
    y = FinitePort(PortVariable(0, 0, "y", 0), 5)
    original = arena.variable((x,), x)
    source = arena.resolve(original)
    tx = _Transaction(arena)
    signature = FunctionSignature((x, y), source.signature.output)
    # Import the high subtree first; the complete parent must reuse that walk.
    child = source.high
    assert child >= 0
    tx.resign(child, signature)
    result = tx.finish(tx.resign(original.local_id, signature))
    assert ledger.counters["semantic_function_resign_shared_child_hits"] > 0
    # Resigning changes declarations, not admissibility. Invalid original
    # x codes remain invalid; newly declared y is unobserved until masking.
    for xx, yy in product(range(4), range(8)):
        expected = arena.evaluate(original, {x.variable: xx})
        assert arena.evaluate(result, {x.variable: xx, y.variable: yy}) == expected

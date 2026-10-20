"""Early identical-branch sharing must retain undefined-condition semantics."""

from collections.abc import Callable
from typing import Never, cast

import pytest

from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
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


def test_equal_branches_skip_decisions_after_total_condition_proof(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena = SemanticFunctionArena(ResourceLedger())
    inputs = (FinitePort(PortVariable(0, 0, "input", 0), 128),)
    tx = _Transaction(arena)
    condition = tx.bit(inputs, inputs[0].variable)
    signature = FunctionSignature(inputs, AtomSort("output", 3))
    zero = tx.terminal(signature, SemanticTerminal("atom", 0))
    one = tx.terminal(signature, SemanticTerminal("atom", 1))

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("equal branches descended into semantic decisions")

    monkeypatch.setattr(_Transaction, "decision", forbidden)
    assert tx.choose(condition, zero, zero) == zero
    assert tx.choose(condition, one, one) == one
    assert arena.ledger.counters["semantic_identical_branch_reductions"] == 2


@pytest.mark.parametrize("undefined_high", (False, True))
def test_equal_branches_do_not_erase_partial_condition(undefined_high: bool) -> None:
    arena = SemanticFunctionArena(ResourceLedger())
    port = FinitePort(PortVariable(0, 0, "condition", 0), 2)
    inputs = (port,)
    signature = FunctionSignature(inputs, BOOL)
    tx = _Transaction(arena)
    zero = tx.terminal(signature, SemanticTerminal("atom", 0))
    invalid = tx.terminal(signature, SemanticTerminal("invalid"))
    low, high = (zero, invalid) if undefined_high else (invalid, zero)
    condition = tx.decision(signature, port.variable, low, high)
    result = tx.choose(condition, zero, zero)
    assert result != zero
    node = tx.node(result)
    terminal = tx.node(node.high if undefined_high else node.low).terminal
    assert terminal is not None and terminal.kind == "invalid"
    assert tx.node(
        node.low if undefined_high else node.high
    ).terminal == SemanticTerminal("atom", 0)


def test_existing_padded_condition_is_proved_once_per_transaction() -> None:
    arena = SemanticFunctionArena(ResourceLedger())
    port = FinitePort(PortVariable(0, 0, "three-state", 0), 3)
    # Public total-on-admissible inputs still has an invalid padding branch.
    condition = arena.atom(FunctionSignature((port,), BOOL), 1)
    tx = _Transaction(arena)
    assert not cast(
        Callable[[int], bool], object.__getattribute__(tx, "_total_condition")
    )(condition.local_id)
    frames = arena.ledger.counters["semantic_total_condition_frames"]
    assert not cast(
        Callable[[int], bool], object.__getattribute__(tx, "_total_condition")
    )(condition.local_id)
    assert arena.ledger.counters["semantic_total_condition_frames"] == frames

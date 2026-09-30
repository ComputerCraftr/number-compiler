"""Canonical symbolic totality proof over admitted semantic decision DAGs."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FinitePort,
    FunctionSignature,
    SemanticFunctionID,
    SemanticNode,
    SemanticTerminal,
)
from number_compiler.arithmetic.functions.semantic_function_transactions import (
    _Transaction,
)

if TYPE_CHECKING:
    from number_compiler.arithmetic.functions.semantic_functions import (
        SemanticFunctionArena,
    )


def totality_predicate(tx: _Transaction, identity: int) -> int:
    signature = tx.node(identity).signature
    return tx.map_terminals(
        identity,
        signature,
        lambda leaf: tx.terminal(
            signature,
            SemanticTerminal("atom", int(leaf.kind == "atom" and leaf.value == 1)),
        ),
    )


def split_semantic_pair(
    pair: tuple[int, int], value: SemanticNode, condition: SemanticNode
) -> tuple[tuple[int, int], tuple[int, int]]:
    """Cofactor both sides of an implication at its earliest live decision."""
    variable = min(
        node.variable for node in (value, condition) if node.variable is not None
    )
    low = tuple(
        node.low if node.variable == variable else identity
        for node, identity in zip((value, condition), pair, strict=True)
    )
    high = tuple(
        node.high if node.variable == variable else identity
        for node, identity in zip((value, condition), pair, strict=True)
    )
    return (low[0], low[1]), (high[0], high[1])


def require_semantic_total(
    functions: SemanticFunctionArena,
    references: tuple[SemanticFunctionID, ...],
    admissible: SemanticFunctionID,
) -> None:
    """Prove complete channels and referenced inner functions in one workspace."""
    if not references:
        return
    allowed = functions.resolve(admissible)
    inputs = functions.resolve(references[0]).signature.inputs
    if allowed.signature != FunctionSignature(inputs, BOOL) or any(
        functions.resolve(item).signature.inputs != inputs for item in references
    ):
        raise ValueError("totality requires the full Boolean admissibility interface")
    tx = _Transaction(functions)
    try:
        admitted = totality_predicate(tx, admissible.local_id)
        pending = [(reference.local_id, admitted) for reference in references]
        checked: set[tuple[int, int]] = set()
        domains: dict[tuple[FinitePort, ...], int] = {}
        while pending:
            pair = pending.pop()
            if pair in checked:
                continue
            checked.add(pair)
            value, condition = (tx.node(identity) for identity in pair)
            functions.ledger.bump("semantic_totality_pair_visits")
            if condition.terminal is not None and not condition.terminal.value:
                continue
            terminal = value.terminal
            if terminal is not None:
                if terminal.kind == "invalid":
                    raise ValueError(
                        "complete semantic channel is undefined on an admissible input"
                    )
                for child in terminal.references:
                    child_inputs = tx.node(child).signature.inputs
                    valid = domains.get(child_inputs)
                    if valid is None:
                        signature = FunctionSignature(child_inputs, BOOL)
                        valid = totality_predicate(
                            tx,
                            tx.admissible(
                                tx.terminal(signature, SemanticTerminal("atom", 1))
                            ),
                        )
                        domains[child_inputs] = valid
                    pending.append((child, valid))
                continue
            low, high = split_semantic_pair(pair, value, condition)
            pending.extend(((low[0], low[1]), (high[0], high[1])))
    finally:
        tx.close()

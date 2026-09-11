"""Shared symbolic totality proofs for one quotient normalization."""

from __future__ import annotations

from collections.abc import Iterable

from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FinitePort,
    FunctionSignature,
    SemanticFunctionID,
    SemanticTerminal,
)
from number_compiler.arithmetic.functions.semantic_function_transactions import (
    _Transaction,
)
from number_compiler.hashlife.interfaces.semantic_structures import (
    StructureArena,
    StructureID,
)


def _predicate(tx: _Transaction, identity: int) -> int:
    signature = tx.node(identity).signature
    return tx.map_terminals(
        identity,
        signature,
        lambda leaf: tx.terminal(
            signature,
            SemanticTerminal("atom", int(leaf.kind == "atom" and leaf.value == 1)),
        ),
    )


def _require_semantic_total(
    arena: StructureArena,
    references: tuple[SemanticFunctionID, ...],
    admissible: SemanticFunctionID,
) -> None:
    """Prove several channels with one predicate and product-walk workspace."""
    if not references:
        return
    functions = arena.functions
    allowed = functions.resolve(admissible)
    inputs = functions.resolve(references[0]).signature.inputs
    if allowed.signature != FunctionSignature(inputs, BOOL) or any(
        functions.resolve(item).signature.inputs != inputs for item in references
    ):
        raise ValueError("totality requires the full Boolean admissibility interface")
    tx = _Transaction(functions)
    try:
        admitted = _predicate(tx, admissible.local_id)
        pending = [(reference.local_id, admitted) for reference in references]
        checked: set[tuple[int, int]] = set()
        domains: dict[tuple[FinitePort, ...], int] = {}
        while pending:
            pair = pending.pop()
            if pair in checked:
                continue
            checked.add(pair)
            value, condition = (tx.node(identity) for identity in pair)
            arena.ledger.bump("semantic_totality_pair_visits")
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
                        valid = _predicate(
                            tx,
                            tx.admissible(
                                tx.terminal(signature, SemanticTerminal("atom", 1))
                            ),
                        )
                        domains[child_inputs] = valid
                    pending.append((child, valid))
                continue
            variable = min(
                node.variable
                for node in (value, condition)
                if node.variable is not None
            )
            low = tuple(
                node.low if node.variable == variable else identity
                for node, identity in zip((value, condition), pair, strict=True)
            )
            high = tuple(
                node.high if node.variable == variable else identity
                for node, identity in zip((value, condition), pair, strict=True)
            )
            pending.extend(((low[0], low[1]), (high[0], high[1])))
    finally:
        tx.close()


def _require_structured_total(
    arena: StructureArena,
    references: tuple[StructureID, ...],
    admissible: SemanticFunctionID,
) -> None:
    """Walk shared structured descendants once during a normalization."""
    allowed = arena.functions.resolve(admissible)
    for reference in references:
        root = arena.resolve(reference)
        if allowed.signature != FunctionSignature(root.signature.inputs, BOOL):
            raise ValueError(
                "structured totality requires the complete admissibility interface"
            )
    pending = list(references)
    seen: set[int] = set()
    proved: set[tuple[int, tuple[FinitePort, ...]]] = set()
    while pending:
        current = pending.pop()
        if current.local_id in seen:
            continue
        seen.add(current.local_id)
        node = arena.resolve(current)
        inputs = node.signature.inputs
        proof = node.valid.local_id, inputs
        if proof not in proved:
            proved.add(proof)
            tx = _Transaction(arena.functions)
            try:
                signature = FunctionSignature(inputs, BOOL)
                predicate = _predicate(
                    tx, tx.admissible(tx.resign(admissible.local_id, signature))
                )
                pairs = [(node.valid.local_id, predicate)]
                checked: set[tuple[int, int]] = set()
                while pairs:
                    pair = pairs.pop()
                    if pair in checked:
                        continue
                    checked.add(pair)
                    value, condition = (tx.node(identity) for identity in pair)
                    arena.ledger.bump("semantic_structure_totality_pair_visits")
                    if condition.terminal is not None and not condition.terminal.value:
                        continue
                    if value.terminal is not None:
                        if value.terminal.kind != "atom" or value.terminal.value != 1:
                            raise ValueError(
                                "complete structured channel is undefined on an admissible input"
                            )
                        continue
                    variable = min(
                        item.variable
                        for item in (value, condition)
                        if item.variable is not None
                    )
                    low = tuple(
                        item.low if item.variable == variable else identity
                        for item, identity in zip((value, condition), pair, strict=True)
                    )
                    high = tuple(
                        item.high if item.variable == variable else identity
                        for item, identity in zip((value, condition), pair, strict=True)
                    )
                    pairs.extend(((low[0], low[1]), (high[0], high[1])))
            finally:
                tx.close()
        pending.extend(node.components)
        if node.body is not None:
            pending.append(node.body)


def require_total_components(
    arena: StructureArena,
    references: Iterable[SemanticFunctionID | StructureID],
    admissible: SemanticFunctionID,
) -> None:
    """Validate all unique channels in one transient normalization session."""
    unique = tuple(dict.fromkeys(references))
    semantic = tuple(item for item in unique if type(item) is SemanticFunctionID)
    structured = tuple(item for item in unique if type(item) is StructureID)
    if len(semantic) + len(structured) != len(unique):
        raise TypeError("totality validation requires canonical semantic components")
    _require_semantic_total(arena, semantic, admissible)
    _require_structured_total(arena, structured, admissible)


def require_total(
    arena: StructureArena,
    reference: StructureID,
    admissible: SemanticFunctionID,
) -> None:
    """Compatibility entry point for a single structured totality proof."""
    require_total_components(arena, (reference,), admissible)


__all__ = ["require_total", "require_total_components"]

"""Shared symbolic totality proofs for one quotient normalization."""

from __future__ import annotations

from collections.abc import Iterable

from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FinitePort,
    FunctionSignature,
    SemanticFunctionID,
)
from number_compiler.arithmetic.functions.semantic_function_transactions import (
    _Transaction,
)
from number_compiler.arithmetic.functions.semantic_totality import (
    require_semantic_total,
)
from number_compiler.arithmetic.functions.semantic_totality import (
    split_semantic_pair as _split_pair,
)
from number_compiler.arithmetic.functions.semantic_totality import (
    totality_predicate as _predicate,
)
from number_compiler.hashlife.interfaces.semantic_structures import (
    StructureArena,
    StructureID,
)


def _require_semantic_total(
    arena: StructureArena,
    references: tuple[SemanticFunctionID, ...],
    admissible: SemanticFunctionID,
) -> None:
    require_semantic_total(arena.functions, references, admissible)


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
                    low, high = _split_pair(pair, value, condition)
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

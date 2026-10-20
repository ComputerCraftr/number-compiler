"""Recognize an already masked atomic product without rewriting its decision DAG.

BitFunctionArena publishes output bits through BooleanCircuit.normalized: each bit is
masked by its valid predicate. StructureArena.atom preserves that predicate.
Applying exactly the same mask again cannot change such an atom. Root validity
alone does not establish this law for a product or a function-valued structure.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.functions.finite_function_types import (
    SemanticFunctionID,
    SemanticNode,
    SemanticTerminal,
)
from number_compiler.arithmetic.functions.semantic_function_transactions import (
    _Transaction,
)
from number_compiler.hashlife.interfaces.semantic_bits import FactoredFunctionID
from number_compiler.hashlife.interfaces.semantic_structures import StructureID
from number_compiler.resources.metric_keys import (
    hashlife_interfaces as _interfaces_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.diamond_quotient import (
        DiamondQuotientArena,
    )
    from number_compiler.hashlife.interfaces.semantic_structures import (
        MacroComponents,
        MacroInterface,
    )


def _existing_mask(
    arena: DiamondQuotientArena, root: SemanticFunctionID
) -> SemanticFunctionID | None:
    """Probe the total-mask interner; do not publish speculative semantic nodes."""
    functions = arena.functions
    functions.resolve(root)
    with _Transaction(functions) as workspace:
        workspace.reserve_workspace(entries=1)
        pending = [(root.local_id, False)]
        done: dict[int, int] = {}
        while pending:
            identity, ready = pending.pop()
            workspace.release_workspace(entries=1)
            if identity in done:
                continue
            node = functions.nodes[identity]
            arena.ledger.bump(_interfaces_keys.QUOTIENT_ATOMIC_MASK_VALIDATION_NODES)
            if node.terminal is not None:
                leaf = node.terminal
                normalized = SemanticNode(
                    node.signature,
                    terminal=SemanticTerminal(
                        "atom", int(leaf.kind == "atom" and leaf.value == 1)
                    ),
                )
                found = functions.keys.get(normalized)
            elif ready:
                low, high = done[node.low], done[node.high]
                found = (
                    low
                    if low == high
                    else functions.keys.get(
                        SemanticNode(node.signature, node.variable, low, high)
                    )
                )
            else:
                workspace.reserve_workspace(entries=3)
                pending.extend(
                    ((identity, True), (node.high, False), (node.low, False))
                )
                continue
            if found is None:
                return None
            workspace.reserve_workspace(entries=1)
            done[identity] = found
        return functions.scoped_handle(done[root.local_id])


def atomic_product_is_masked(
    arena: DiamondQuotientArena,
    interface: MacroInterface,
    components: MacroComponents,
) -> bool:
    """Require the canonical atomic constructor and this exact validity domain."""
    if not all(type(component) is StructureID for component in components.functions()):
        return False
    # Interface predicates use invalid terminals outside encoded port domains;
    # factored bits instead use a total false mask there. Probe that canonical
    # mask without publishing anything before the enclosing atomic reservation.
    predicate = _existing_mask(arena, interface.admissible)
    if predicate is None:
        return False
    for component in components.functions():
        assert type(component) is StructureID
        node = arena.structures.resolve(component)
        if (
            node.kind != "atom"
            or node.valid != predicate
            or type(node.atom) is not FactoredFunctionID
        ):
            return False
        value = arena.structures.bits.resolve(node.atom)
        if value.signature != node.signature or value.valid != node.valid:
            return False
    return True


__all__ = ["atomic_product_is_masked"]

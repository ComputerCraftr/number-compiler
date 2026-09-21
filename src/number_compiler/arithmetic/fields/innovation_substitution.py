"""Private charged worklist for the symbolic innovation arena's pullback.

No independent arena, scheduler, source authority or publication owner lives here.
"""

from __future__ import annotations

from collections.abc import Mapping, Sequence

from number_compiler.arithmetic.fields.symbolic_innovation import (
    InnovationID,
    SymbolicInnovationArena,
    _Add,
    _Atom,
    _Charted,
    _Radial,
    _Scale,
)
from number_compiler.resources.ledger import OwnedMemo


def substitute_innovations(
    arena: SymbolicInnovationArena,
    roots: Sequence[InnovationID],
    replacements: Mapping[InnovationID, InnovationID],
) -> tuple[InnovationID, ...]:
    """Run simultaneous substitution using only the caller's arithmetic owner."""
    arena._check_open()
    arena.ledger.bump("symbolic_innovation_pullback_attempts")
    for root in roots:
        arena.ledger.bump("symbolic_innovation_pullback_root_checks")
        arena.resolve(root)
    for atom, replacement in replacements.items():
        arena.ledger.bump("symbolic_innovation_pullback_binding_checks")
        if not isinstance(arena.resolve(atom), _Atom):
            raise TypeError("innovation substitution keys must be primitive atoms")
        arena.resolve(replacement)
    prefix = f"innovation-pullback-{arena.ledger.owner_count}"
    environment = OwnedMemo[InnovationID, InnovationID](
        arena.ledger,
        arena.ledger.register(prefix + "-environment", "query_memo"),
        nodes_per_entry=2,
    )
    memo = OwnedMemo[InnovationID, InnovationID](
        arena.ledger,
        arena.ledger.register(prefix + "-memo", "query_memo"),
        nodes_per_entry=2,
    )
    frames = OwnedMemo[int, tuple[InnovationID, bool]](
        arena.ledger,
        arena.ledger.register(prefix + "-frames", "query_memo"),
        nodes_per_entry=3,
    )
    try:
        for atom, replacement in replacements.items():
            environment[atom] = replacement
        for root in roots:
            frames[len(frames)] = (root, False)
            while frames:
                index = len(frames) - 1
                reference, ready = frames[index]
                del frames[index]
                arena.ledger.bump("symbolic_innovation_pullback_frames")
                if reference in memo:
                    arena.ledger.bump("symbolic_innovation_pullback_hits")
                    continue
                node = arena.resolve(reference)
                children: tuple[InnovationID, ...]
                if isinstance(node, (_Radial, _Charted, _Scale)):
                    children = (node.child,)
                elif isinstance(node, _Add):
                    children = (node.left, node.right)
                else:
                    children = ()
                if children and not ready:
                    frames[len(frames)] = (reference, True)
                    for child in reversed(children):
                        frames[len(frames)] = (child, False)
                    continue
                if isinstance(node, _Atom):
                    result = environment.get(reference, reference)
                elif isinstance(node, _Radial):
                    result = arena.radial(memo[node.child], node.multiplier)
                elif isinstance(node, _Charted):
                    result = arena.chart(memo[node.child], node.chart)
                elif isinstance(node, _Scale):
                    result = arena._scale(memo[node.child], node.coefficient)
                elif isinstance(node, _Add):
                    result = arena.add(memo[node.left], memo[node.right])
                else:
                    result = reference
                memo[reference] = result
                arena.ledger.bump("symbolic_innovation_pullback_nodes")
        # Charge the outgoing collection while materializing it; retained
        # ownership belongs to the caller, just as for existing projections.
        arena.ledger.reserve(memo.owner, nodes=len(roots))
        try:
            return tuple(memo[root] for root in roots)
        finally:
            arena.ledger.release(memo.owner, nodes=len(roots))
    finally:
        frames.dispose()
        memo.dispose()
        environment.dispose()

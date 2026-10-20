"""Private charged worklist for the symbolic innovation arena's pullback.

No independent arena, scheduler, source authority or publication owner lives here.
"""

from __future__ import annotations

from collections.abc import Mapping, Sequence

from number_compiler.arithmetic.fields.radial_innovation import (
    InnovationAdd,
    InnovationAtom,
    InnovationCharted,
    InnovationID,
    InnovationRadial,
    InnovationScale,
)
from number_compiler.arithmetic.fields.symbolic_innovation import (
    SymbolicInnovationArena,
)
from number_compiler.resources.ledger import OwnedMemo
from number_compiler.resources.metric_keys import (
    arithmetic_fields as _fields_keys,
)


def substitute_innovations(
    arena: SymbolicInnovationArena,
    roots: Sequence[InnovationID],
    replacements: Mapping[InnovationID, InnovationID],
    *,
    parity: bool = False,
) -> tuple[InnovationID, ...]:
    """Run simultaneous substitution using only the caller's arithmetic owner."""
    arena.check_open()
    arena.ledger.bump(_fields_keys.SYMBOLIC_INNOVATION_PULLBACK_ATTEMPTS)
    for root in roots:
        arena.ledger.bump(_fields_keys.SYMBOLIC_INNOVATION_PULLBACK_ROOT_CHECKS)
        arena.resolve(root)
    for atom, replacement in replacements.items():
        arena.ledger.bump(_fields_keys.SYMBOLIC_INNOVATION_PULLBACK_BINDING_CHECKS)
        if not isinstance(arena.resolve(atom), InnovationAtom):
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
                arena.ledger.bump(_fields_keys.SYMBOLIC_INNOVATION_PULLBACK_FRAMES)
                if reference in memo:
                    arena.ledger.bump(_fields_keys.SYMBOLIC_INNOVATION_PULLBACK_HITS)
                    continue
                node = arena.resolve(reference)
                if parity and (
                    isinstance(node, InnovationRadial)
                    and node.multiplier.no_growth > 0
                    or isinstance(node, InnovationScale)
                    and node.coefficient % 2 == 0
                ):
                    # Do not enter the old source or forcing subtree. This
                    # changes only the demanded parity view, never exact data.
                    memo[reference] = arena.zero
                    arena.ledger.bump(_fields_keys.SYMBOLIC_INNOVATION_PARITY_PRUNED)
                    arena.ledger.bump(_fields_keys.SYMBOLIC_INNOVATION_PULLBACK_NODES)
                    continue
                children: tuple[InnovationID, ...]
                if isinstance(
                    node, (InnovationRadial, InnovationCharted, InnovationScale)
                ):
                    children = (node.child,)
                elif isinstance(node, InnovationAdd):
                    children = (node.left, node.right)
                else:
                    children = ()
                if children and not ready:
                    frames[len(frames)] = (reference, True)
                    for child in reversed(children):
                        frames[len(frames)] = (child, False)
                    continue
                if isinstance(node, InnovationAtom):
                    result = environment.get(reference, reference)
                elif isinstance(node, InnovationRadial):
                    result = arena.radial(memo[node.child], node.multiplier)
                elif isinstance(node, InnovationCharted):
                    result = arena.chart(memo[node.child], node.chart)
                elif isinstance(node, InnovationScale):
                    result = (
                        memo[node.child]
                        if parity
                        else arena.scale(memo[node.child], node.coefficient)
                    )
                elif isinstance(node, InnovationAdd):
                    left, right = memo[node.left], memo[node.right]
                    result = (
                        arena.zero
                        if parity and left == right
                        else arena.add(left, right)
                    )
                else:
                    result = reference
                memo[reference] = result
                arena.ledger.bump(_fields_keys.SYMBOLIC_INNOVATION_PULLBACK_NODES)
        # Charge the outgoing collection while materializing it; retained
        # ownership belongs to the caller, just as for existing projections.
        with arena.ledger.reservation(memo.owner, nodes=len(roots)):
            return tuple(memo[root] for root in roots)
    finally:
        frames.dispose()
        memo.dispose()
        environment.dispose()

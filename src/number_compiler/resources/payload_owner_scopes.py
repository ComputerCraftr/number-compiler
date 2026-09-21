"""Exact live-arena owner scopes used by the payload admission audit."""

from __future__ import annotations

from collections.abc import Iterable
from typing import cast

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken


def field_owner_scopes(
    execution_roots: Iterable[object],
) -> tuple[set[ArenaToken], set[ArenaToken]]:
    from number_compiler.hashlife.execution.recursive_outputs import (
        RecursiveCoordinateMorphismArena,
    )
    from number_compiler.hashlife.interfaces.semantic_interfaces import (
        SemanticCoordinateOutputArena,
    )
    from number_compiler.sequences.collatz.field_action import CollatzFieldActionArena

    action_owners: set[ArenaToken] = set()
    output_owners: set[ArenaToken] = set()
    for root in execution_roots:
        if type(root) is CollatzFieldActionArena:
            collatz_actions = root
            action_owners.add(collatz_actions.owner)
            output_owners.add(collatz_actions.output_owner)
        elif type(root) in (
            RecursiveCoordinateMorphismArena,
            SemanticCoordinateOutputArena,
        ):
            output_owners.add(
                cast(
                    RecursiveCoordinateMorphismArena | SemanticCoordinateOutputArena,
                    root,
                ).owner
            )
    return action_owners, output_owners

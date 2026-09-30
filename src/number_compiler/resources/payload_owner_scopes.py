"""Exact live-arena owner scopes used by the payload admission audit."""

from __future__ import annotations

from collections.abc import Iterable
from typing import cast

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken


def field_owner_scopes(
    execution_roots: Iterable[object],
) -> tuple[set[ArenaToken], set[ArenaToken]]:
    roots = tuple(execution_roots)
    from number_compiler.hashlife.execution.recursive_outputs import (
        RecursiveCoordinateMorphismArena,
    )
    from number_compiler.hashlife.interfaces.semantic_interfaces import (
        SemanticCoordinateOutputArena,
    )
    from number_compiler.sequences.collatz.field_action import CollatzFieldActionArena

    reverse_action_types: tuple[type[object], ...] = ()
    reverse_output_types: tuple[type[object], ...] = ()
    if any(
        type(root).__module__
        in (
            "number_compiler.sequences.reverse_add.coordinate_program",
            "number_compiler.sequences.reverse_add.field_action",
        )
        for root in roots
    ):
        from number_compiler.sequences.reverse_add.coordinate_program import (
            ReverseCoordinateProgramArena,
        )
        from number_compiler.sequences.reverse_add.field_action import (
            ReverseFieldActionArena,
        )

        reverse_action_types = (ReverseFieldActionArena,)
        reverse_output_types = (
            ReverseCoordinateProgramArena,
            ReverseFieldActionArena,
        )

    action_owners: set[ArenaToken] = set()
    output_owners: set[ArenaToken] = set()
    for root in roots:
        if type(root) is CollatzFieldActionArena:
            collatz_actions = root
            action_owners.add(collatz_actions.owner)
            output_owners.add(collatz_actions.output_owner)
        elif type(root) in reverse_action_types:
            reverse_action = cast(ReverseFieldActionArena, root)
            action_owners.add(reverse_action.owner)
            output_owners.add(reverse_action.output_owner)
        elif type(root) in reverse_output_types:
            reverse_output = cast(
                ReverseCoordinateProgramArena | ReverseFieldActionArena,
                root,
            )
            output_owners.add(reverse_output.owner)
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

"""Exact live-arena owner scopes used by the payload admission audit."""

from __future__ import annotations

from collections.abc import Iterable
from typing import cast

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_contracts import PayloadAuditContractAudit


def field_owner_scopes(
    execution_roots: Iterable[object],
    contracts: PayloadAuditContractAudit,
    ledger: ResourceLedger,
) -> tuple[set[ArenaToken], set[ArenaToken]]:
    roots = tuple(execution_roots)
    from number_compiler.hashlife.execution.recursive_outputs import (
        RecursiveCoordinateMorphismArena,
    )
    from number_compiler.hashlife.interfaces.semantic_interfaces import (
        SemanticCoordinateOutputArena,
    )

    action_owners: set[ArenaToken] = set()
    output_owners: set[ArenaToken] = set()
    for root in roots:
        module = type(root).__module__
        is_collatz_action_owner = contracts.owns_root("collatz", root, ledger=ledger)
        is_reverse_action_owner = (
            module == "number_compiler.sequences.reverse_add.field_action"
            and contracts.owns_root("reverse_add", root, ledger=ledger)
        )
        if is_collatz_action_owner or is_reverse_action_owner:
            action_owner = getattr(root, "owner", None)
            output_owner = getattr(root, "output_owner", None)
            if type(action_owner) is ArenaToken and type(output_owner) is ArenaToken:
                action_owners.add(action_owner)
                output_owners.add(output_owner)
        elif (
            module == "number_compiler.sequences.reverse_add.coordinate_program"
            and contracts.owns_root("reverse_add", root, ledger=ledger)
        ):
            output_owner = getattr(root, "owner", None)
            if type(output_owner) is ArenaToken:
                output_owners.add(output_owner)
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

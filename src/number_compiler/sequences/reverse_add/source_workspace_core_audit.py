"""Read-only resource-shape validation for reverse source-image cores."""

from __future__ import annotations

from collections.abc import Mapping

from number_compiler.resources.ledger import ResourceInventory, ResourceLedger


def source_image_core_storage_valid(
    ledger: ResourceLedger,
    containers: Mapping[int, object],
    inventory: Mapping[int, ResourceInventory],
    state: object,
) -> bool:
    """Check every retained core store against its exact ledger owner."""
    from number_compiler.hashlife.execution.source_bound_image_audit import (
        SourceBoundSchedulerCoreAuditSnapshot,
    )

    if type(state) is not SourceBoundSchedulerCoreAuditSnapshot:
        return False
    try:
        from number_compiler.hashlife.execution.source_image_seals import (
            PublicationSeal,
        )

        image_seals = tuple(state.image_seals)
        projection_seals = tuple(state.projection_seals.values())
        if any(
            type(seal) is not PublicationSeal
            for seal in (*image_seals, *projection_seals)
        ):
            return False
        expected = (
            (
                state.node_owner,
                state.node_store,
                "source_image",
                len(state.nodes),
                len(state.nodes),
            ),
            (
                state.adapter_owner,
                state.adapter_store,
                "source_image_adapter",
                len(state.adapters),
                0,
            ),
            (
                state.origin_owner,
                state.origin_store,
                "source_image_origin",
                len(state.origins),
                0,
            ),
            (
                state.application_owner,
                state.application_store,
                "source_image_application",
                len(state.applications),
                0,
            ),
            (
                state.relative_owner,
                state.relative_store,
                "source_image_relative_transfer",
                len(state.relative),
                0,
            ),
            (
                state.projection_owner,
                state.projection_store,
                "source_image_projection",
                len(state.projections),
                len(state.projections),
            ),
            (
                state.image_seal_owner,
                state.image_seal_store,
                "source_image_publication_seal",
                len(image_seals),
                sum(seal.retained_nodes for seal in image_seals),
            ),
            (
                state.projection_seal_owner,
                state.projection_seal_store,
                "source_image_publication_seal",
                len(projection_seals),
                sum(seal.retained_nodes for seal in projection_seals),
            ),
        )
    except (AttributeError, IndexError, KeyError, TypeError, ValueError):
        return False
    for owner, store, role, entries, nodes in expected:
        if type(owner) is not int:
            return False
        try:
            account: object = (
                inventory[owner]
                if owner in inventory
                else ledger.inventory_owner(owner)
            )
        except (IndexError, KeyError, RuntimeError, TypeError, ValueError):
            return False
        if (
            type(account) is not ResourceInventory
            or account.role != role
            or account.disposed
            or not account.payloads_registered
            or account.entries != entries
            or account.nodes != nodes
            or (owner in containers and containers[owner] is not store)
        ):
            return False
        try:
            if ledger.registered_container(owner) is not store:
                return False
        except (IndexError, RuntimeError, TypeError, ValueError):
            return False
    return True


__all__ = ["source_image_core_storage_valid"]

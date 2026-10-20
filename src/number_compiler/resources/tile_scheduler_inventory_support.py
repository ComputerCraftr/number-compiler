"""Small independent checks shared by tile scheduler inventory traversal."""

from __future__ import annotations

from collections.abc import Mapping

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundSchedulerCore,
)
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler

CAUSAL_FRAME_OPS = frozenset(
    (
        "memo_done",
        "point",
        "advance",
        "emit",
        "advance_symbol",
        "anchor",
        "residual",
        "output",
        "output_boundary",
        "scan_chunks",
        "output_chunk_list",
        "interface",
        "reverse_interface",
        "exact_reverse_output",
        "reverse_boundary",
        "source_root_match",
        "interface_emit",
        "child_states",
    )
)


def valid_source_only_scheduler(
    scheduler: TileScheduler,
    ledger: object,
    containers: Mapping[int, object],
    roots: tuple[object, ...],
) -> tuple[bool, SourceBoundSchedulerCore | None]:
    """Validate the exact minimal facade and its optional live core owner."""
    core = scheduler.published_source_image_core
    snapshot = core.audit_snapshot() if core is not None else None
    valid = (
        set(vars(scheduler)) == {"_source_only", "ledger", "_source_images"}
        and scheduler.is_source_only
        and scheduler.ledger is ledger
        and (
            core is None
            or (
                type(core) is SourceBoundSchedulerCore
                and core in roots
                and core.ledger is ledger
                and snapshot is not None
                and not snapshot.closed
                and type(core.owner) is ArenaToken
                and containers.get(snapshot.adapter_owner) is snapshot.adapter_store
                and containers.get(snapshot.node_owner) is snapshot.node_store
                and containers.get(snapshot.origin_owner) is snapshot.origin_store
                and containers.get(snapshot.application_owner)
                is snapshot.application_store
                and containers.get(snapshot.relative_owner) is snapshot.relative_store
                and containers.get(snapshot.projection_owner)
                is snapshot.projection_store
                and containers.get(snapshot.workspace.owner)
                is snapshot.workspace.store_identity
                and not snapshot.workspace.running
                and snapshot.workspace.frame_count == 0
                and snapshot.workspace.value_count == 0
                and containers.get(snapshot.image_seal_owner)
                is snapshot.image_seal_store
                and containers.get(snapshot.projection_seal_owner)
                is snapshot.projection_seal_store
                and all(
                    adapter.ledger is ledger
                    and key == (adapter.family, adapter.semantic_version)
                    for key, adapter in snapshot.adapters.items()
                )
            )
        )
    )
    return valid, core


__all__ = ["CAUSAL_FRAME_OPS", "valid_source_only_scheduler"]

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
    core = scheduler._source_images
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
                and not core._closed
                and type(core.owner) is ArenaToken
                and containers.get(core._adapter_owner) is core._adapters
                and containers.get(core._node_owner) is core._nodes
                and containers.get(core._origin_owner) is core._origins
                and containers.get(core._apply_owner) is core._applications
                and containers.get(core._relative_owner) is core._relative
                and containers.get(core._projection_owner) is core._projections
                and containers.get(core._workspace_owner) is core._workspace._storage
                and not core._workspace.running
                and not len(core._workspace)
                and containers.get(core._publication_seals._image_owner)
                is core._publication_seals.images
                and containers.get(core._publication_seals._projection_owner)
                is core._publication_seals.projections
                and all(
                    adapter.ledger is ledger
                    and key == (adapter.family, adapter.semantic_version)
                    for key, adapter in core._adapters.items()
                )
            )
        )
    )
    return valid, core


__all__ = ["CAUSAL_FRAME_OPS", "valid_source_only_scheduler"]

"""Demanded causal observations over output-independent interface payloads."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Protocol

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.tile_causal_interfaces import (
    CausalInterfacePayload,
)
from number_compiler.hashlife.tiles.tiles import TileArena, TileID
from number_compiler.resources.causal_types import CausalChildStates, CausalState
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)


class CausalObservationEngine(Protocol):
    """Narrow transient API supplied by the iterative causal task engine."""

    tiles: TileArena
    ledger: ResourceLedger

    def interface(
        self,
        action: FieldCellActionID,
        tile: TileID,
        left: CausalState,
        right: CausalState,
    ) -> CausalInterfacePayload: ...

    def child_states(
        self,
        action: FieldCellActionID,
        parent: TileID,
        left: CausalState,
        right: CausalState,
    ) -> CausalChildStates: ...


@dataclass(frozen=True, slots=True)
class _WidthFrame:
    origin: int
    tile: TileID
    left: CausalState
    right: CausalState


def causal_width(
    engine: CausalObservationEngine,
    action: FieldCellActionID,
    tile: TileID,
    left: CausalState,
    right: CausalState,
    *,
    limit: int,
) -> int:
    """Find the rightmost active output through bounded interface descent.

    Fully covered siblings are skipped from their activity function.  A clipped
    branch descends until its covered children can be queried, so activity
    outside ``limit`` cannot affect the answer.  No scalar point loop or exact
    final-output tile participates in this operation.
    """
    if not isinstance(engine.tiles, TileArena) or not isinstance(
        engine.ledger, ResourceLedger
    ):
        raise TypeError("causal width requires the shared tile runtime")
    if type(action) is not FieldCellActionID:
        raise TypeError("causal width requires a scoped field action")
    root = engine.tiles.resolve(tile)
    if type(limit) is not int:
        raise TypeError("causal width limit requires an exact integer")
    if not 0 <= limit <= root.width:
        raise ValueError("causal width limit lies outside its source tile")
    if not limit:
        return 0

    pending = [_WidthFrame(0, tile, left, right)]
    engine.ledger.bump(_execution_keys.TILE_CAUSAL_WIDTH_REQUESTS)
    while pending:
        previous = engine.ledger.counters.get(
            _execution_keys.TILE_CAUSAL_WIDTH_WORKSPACE_PEAK, 0
        )
        if len(pending) > previous:
            engine.ledger.bump(
                _execution_keys.TILE_CAUSAL_WIDTH_WORKSPACE_PEAK,
                len(pending) - previous,
            )
        frame = pending.pop()
        node = engine.tiles.resolve(frame.tile)
        engine.ledger.bump(_execution_keys.TILE_CAUSAL_WIDTH_DESCENTS)
        if frame.origin >= limit:
            continue
        covered = frame.origin + node.width <= limit
        if covered:
            payload = engine.interface(
                action,
                frame.tile,
                frame.left,
                frame.right,
            )
            if type(payload) is not CausalInterfacePayload:
                raise TypeError("causal interface task returned another payload sort")
            payload.__post_init__()
            if payload.level != node.level:
                raise ValueError("causal interface task returned another spatial level")
            if not payload.active:
                continue
        if not node.level:
            return frame.origin + 1
        if node.left is None or node.right is None:
            raise ValueError("causal width encountered a malformed tile parent")
        contexts = engine.child_states(
            action,
            frame.tile,
            frame.left,
            frame.right,
        )
        left_context, right_context = contexts
        half = node.width // 2
        # LIFO: queue left first so the rightmost admissible child is inspected
        # first and the first active leaf is the exact width.
        pending.append(
            _WidthFrame(
                frame.origin,
                node.left,
                left_context[0],
                left_context[1],
            )
        )
        pending.append(
            _WidthFrame(
                frame.origin + half,
                node.right,
                right_context[0],
                right_context[1],
            )
        )
    return 0


__all__ = ["CausalObservationEngine", "causal_width"]

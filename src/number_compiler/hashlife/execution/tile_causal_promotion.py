"""Opportunistic exact-parent publication for completed causal children.

The causal point recurrence can complete the two spatial children of a
temporal midpoint in separate observations.  This task joins those already
completed results without requesting either child and publishes the ordinary
completed parent.  A missing child is a no-op; no partial image is retained.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.execution.causal_frames import (
    AnchorFrame,
    CausalTaskFrame,
    ChildStatesFrame,
    PromoteMidpointFrame,
)
from number_compiler.hashlife.execution.tile_causal_results import (
    lookup_causal_result,
    publish_causal_completed,
)
from number_compiler.hashlife.execution.tile_causal_tasks import (
    combine_spatial_outputs,
    result_payload,
)
from number_compiler.resources.causal_stacks import CausalFrameStack, CausalResults
from number_compiler.resources.causal_types import (
    CausalPrefix,
    CausalTaskValue,
    pop_causal_state,
    pop_child_states,
)
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_causal import CausalTileEngine


def promotion_step(
    engine: CausalTileEngine,
    frame: PromoteMidpointFrame,
    frames: CausalFrameStack[CausalTaskFrame],
    values: CausalResults[CausalTaskValue],
) -> bool:
    """Publish a temporal midpoint parent when both exact children exist."""
    action, tile, left, right = frame.args
    children = engine._children(action)
    if engine._application is None or children is None:
        values.append(False)
        return True
    before, _after = children
    # Primitive parents are already completed directly.  Promotion targets
    # the composite midpoint whose spatial children arrived independently.
    if engine._children(before) is None:
        values.append(False)
        return True
    node = engine.tiles.resolve(tile)
    if not node.level or node.left is None or node.right is None:
        values.append(False)
        return True
    match (left, right):
        case (CausalPrefix(), CausalPrefix()):
            pass
        case _:
            raise ValueError("midpoint promotion requires exact causal prefixes")
    if frame.stage == 0:
        from number_compiler.hashlife.tiles.result_reverse_indexes import (
            _has_completed_result_input,
        )

        # A retained exact parent is reusable even after either child is
        # independently evicted.  Without a parent candidate, promotion cannot
        # succeed unless both spatial children have some completed producer
        # result. Reject only that impossible cold case before constructing
        # temporal anchors or half-parent contexts. A positive answer grants no
        # authority: the exact keyed lookups below validate the full requests.
        parent_present = _has_completed_result_input(
            engine.scheduler.results, before, tile
        )
        if not parent_present and (
            not _has_completed_result_input(engine.scheduler.results, before, node.left)
            or not _has_completed_result_input(
                engine.scheduler.results, before, node.right
            )
        ):
            engine.ledger.bump(
                _execution_keys.TILE_CAUSAL_PARENT_PROMOTION_PREFLIGHT_MISSES
            )
            values.append(False)
            return True
        frame.stage = 1
        frames.extend(
            (
                frame,
                AnchorFrame((before, 1, right)),
                AnchorFrame((before, 0, left)),
            )
        )
        return True
    if frame.stage == 1:
        right_anchor = pop_causal_state(values)
        left_anchor = pop_causal_state(values)
        parent_key = engine._composite_key(
            before,
            tile,
            left_anchor,
            right_anchor,
        )
        if parent_key is None:
            values.append(False)
            return True
        completed = lookup_causal_result(
            engine.scheduler.results,
            parent_key,
            action_admission=engine.action_admission,
        )
        if completed is not None:
            engine.scheduler._pin_causal(
                engine._application,
                parent_key,
                completed,
            )
            engine.ledger.bump(_execution_keys.TILE_CAUSAL_PARENT_PROMOTION_HITS)
            values.append(True)
            return True
        frame.stage = 2
        frame.saved = (parent_key, node.left, node.right)
        frames.extend(
            (
                frame,
                ChildStatesFrame(
                    (before, tile, left_anchor, right_anchor),
                ),
            )
        )
        return True

    child_contexts = pop_child_states(values)
    match frame.saved:
        case (parent_key, left_tile, right_tile):
            pass
        case _:
            raise AssertionError("midpoint promotion lost its parent references")
    left_context, right_context = child_contexts
    left_key = engine._composite_key(before, left_tile, *left_context)
    right_key = engine._composite_key(before, right_tile, *right_context)
    if left_key is None or right_key is None:
        values.append(False)
        return True
    left_result = lookup_causal_result(
        engine.scheduler.results,
        left_key,
        action_admission=engine.action_admission,
    )
    right_result = lookup_causal_result(
        engine.scheduler.results,
        right_key,
        action_admission=engine.action_admission,
    )
    if left_result is None or right_result is None:
        if left_result is not None:
            left_result.close()
        if right_result is not None:
            right_result.close()
        engine.ledger.bump(_execution_keys.TILE_CAUSAL_PARENT_PROMOTION_MISSES)
        values.append(False)
        return True
    try:
        left_output = result_payload(engine.tiles, left_result)
        right_output = result_payload(engine.tiles, right_result)
        payload = combine_spatial_outputs(engine, before, left_output, right_output)
        published = publish_causal_completed(
            engine.scheduler.results,
            parent_key,
            payload,
        )
        engine.scheduler._pin_causal(
            engine._application,
            parent_key,
            published,
        )
    finally:
        left_result.close()
        right_result.close()
    engine.ledger.bump(_execution_keys.TILE_CAUSAL_PARENT_PROMOTIONS)
    values.append(True)
    return True


__all__ = ["promotion_step"]

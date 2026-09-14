"""Opportunistic exact-parent publication for completed causal children.

The causal point recurrence can complete the two spatial children of a
temporal midpoint in separate observations.  This task joins those already
completed results without requesting either child and publishes the ordinary
completed parent.  A missing child is a no-op; no partial image is retained.
"""

from __future__ import annotations

from typing import Any

from number_compiler.hashlife.execution.tile_causal_results import (
    combine_causal_outputs,
    lookup_causal_result,
    publish_causal_completed,
)
from number_compiler.hashlife.execution.tile_causal_tasks import (
    CausalFrame,
    CausalPrefix,
    producer_parent,
    result_payload,
)
from number_compiler.resources.causal_workspace import CausalResults


def promotion_step(
    engine: Any,
    frame: CausalFrame,
    frames: Any,
    values: CausalResults,
) -> bool:
    """Publish a temporal midpoint parent when both exact children exist."""
    if frame.op != "promote_midpoint":
        return False
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
    match (left, right):
        case (CausalPrefix(), CausalPrefix()):
            pass
        case _:
            raise ValueError("midpoint promotion requires exact causal prefixes")
    if frame.stage == 0:
        frame.stage = 1
        frames.extend(
            (
                frame,
                CausalFrame("anchor", (before, 1, right)),
                CausalFrame("anchor", (before, 0, left)),
            )
        )
        return True
    if frame.stage == 1:
        right_anchor, left_anchor = values.pop(), values.pop()
        parent_key = engine._composite_key(
            before,
            tile,
            left_anchor,
            right_anchor,
        )
        if parent_key is None:
            values.append(False)
            return True
        completed = lookup_causal_result(engine.scheduler.results, parent_key)
        if completed is not None:
            engine.scheduler._pin_causal(
                engine._application,
                parent_key,
                completed,
            )
            engine.ledger.bump("tile_causal_parent_promotion_hits")
            values.append(True)
            return True
        node = engine.tiles.resolve(tile)
        if not node.level or node.left is None or node.right is None:
            values.append(False)
            return True
        frame.stage = 2
        frame.saved = (parent_key, node.left, node.right)
        frames.extend(
            (
                frame,
                CausalFrame(
                    "child_states",
                    (before, tile, left_anchor, right_anchor),
                ),
            )
        )
        return True

    child_contexts = values.pop()
    parent_key, left_tile, right_tile = frame.saved
    if type(child_contexts) is not tuple or len(child_contexts) != 2:
        raise TypeError("midpoint promotion received malformed child contexts")
    left_context, right_context = child_contexts
    if (
        type(left_context) is not tuple
        or len(left_context) != 2
        or type(right_context) is not tuple
        or len(right_context) != 2
    ):
        raise TypeError("midpoint promotion requires two exact child contexts")
    left_key = engine._composite_key(before, left_tile, *left_context)
    right_key = engine._composite_key(before, right_tile, *right_context)
    if left_key is None or right_key is None:
        values.append(False)
        return True
    left_result = lookup_causal_result(engine.scheduler.results, left_key)
    right_result = lookup_causal_result(engine.scheduler.results, right_key)
    if left_result is None or right_result is None:
        if left_result is not None:
            left_result.close()
        if right_result is not None:
            right_result.close()
        engine.ledger.bump("tile_causal_parent_promotion_misses")
        values.append(False)
        return True
    try:
        left_output = result_payload(engine.tiles, left_result)
        right_output = result_payload(engine.tiles, right_result)
        producer_output = producer_parent(
            engine.tiles,
            engine._leases,
            left_output,
            right_output,
        )
        joined = engine.tiles.join(left_output.output, right_output.output)
        engine._leases.append(joined)
        payload = combine_causal_outputs(
            engine.scheduler.results,
            before,
            joined.tile,
            left_output,
            right_output,
            engine.adapter.wiring(before),
            producer_output=producer_output,
        )
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
    engine.ledger.bump("tile_causal_parent_promotions")
    values.append(True)
    return True


__all__ = ["promotion_step"]

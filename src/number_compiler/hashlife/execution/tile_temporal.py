"""Iterative completed-midpoint temporal composition.

This helper is the canonical full-output milestone. It shares the scheduler's
single result arena and never stores a generation index, trajectory, flat word,
or temporal itinerary. Demand-driven point and width paths do not call it.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.tiles.tile_context import (
    ChildContext,
    after_context,
    before_context,
    temporal_result,
)
from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
from number_compiler.hashlife.tiles.tile_results import ResultLease
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler


@dataclass(slots=True)
class _Frame:
    key: PoweredResultKey
    stage: int = 0
    children: tuple[FieldCellActionID, FieldCellActionID] | None = None
    before: ResultLease | None = None


def complete_temporal(
    scheduler: TileScheduler,
    root: PoweredResultKey,
) -> ResultLease:
    """Complete a checked-miss composite through canonical midpoint tiles."""
    if scheduler.adapter.action_children(root.action) is None:
        raise ValueError("completed-midpoint execution requires a composite action")
    frames: list[_Frame] = [_Frame(root)]
    values: list[ResultLease] = []
    owned: dict[int, ResultLease] = {}

    def own(value: ResultLease) -> ResultLease:
        owned[id(value)] = value
        return value

    def close(value: ResultLease) -> None:
        held = owned.pop(id(value), None)
        if held is not None:
            held.close()

    try:
        while frames:
            frame = frames.pop()
            key = frame.key
            found = scheduler.lookup_execution_key(key)
            scheduler.ledger.bump(_execution_keys.TILE_TEMPORAL_COMPLETE_FRAMES)
            if found is not None:
                values.append(own(found))
                continue
            if frame.stage == 0:
                children = scheduler.adapter.action_children(key.action)
                if children is None:
                    values.append(
                        own(
                            scheduler.complete_direct(
                                key,
                                checked_miss=True,
                            )
                        )
                    )
                    continue
                before, after = children
                scheduler.adapter.validate_action(before)
                scheduler.adapter.validate_action(after)
                context = before_context(scheduler, key, before)
                if type(context) is not ChildContext:
                    raise TypeError("temporal prefix returned another context")
                frame.stage, frame.children = 1, children
                frames.append(frame)
                frames.append(
                    _Frame(
                        PoweredResultKey(
                            before,
                            key.input,
                            context.ports,
                            context.wiring,
                            context.boundaries,
                        )
                    )
                )
                continue
            if frame.stage == 1:
                if frame.children is None or not values:
                    raise AssertionError("temporal prefix frame lost its result")
                before_result = values.pop()
                after = frame.children[1]
                context = after_context(scheduler, key, after, before_result.result)
                if type(context) is not ChildContext:
                    raise TypeError("temporal suffix returned another context")
                frame.stage, frame.before = 2, before_result
                frames.append(frame)
                frames.append(
                    _Frame(
                        PoweredResultKey(
                            after,
                            before_result.output,
                            context.ports,
                            context.wiring,
                            context.boundaries,
                        )
                    )
                )
                continue
            parent_before = frame.before
            if parent_before is None or frame.children is None or not values:
                raise AssertionError("temporal parent lost a completed child")
            after_result = values.pop()
            try:
                result = scheduler.results.publish(
                    key,
                    temporal_result(
                        scheduler, key, parent_before.result, after_result.result
                    ),
                )
                values.append(own(result))
                scheduler.ledger.bump(
                    _execution_keys.TILE_TEMPORAL_COMPLETE_COMPOSITIONS
                )
            finally:
                close(parent_before)
                close(after_result)
        if len(values) != 1:
            raise AssertionError("temporal executor produced another result arity")
        result = values.pop()
        owned.pop(id(result))
        return result
    except BaseException:
        for value in tuple(owned.values()):
            value.close()
        owned.clear()
        raise


__all__ = ["complete_temporal"]

"""Completed clock actions admitted before generic causal execution."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
from number_compiler.hashlife.tiles.tile_results import ResultLease
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler


def complete_clock(
    scheduler: TileScheduler, key: PoweredResultKey, *, whole_output: bool = True
) -> ResultLease | None:
    """Try certified clock sectors after the caller admits the full key.

    A declined sector supplies no result. Successful sectors publish through
    the same result arena and retain the request's occurrence and context.
    Point and width demands keep their lazy first-root coordinate pullback;
    only whole-output demands construct the two primitive root-event fields.
    """
    scheduler.ledger.bump(_execution_keys.TILE_CLOCK_COMPLETION_REQUESTS)
    hooks = scheduler.adapter.family_hooks
    result = (
        None
        if hooks is None
        else hooks.finish_clock(scheduler, key, whole_output=whole_output)
    )
    if result is not None:
        scheduler.ledger.bump(_execution_keys.TILE_CLOCK_COMPLETION_SUCCESSES)
    return result

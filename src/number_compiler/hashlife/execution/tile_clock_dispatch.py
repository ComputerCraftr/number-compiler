"""Completed clock actions admitted before generic causal execution."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.execution.tile_collatz_cycle import complete_collatz_cycle
from number_compiler.hashlife.execution.tile_collatz_root_completion import (
    complete_collatz_root,
)
from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
from number_compiler.hashlife.tiles.tile_results import ResultLease

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
    scheduler.ledger.bump("tile_clock_completion_requests")
    result = complete_collatz_cycle(scheduler, key)
    if result is None and whole_output:
        result = complete_collatz_root(scheduler, key)
    if result is not None:
        scheduler.ledger.bump("tile_clock_completion_successes")
    return result

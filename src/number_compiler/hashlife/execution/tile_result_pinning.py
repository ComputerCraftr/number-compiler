"""Authenticated publication of application-owned completed result leases."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.execution.tile_application_authority import (
    application_by_id,
)
from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
from number_compiler.hashlife.tiles.tile_results import ResultLease
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler


def pin_result(
    scheduler: TileScheduler,
    application: int,
    key: PoweredResultKey,
    lease: ResultLease,
) -> None:
    """Validate ownership before warm lookup or retained publication."""
    application_by_id(scheduler, application)
    if type(key) is not PoweredResultKey or type(lease) is not ResultLease:
        raise TypeError("application pins require an exact completed result")
    scheduler.results.validate_key(key)
    if lease._issuer is not scheduler.results or lease._key != key:
        raise ValueError("application pin belongs to another result request")
    _ = lease.result
    binding = application, key
    found = scheduler._pins.get(binding)
    if found is not None:
        if type(found) is not ResultLease or found._key != key:
            raise ValueError("application pin contains another result request")
        _ = found.result
        if found is not lease:
            lease.close()
        scheduler.ledger.bump(_execution_keys.TILE_RESULT_PIN_EARLY_HITS)
        return
    reserved = False
    try:
        scheduler.ledger.reserve(scheduler._pin_owner, entries=1)
        reserved = True
        scheduler._pins[binding] = lease
    except BaseException:
        scheduler._pins.pop(binding, None)
        if reserved:
            scheduler.ledger.release(scheduler._pin_owner, entries=1)
        lease.close()
        raise
    scheduler.ledger.bump(_execution_keys.TILE_SCHEDULER_DEMANDED_RESULT_PINS)


def release_result_pins(scheduler: TileScheduler, application: int) -> None:
    """Release one application's result pins with retryable deletion journals."""
    if type(application) is not int or application < 0:
        raise ValueError("application pin release requires an exact identity")
    bindings = tuple(key for key in scheduler._pins if key[0] == application)
    for binding in bindings:
        lease = scheduler._pins[binding]
        try:
            scheduler._pins.pop(binding)
        except BaseException:
            if binding not in scheduler._pins:
                scheduler._pins[binding] = lease
            raise
        try:
            lease.close()
        except BaseException:
            if not lease._closed:
                scheduler._pins[binding] = lease
            else:
                scheduler.ledger.release(scheduler._pin_owner, entries=1)
            raise
        scheduler.ledger.release(scheduler._pin_owner, entries=1)


__all__ = ["pin_result", "release_result_pins"]

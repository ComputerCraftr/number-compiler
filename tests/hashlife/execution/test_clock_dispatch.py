"""Every public scheduler observation reaches admitted clock completion."""

from __future__ import annotations

from dataclasses import replace

import pytest

from number_compiler.hashlife.execution import tile_causal_entry
from number_compiler.hashlife.execution import tile_scheduler
from number_compiler.hashlife.observation import demanded_tiles
from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
from number_compiler.hashlife.tiles.tile_results import ResultLease
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm


@pytest.mark.parametrize("operation", ("point", "width", "complete", "interface"))
def test_clock_dispatch_precedes_deep_causal_execution(
    monkeypatch: pytest.MonkeyPatch, operation: str
) -> None:
    term = PoweredCollatzTerm(1, 10**6)
    projection = term._point_index()._lazy_application
    application = projection._application
    scheduler = application.scheduler
    original_complete = tile_causal_entry.causal_complete

    def no_deep_completion(
        scheduler: TileScheduler, key: PoweredResultKey
    ) -> ResultLease | None:
        if scheduler.adapter.action_cocycle(key.action).physical_ticks > 3:
            pytest.fail("clock request entered deep causal completion")
        return original_complete(scheduler, key)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("clock request entered a deep causal observation")

    monkeypatch.setattr(tile_causal_entry, "causal_complete", no_deep_completion)
    monkeypatch.setattr(tile_causal_entry, "causal_point", forbidden)
    monkeypatch.setattr(tile_causal_entry, "causal_width_query", forbidden)
    args = (application.action, application.source, application.ports, application.wiring)
    try:
        # Call the scheduler directly to bypass the application's root memo.
        if operation == "point":
            assert scheduler.point(*args, 2) == 1
        elif operation == "width":
            assert scheduler.width(*args) == 3
        elif operation == "complete":
            with scheduler.complete(*args) as completed:
                assert completed.result.physical_ticks == 10**6
                assert scheduler.tiles.active_width(completed.output) == 3
        else:
            interface = application.interface()
            assert interface.physical_ticks == 10**6
            assert interface.event_weight == (10**6 + 2) // 3
        assert term._ledger.counters["tile_clock_completion_successes"] == 1
        audit = audit_registered_payloads(term._ledger)
        assert (
            audit.forbidden_future_payloads,
            audit.unbounded_future_integers,
            audit.unknown_payloads,
        ) == (0, 0, 0)
    finally:
        projection.close()


@pytest.mark.parametrize("operation", ("point", "width", "complete"))
def test_clock_dispatch_cannot_bypass_execution_context_admission(
    monkeypatch: pytest.MonkeyPatch, operation: str
) -> None:
    term = PoweredCollatzTerm(1, 16)
    projection = term._point_index()._lazy_application
    application = projection._application
    scheduler = application.scheduler

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("invalid request reached clock dispatch")

    monkeypatch.setattr(tile_scheduler, "complete_clock", forbidden)
    monkeypatch.setattr(demanded_tiles, "complete_clock", forbidden)
    wiring = replace(application.wiring, orientation=1)
    args = (application.action, application.source, application.ports, wiring)
    before = term._ledger.snapshot()
    try:
        with pytest.raises(ValueError):
            if operation == "point":
                scheduler.point(*args, 0)
            elif operation == "width":
                scheduler.width(*args)
            else:
                scheduler.complete(*args)
        after = term._ledger.snapshot()
        assert (after.entries, after.nodes) == (before.entries, before.nodes)
    finally:
        projection.close()


@pytest.mark.parametrize("seed,ticks", ((1, 10**6), (9557, 13)))
def test_clock_leaves_do_not_recursively_reenter_scheduler(
    monkeypatch: pytest.MonkeyPatch, seed: int, ticks: int
) -> None:
    term = PoweredCollatzTerm(seed, ticks)
    projection = term._point_index()._lazy_application
    application = projection._application
    scheduler = application.scheduler
    complete = scheduler.complete

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("clock leaf recursively re-entered scheduler.complete")

    monkeypatch.setattr(TileScheduler, "complete", forbidden)
    try:
        with complete(
            application.action, application.source, application.ports, application.wiring
        ) as result:
            assert result.result.physical_ticks == ticks
            assert scheduler.tiles.active_width(result.output) == 3
    finally:
        projection.close()

"""Certified Collatz cycle completion remains inside the tile scheduler."""

from __future__ import annotations

import pytest

from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError
from number_compiler.hashlife.observation.tile_projection import LazyProjection
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm


@pytest.mark.parametrize("seed", (1, 2, 4))
def test_large_fixed_cycle_publishes_one_constant_tile_result(seed: int) -> None:
    steps = 10**12 + seed
    cycle = {1: (1, 4, 2), 2: (2, 1, 4), 4: (4, 2, 1)}[seed]
    expected = cycle[steps % 3]
    term = PoweredCollatzTerm(seed, steps)
    width = term.width()
    assert (
        sum(term.digit(position) << position for position in range(width)) == expected
    )
    projection = term._point_index()._lazy_application
    assert type(projection) is LazyProjection
    completed = projection._application.complete()
    assert completed.physical_ticks == steps
    event_offset = {1: 2, 2: 1, 4: 0}[seed]
    assert completed.event_weight == (steps + event_offset) // 3
    assert term._ledger.counters.get("tile_collatz_cycle_completions", 0) == 1
    assert term._ledger.counters.get("tile_causal_frames", 0) < 1024
    audit = audit_registered_payloads(term._ledger)
    assert (
        audit.forbidden_future_payloads,
        audit.unbounded_future_integers,
        audit.unknown_payloads,
    ) == (0, 0, 0)


def test_noninitial_cycle_contract_rejects_the_certified_shortcut() -> None:
    term = PoweredCollatzTerm(1, 8)
    projection = term._point_index()._lazy_application
    assert type(projection) is LazyProjection
    application = projection._application
    altered = application.scheduler.application(
        application.action,
        application.source,
        (1, application.ports[1]),
        application.wiring,
    )
    try:
        with pytest.raises(UnsupportedInterfaceError):
            altered.point(0)
        assert term._ledger.counters.get("tile_collatz_cycle_completions", 0) == 0
    finally:
        altered.close()


def test_completed_cycle_interface_bypasses_causal_evaluation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.hashlife.execution.tile_causal import CausalTileEngine

    term = PoweredCollatzTerm(1, 10**12)
    projection = term._point_index()._lazy_application
    assert type(projection) is LazyProjection
    completed = projection._application.complete()
    monkeypatch.setattr(
        CausalTileEngine,
        "interface",
        lambda *_args: pytest.fail("warm completed result replayed causal evaluation"),
    )
    payload = projection._application.interface()
    assert payload.interface == completed.outgoing
    assert payload.outgoing_ports == completed.outgoing_ports
    assert payload.physical_ticks == completed.physical_ticks
    assert payload.event_weight == completed.event_weight

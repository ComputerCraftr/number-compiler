"""Direct Python observers retain detailed metrics; compact callers may omit them."""

from __future__ import annotations

from number_compiler.api.antihydra_observation import (
    observe_arithmetic,
    observe_arithmetic_many,
    observe_run,
)
from number_compiler.api.cylinder_observation import (
    CollatzObservationContext,
    observe_collatz,
    observe_mirror,
    observe_physical_clock,
)
from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm, run
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def test_cylinder_observers_can_omit_reporting_metadata() -> None:
    physical = PoweredCollatzTerm(1, 0)
    full_clock = observe_physical_clock(1, 0, max_ticks=0, max_digits=8, _term=physical)
    compact_clock = observe_physical_clock(
        1,
        0,
        max_ticks=0,
        max_digits=8,
        _term=physical,
        _include_metrics=False,
    )
    assert {"work_counters", "peak_nodes", "retained_nodes"} <= full_clock.keys()
    assert compact_clock == {
        key: value
        for key, value in full_clock.items()
        if key not in {"work_counters", "peak_nodes", "retained_nodes"}
    }

    context = CollatzObservationContext(1, 0, max_events=0, max_digits=8)
    full_event = observe_collatz(
        1, 0, kind="clock", max_events=0, max_digits=8, _context=context
    )
    compact_event = observe_collatz(
        1,
        0,
        kind="clock",
        max_events=0,
        max_digits=8,
        _context=context,
        _include_metrics=False,
    )
    reporting = {
        "source_work_counters",
        "source_support_retained_nodes",
        "separately_retained",
        "arena_nodes",
        "normalization_compositions",
        "observer_nodes",
        "observer_compositions",
        "ring_power_compositions",
    }
    assert reporting <= full_event.keys()
    assert not reporting.intersection(compact_event)
    assert compact_event["value"] == full_event["value"]
    assert compact_event["discovered_events"] == full_event["discovered_events"]

    reverse = ReverseAddPoweredTerm(196, 0)
    full_mirror = observe_mirror(196, 0, first_width=1, max_digits=8, _term=reverse)
    compact_mirror = observe_mirror(
        196,
        0,
        first_width=1,
        max_digits=8,
        _term=reverse,
        _include_metrics=False,
    )
    assert {"work_counters", "peak_nodes", "retained_nodes"} <= full_mirror.keys()
    assert compact_mirror == {
        key: value
        for key, value in full_mirror.items()
        if key not in {"work_counters", "peak_nodes", "retained_nodes"}
    }


def test_antihydra_observers_can_omit_reporting_metadata() -> None:
    arithmetic = AntihydraArithmeticTerm(0).result()
    full = observe_arithmetic(arithmetic, kind="hensel")
    compact = observe_arithmetic(arithmetic, kind="hensel", _include_metrics=False)
    reporting = {"work_counters", "peak_nodes", "retained_nodes"}
    assert reporting <= full.keys()
    assert not reporting.intersection(compact)
    assert compact["value"] == full["value"]
    assert compact["source_binding"] == full["source_binding"]

    paired = observe_arithmetic_many(
        arithmetic, kinds=("hensel", "mahler"), _include_metrics=False
    )
    assert set(paired) == {"hensel", "mahler"}
    assert all(not reporting.intersection(packet) for packet in paired.values())
    assert "associated_action" in paired["mahler"]["value"]

    physical = run(0)
    full_run = observe_run(physical, kind="clock")
    compact_run = observe_run(physical, kind="clock", _include_metrics=False)
    assert reporting <= full_run.keys()
    assert compact_run == {
        key: value for key, value in full_run.items() if key not in reporting
    }

"""Exact singleton cycles stay in the shared source-image scheduler."""

from __future__ import annotations

from itertools import islice

import pytest

from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from tests.support.assertions import assert_rejected_atomically


@pytest.mark.parametrize("seed", (1, 2, 4))
def test_large_fixed_cycle_publishes_one_constant_tile_result(seed: int) -> None:
    steps = 10**12 + seed
    cycle = {1: (1, 4, 2), 2: (2, 1, 4), 4: (4, 2, 1)}[seed]
    expected = cycle[steps % 3]
    term = PoweredCollatzTerm(seed, steps)
    assert sum(term.digit(i) << i for i in range(term.width())) == expected
    workspace = term._source_image()
    summary = workspace.summary()
    assert summary.width == steps
    assert summary.odd_steps == (steps + {1: 2, 2: 1, 4: 0}[seed]) // 3
    assert summary.cycle is not None
    first = next(islice(workspace.segments(), 1))
    assert first[0] == 0
    assert (
        tuple((first[2] >> i) & 1 for i in range(5))
        == {1: (1, 0, 0, 1, 0), 2: (0, 1, 0, 0, 1), 4: (0, 0, 1, 0, 0)}[seed]
    )
    assert term.resource_ledger.counters["collatz_physical_cycle_compressions"] == 1
    assert term.resource_ledger.counters.get("collatz_physical_leaf_steps", 0) == 0
    audit = audit_registered_payloads(term.resource_ledger)
    assert (
        audit.forbidden_future_payloads,
        audit.unbounded_future_integers,
        audit.unknown_payloads,
    ) == (0, 0, 0)


def test_noninitial_cycle_contract_rejects_the_certified_shortcut() -> None:
    term = PoweredCollatzTerm(1, 8)
    workspace = term._source_image()
    foreign = PoweredCollatzTerm(2, 8)._source_image()
    assert_rejected_atomically(
        term.resource_ledger,
        lambda: workspace.validate_source(foreign.root_source),
        (ValueError, TypeError),
    )


def test_completed_cycle_interface_bypasses_causal_evaluation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = PoweredCollatzTerm(1, 10**12)
    workspace = term._source_image()
    completed = workspace.summary()
    monkeypatch.setattr(
        CausalTileEngine,
        "interface",
        lambda *_args: pytest.fail("cycle replayed causal evaluation"),
    )
    monkeypatch.setattr(
        type(workspace),
        "apply_primitive",
        lambda *_args: pytest.fail("completed image rediscovered leaves"),
    )
    assert workspace.summary() is completed
    assert term.s_arithmetic_clock().events == completed.odd_steps
    assert term.materialize(max_bits=4) == 4


@pytest.mark.parametrize("exponent", (4, 8))
@pytest.mark.parametrize("cycle_ticks", (0, 1, 2, 3, 4))
def test_power_of_two_enters_cycle_with_bounded_residual_work(
    exponent: int,
    cycle_ticks: int,
) -> None:
    steps = exponent + cycle_ticks
    expected = (1, 4, 2)[cycle_ticks % 3]
    term = PoweredCollatzTerm(1 << exponent, steps)
    summary = term._source_image().summary()
    assert summary.width == steps
    assert summary.odd_steps == (cycle_ticks + 2) // 3
    assert term.materialize(max_bits=4) == expected
    assert term.width() == expected.bit_length()
    assert term.resource_ledger.counters.get("collatz_physical_leaf_steps", 0) <= steps
    assert term.resource_ledger.counters.get("tile_causal_frames", 0) == 0


def test_wide_power_of_two_cycle_entry_is_independent_of_temporal_extent() -> None:
    exponent = 1000
    steps = 10**12 + exponent
    expected = (1, 4, 2)[(steps - exponent) % 3]
    term = PoweredCollatzTerm(1 << exponent, steps)
    assert term.materialize(max_bits=4) == expected
    assert term.resource_ledger.counters["collatz_physical_cycle_compressions"] > 0
    assert (
        term.resource_ledger.counters["collatz_physical_temporal_zero_run_symbols"]
        == exponent
    )
    assert term.resource_ledger.counters["collatz_physical_temporal_run_actions"] <= 4
    assert term.resource_ledger.counters.get("collatz_physical_leaf_steps", 0) == 0
    assert term.resource_ledger.counters.get("tile_causal_frames", 0) == 0


def test_power_of_two_short_prefix_does_not_claim_cycle_entry() -> None:
    term = PoweredCollatzTerm(1 << 8, 4)
    assert term.materialize(max_bits=16) == 1 << 4
    assert term._source_image().summary().cycle is None
    assert (
        term.resource_ledger.counters.get("collatz_physical_cycle_compressions", 0) == 0
    )


def test_multi_one_source_does_not_claim_power_of_two_cycle_entry() -> None:
    term = PoweredCollatzTerm((1 << 8) | 1, 4)
    assert term.materialize(max_bits=16) == 580
    assert term._source_image().summary().cycle is None
    assert (
        term.resource_ledger.counters.get("collatz_physical_cycle_compressions", 0) == 0
    )

from random import Random
from typing import Never

import pytest

from devtools.verification.collatz_carry_ranges import CarryRangeTransfer
from devtools.verification.lazy_collatz import LazyCollatzApplication
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.scoped_handles import (
    ArenaToken,
    LoweringCapability,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.payload_audit import audit_registered_payloads


def bits(value: int) -> tuple[int, ...]:
    return tuple((value >> i) & 1 for i in range(value.bit_length()))


def physical(value: int, steps: int) -> tuple[int, int]:
    odds = 0
    for _ in range(steps):
        if value & 1:
            value = 3 * value + 1
            odds += 1
        else:
            value //= 2
    return value, odds


@pytest.mark.parametrize("seed", [1, 2, 3, 5, 27, 64, 255, (1 << 255) - 1])
def test_point_and_width_are_exact_without_any_endpoint_lowering(
    seed: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("point query requested an exact endpoint")

    monkeypatch.setattr(LazyCollatzApplication, "materialize_bits", forbidden)
    monkeypatch.setattr(LazyCollatzApplication, "source_span", forbidden)
    for steps in (0, 1, 2, 3, 4, 16, 64, 256):
        expected, odds = physical(seed, steps)
        app = LazyCollatzApplication(2, steps, bits(seed))
        assert app.active_width() == expected.bit_length()
        for position in {0, expected.bit_length() // 2, expected.bit_length() - 1}:
            assert app.point(position) == (expected >> position) & 1
        assert app.point(-1) == app.point(expected.bit_length()) == 2
        assert app.advance_physical(steps).odd_ticks == odds
        assert app.maximum_carry <= 2
        audit = audit_registered_payloads(app.ledger)
        assert audit.forbidden_future_payloads == 0
        assert audit.unbounded_future_integers == 0
        assert audit.unknown_payloads == 0
        inventory = collect_ledger_metrics(app.ledger)
        assert inventory.resource_audit_complete == 1
        assert inventory.resource_accounting_mismatch == 0
        assert inventory.resource_ledger_entries == app.retained_entries()
        assert not app.retained_spans()


def test_random_accelerated_endpoints_and_cocycles() -> None:
    rng = Random(196)
    for width in (4, 32, 130, 255):
        for _ in range(3):
            seed = rng.getrandbits(width) | 1
            events = rng.randrange(1, 24)
            expected, shift = seed, 0
            for _ in range(events):
                raw = 3 * expected + 1
                valuation = (raw & -raw).bit_length() - 1
                shift += valuation
                expected = raw >> valuation
            app = LazyCollatzApplication(2, 0, bits(seed))
            result = app.advance_events(events)
            assert result.events == events
            assert result.shift == shift
            assert result.view.width == expected.bit_length()
            output = app.materialize_bits(result.view, LoweringCapability(app.token))
            assert output == bits(expected)


def test_long_zero_prefix_is_a_transfer_witness_not_an_integer_prefix() -> None:
    seed = ((1 << 256) - 1) // 3
    app = LazyCollatzApplication(2, 0, bits(seed))
    transfer = app.mul3_summary(app.initial)
    assert transfer[1].first_one == transfer[1].last_one == 256
    assert transfer[1].exit_carry == 0
    result = app.advance_events(1 << 30)
    assert result.shift == 256 + 2 * ((1 << 30) - 1)
    assert result.view.width == 1
    assert app.view_point(result.view, 0) == 1
    assert app.branch_evaluations == 1
    assert app.carry_cell_evaluations < 16
    assert audit_registered_payloads(app.ledger).unbounded_future_integers == 0


def test_three_carry_transfer_composition_and_large_uniform_skip() -> None:
    left = CarryRangeTransfer.bit(1).compose(CarryRangeTransfer.bit(0))
    right = CarryRangeTransfer.bit(0).repeat(1 << 100)
    total = left.compose(right)
    for carry in range(3):
        row = total.rows[carry]
        expected = 3 + carry
        assert row.exit_carry == 0
        assert row.first_one == (expected & -expected).bit_length() - 1
        assert row.last_one == expected.bit_length() - 1
        assert row.length == 2 + (1 << 100)


def test_budget_reservation_is_preemptive_and_inventory_remains_consistent() -> None:
    ledger = ResourceLedger(max_cache_entries=0)
    with pytest.raises(BlockContextBudgetExceeded):
        LazyCollatzApplication(2, 64, bits(27), ledger)
    assert (
        ledger.entries == ledger.nodes == ledger.peak_entries == ledger.peak_nodes == 0
    )
    app = LazyCollatzApplication(2, 64, bits(27))
    app.ledger.max_cache_entries = app.retained_entries()
    before = app.ledger.snapshot()
    with pytest.raises(BlockContextBudgetExceeded):
        app.point(0)
    assert app.ledger.entries == before.entries
    assert app.ledger.nodes == before.nodes
    assert collect_ledger_metrics(app.ledger).resource_accounting_mismatch == 0


def test_view_and_lowering_ownership_are_checked_before_cached_resolution() -> None:
    a = LazyCollatzApplication(2, 16, bits(27))
    b = LazyCollatzApplication(2, 16, bits(3))
    a.range_summary(a.initial)
    with pytest.raises(ValueError, match="different arena"):
        a.range_summary(b.initial)
    with pytest.raises(ValueError, match="different arena"):
        a.view_point(b.initial, 0)
    with pytest.raises(ValueError, match="foreign"):
        a.materialize_bits(a.initial, LoweringCapability(ArenaToken()))


def test_fixed_physical_cycle_and_even_prefix_do_not_expand_with_ticks() -> None:
    for phase in range(3):
        steps = 10**30 + phase
        app = LazyCollatzApplication(2, steps, bits(8))
        result = app.advance_physical(steps)
        expected = (1, 4, 2)[(steps - 3) % 3]
        assert result.view.width == expected.bit_length()
        assert app.materialize_bits(result.view, LoweringCapability(app.token)) == bits(
            expected
        )
        assert app.branch_evaluations <= 1
        assert app.metrics()["macro_actions"] < 16


def test_zero_width_foreign_view_cannot_bypass_lowering_validation() -> None:
    from dataclasses import replace

    a = LazyCollatzApplication(2, 0, bits(3))
    b = LazyCollatzApplication(2, 0, bits(5))
    foreign = replace(b.initial, width=0)
    with pytest.raises(ValueError, match="different arena"):
        a.materialize_bits(foreign, LoweringCapability(a.token))
    assert a.ledger.counters.get("endpoint_lowering_requests", 0) == 0
    assert a.materialize_bits(a.initial, LoweringCapability(a.token)) == bits(3)
    assert a.ledger.counters["explicitly_materialized_endpoints"] == 1

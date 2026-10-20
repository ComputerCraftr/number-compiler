from __future__ import annotations

from collections import OrderedDict
from dataclasses import fields
from math import comb
from random import Random

import pytest

from devtools.verification.lazy_reverse import (
    CarryRangeSummary,
    LazyReverseApplication,
    OffsetProgram,
    ReverseProgram,
    transport_weights,
)
from number_compiler.arithmetic.carry.event_memory import pair_step
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.scoped_handles import (
    ExactSource,
    TransferSummaryID,
)
from number_compiler.arithmetic.fields.dyadic_tile import tile_arena_metrics
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_audit import audit_registered_payloads


def _digits(pair: tuple[int, ...] | tuple[int, int, int], base: int) -> list[int]:
    carry = 0
    output: list[int] = []
    for symbol in pair:
        output.append((symbol + carry) % base)
        carry = (symbol + carry) // base
    if carry:
        output.append(carry)
    return output


@pytest.mark.parametrize("base", (2, 3, 4, 5, 10))
def test_lazy_reverse_points_match_independent_pair_recurrence(base: int) -> None:
    random = Random(base)
    for count in range(5):
        digits = [random.randrange(base) for _ in range(1 + count)]
        digits[-1] = max(1, digits[-1])
        pair = tuple(x + y for x, y in zip(digits, reversed(digits), strict=True))
        steps = 3 * count
        application = LazyReverseApplication(base, -1, steps, pair)
        for _ in range(steps):
            pair, _ = pair_step(pair, base)
        expected = _digits(pair, base)
        assert application.active_width() == len(expected)
        assert [application.point(i) for i in range(len(expected))] == expected
        assert application.point(-1) == application.point(len(expected)) == -1


def test_carry_code_preserves_k1_distinct_from_identity() -> None:
    application = LazyReverseApplication(10, -1, 0, (9, 10, 10, 9))
    identity = application.port_actions.interval_identity(application.carry_port)
    assert application.carry_code_from_summary(identity) == 1
    assert application.scan(0, OrderedDict()) == 1
    summary = next(iter((value for _, value in application.range_snapshot()))).action
    assert application.carry_code_from_summary(summary) == 2


def test_carry_range_miss_is_not_looked_up_twice(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    application = LazyReverseApplication(10, 0, 1, (7, 18, 7))
    original = application.range_action
    parent_lookups: list[tuple[int, int, int]] = []

    def track_range_action(
        generation: int, stop: int, level: int = 1
    ) -> TransferSummaryID | None:
        if (generation, stop, level) == (0, 2, 1):
            parent_lookups.append((generation, stop, level))
        return original(generation, stop, level)

    monkeypatch.setattr(application, "range_action", track_range_action)
    application.evaluate_range(("carry", 0, 2), OrderedDict())
    assert parent_lookups == [(0, 2, 1)]


@pytest.mark.validation  # Full N=256 representation and retention workload.
def test_lazy_reverse_256_keeps_programs_and_range_functions_only() -> None:
    tiles_before = tile_arena_metrics()["intern_misses"]
    application = LazyReverseApplication(10, 0, 255, (7, 18, 7))
    pair: tuple[int, ...] = (7, 18, 7)
    for _ in range(255):
        pair, _ = pair_step(pair, 10)
    expected = _digits(pair, 10)
    assert application.point(0) == expected[0]
    assert application.active_width() == len(expected)
    assert application.retained_spans() == ()
    assert tile_arena_metrics()["intern_misses"] == tiles_before
    assert application.metrics().exact_endpoint_entries == 0
    assert (
        application.workspace_peak
        <= application.workspace_limit
        == 2 * application.horizon
    )
    assert not hasattr(application, "_target")
    allowed = (ExactSource, OffsetProgram, ReverseProgram, CarryRangeSummary)
    audit = audit_registered_payloads(application.ledger)
    assert (
        audit.forbidden_future_payloads
        == audit.unbounded_future_integers
        == audit.unknown_payloads
        == 0
    )
    for payload in (
        application.source,
        *application.offsets_snapshot(),
        *application.programs_snapshot(),
        *(value for _, value in application.range_snapshot()),
    ):
        assert isinstance(payload, allowed)
        if not isinstance(payload, ExactSource):
            assert all(
                isinstance(getattr(payload, field.name), (str, int, TransferSummaryID))
                for field in fields(payload)
            )
        if isinstance(payload, CarryRangeSummary):
            assert payload.stop >= 2 and payload.stop % 2 == 0
            action = application.port_actions
            assert tuple(
                action.apply(
                    action.interval_effect(payload.action).forward,
                    {application.carry_port: value},
                )
                for value in (False, True)
            ) in ((False, False), (False, True), (True, True))
    for inventory in application.ledger.inventory():
        assert inventory.entries == inventory.observed_entries
        assert inventory.nodes == inventory.observed_nodes


def test_lazy_reverse_zero_budget_rejects_before_retaining_source() -> None:
    ledger = ResourceLedger(max_cache_entries=0)
    with pytest.raises(BlockContextBudgetExceeded):
        LazyReverseApplication(10, 0, 64, (7, 18, 7), ledger)
    assert ledger.snapshot().entries == ledger.snapshot().nodes == 0


def test_reverse_transport_coefficients_use_bounded_modular_limbs() -> None:
    # The true central coefficient has almost a thousand bits; the production
    # evaluator only ever emits a five-bit arithmetic port.
    weights = tuple(transport_weights(1000, 0, 5))
    assert max(weights).bit_length() <= 5
    assert weights == tuple(comb(1000, i) % 32 for i in range(1001))

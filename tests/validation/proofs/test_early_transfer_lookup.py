"""Known canonical identities must avoid evaluation, not only allocation."""

from __future__ import annotations

from number_compiler.arithmetic.contracts.scoped_handles import TransferSummaryID
from tests.support.assertions import assert_rejected_atomically

from collections import OrderedDict
from dataclasses import replace
from itertools import product
from typing import TYPE_CHECKING, Literal, Never

import pytest

from devtools.verification.carry_interval_effects import CarryActionQuotientArena
from devtools.verification.lazy_collatz import LazyCollatzApplication
from devtools.verification.lazy_reverse import LazyReverseApplication
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.resources.metric_collection import collect_ledger_metrics

if TYPE_CHECKING:
    import typing

    from devtools.verification.lazy_reverse import ReverseRangeRequest
    from number_compiler.arithmetic.contracts.scoped_handles import TransferSummaryID


def forbidden(*args: object, **kwargs: object) -> Never:
    raise AssertionError("a canonical cache hit performed duplicate evaluation")


def test_joint_composition_alias_hits_before_child_evaluation_or_output_interning(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena = CarryActionQuotientArena()
    port = PortVariable(0, 0, "carry", 0)
    first = arena.interval_word((9, 10), base=10, port=port)
    alias = arena.interval_word((10, 9), base=10, port=port)
    assert first == alias
    after = arena.interval_word((0, 9), base=10, port=port)
    expected = arena.compose_intervals(first, after, port)
    before = arena.ledger.snapshot()
    monkeypatch.setattr(arena, "compose", forbidden)
    monkeypatch.setattr(arena, "_interval", forbidden)
    assert arena.compose_intervals(alias, after, port) == expected
    observed = arena.ledger.snapshot()
    assert (observed.entries, observed.nodes) == (before.entries, before.nodes)
    for name in (
        "composition_evaluations",
        "joint_interval_composition_evaluations",
        "interval_effect_intern_hits",
        "interval_effect_intern_misses",
    ):
        assert observed.counters.get(name, 0) == before.counters.get(name, 0)
    assert (
        observed.counters["joint_interval_composition_cache_hits"]
        == before.counters.get("joint_interval_composition_cache_hits", 0) + 1
    )


def test_each_pair_of_canonical_interval_ids_is_evaluated_at_most_once() -> None:
    arena = CarryActionQuotientArena()
    port = PortVariable(0, 0, "carry", 0)
    actions = {
        arena.interval_word(word, base=10, port=port)
        for word in product((0, 9, 10), repeat=2)
    }
    assert len(actions) == 7
    for first, second in product(actions, repeat=2):
        arena.compose_intervals(first, second, port)
    before = dict(arena.ledger.counters)
    for first, second in product(actions, repeat=2):
        arena.compose_intervals(first, second, port)
    after = arena.ledger.counters
    assert (
        after["joint_interval_composition_evaluations"]
        == before["joint_interval_composition_evaluations"]
    )
    assert (
        after["joint_interval_composition_cache_hits"]
        - before["joint_interval_composition_cache_hits"]
        == 49
    )
    assert after["joint_interval_composition_requests"] == (
        after["joint_interval_composition_cache_hits"]
        + after["joint_interval_composition_evaluations"]
    )
    assert len(arena._interval_compositions) == 49
    assert collect_ledger_metrics(arena.ledger).resource_accounting_mismatch == 0


@pytest.mark.parametrize("pair", ((9, 10, 10, 9), (0, 10, 9, 9, 10, 0), (7, 18, 7)))
def test_scan_canonicalizes_reflected_intervals_before_coefficient_work(
    monkeypatch: pytest.MonkeyPatch,
    pair: tuple[int, int, int, int, int, int]
    | tuple[int, int, int, int]
    | tuple[int, int, int],
) -> None:
    application = LazyReverseApplication(10, -1, 0, pair)
    coefficient = application._coefficient
    calls = []

    def observe(
        generation: int, position: int, bits: int | None = None
    ) -> typing.Generator[
        tuple[Literal["coefficient", "carry"] | int, int, int] | ReverseRangeRequest,
        int | TransferSummaryID,
        int | TransferSummaryID,
    ]:
        calls.append((generation, position))
        return coefficient(generation, position, bits)

    monkeypatch.setattr(application, "_coefficient", observe)
    expected = 0
    for value in pair:
        expected = int(value + expected >= 10)
    assert application._scan(0, OrderedDict()) == expected
    if len(pair) % 2 == 0:
        assert all(position < (len(pair) + 2) // 2 for _generation, position in calls)
        assert len(calls) == 2  # The terminal reset avoids every earlier interval.
        assert application.ledger.counters["interval_reflection_requests"] > 0
        assert all(
            key.stop <= len(pair) + (1 << key.level) - key.stop
            for key in application._ranges
            if len(pair) % (1 << key.level) == 0
        )
    else:
        assert len(calls) == 1  # Only the unpaired terminal reset is needed.
    assert all(key.stop % 2 == 0 for key in application._ranges)


def test_warm_interval_scan_checks_ids_before_any_coefficient_evaluation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    application = LazyReverseApplication(10, -1, 0, (0, 10, 10, 0))
    expected = application._scan(0, OrderedDict())
    before = application.ledger.snapshot()
    monkeypatch.setattr(application, "_evaluate", forbidden)
    monkeypatch.setattr(application.port_actions, "compose_intervals", forbidden)
    assert application._scan(0, OrderedDict()) == expected
    after = application.ledger.snapshot()
    assert (
        after.counters["summary_evaluations"] == before.counters["summary_evaluations"]
    )
    assert (
        after.counters["bounded_limb_operations"]
        == before.counters["bounded_limb_operations"]
    )
    assert (after.entries, after.nodes) == (before.entries, before.nodes)


def _reflected_fixture() -> tuple[
    CarryActionQuotientArena, PortVariable, TransferSummaryID, TransferSummaryID
]:
    arena = CarryActionQuotientArena()
    port = PortVariable(0, 0, "carry", 0)
    action = arena.interval_word((0, 10), base=10, port=port)
    return arena, port, action, arena.reflect_interval(action)


def test_reflection_is_an_involution_and_does_not_identify_different_boundary_functions() -> (
    None
):
    arena, port, action, reflected = _reflected_fixture()
    assert reflected != action
    assert arena.reflect_interval(reflected) == action
    assert (
        arena.interval_effect(action).forward
        == arena.interval_effect(reflected).backward
    )


def test_known_reflection_and_literal_ids_bypass_descriptor_construction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena, port, action, reflected = _reflected_fixture()
    zero = arena.interval_symbol(0, base=10, port=port)
    identity = arena.interval_identity(port)
    before = arena.ledger.snapshot()
    monkeypatch.setattr(arena, "_interval", forbidden)
    assert arena.reflect_interval(action) == reflected
    assert arena.interval_symbol(8, base=10, port=port) == zero
    assert arena.interval_identity(port) == identity
    after = arena.ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    for name in (
        "interval_effect_intern_hits",
        "interval_effect_intern_misses",
        "interval_reflection_evaluations",
        "interval_literal_evaluations",
    ):
        assert after.counters.get(name, 0) == before.counters.get(name, 0)


def test_eviction_releases_early_composition_memos_without_invalidating_ids() -> None:
    arena = CarryActionQuotientArena()
    port = PortVariable(0, 0, "carry", 0)
    a = arena.interval_word((0, 10), base=10, port=port)
    b = arena.interval_word((9, 10), base=10, port=port)
    expected = arena.compose_intervals(a, b, port)
    assert len(arena._interval_compositions) > 0
    arena.reflect_interval(a)
    nodes = arena.ledger.nodes
    assert len(arena._interval_literals) > 0
    assert len(arena._interval_reflections) > 0
    arena.ledger.evict_query_memos()
    assert len(arena._interval_compositions) == 0
    assert len(arena._interval_literals) == len(arena._interval_reflections) == 0
    assert arena.ledger.nodes == nodes
    assert arena.compose_intervals(a, b, port) == expected
    report = collect_ledger_metrics(arena.ledger)
    assert report.resource_accounting_mismatch == report.forbidden_future_payloads == 0


def test_collatz_source_mul3_summary_uses_identity_before_any_stream_work(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    application = LazyCollatzApplication(2, 0, (1, 1, 0, 1, 1))  # 27
    view = application.initial
    expected = application.mul3_summary(view)
    before = application.ledger.snapshot()
    monkeypatch.setattr(application, "_stream", forbidden)
    assert application.mul3_summary(replace(view)) == expected
    after = application.ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    for counter in (
        "bounded_limb_operations",
        "summary_evaluations",
        "collatz_mul3_summary_evaluations",
    ):
        assert after.counters.get(counter, 0) == before.counters.get(counter, 0)
    assert (
        after.counters["collatz_mul3_summary_cache_hits"]
        == before.counters.get("collatz_mul3_summary_cache_hits", 0) + 1
    )


def test_collatz_summary_validates_foreign_view_before_warm_lookup_and_releases_on_eviction() -> (
    None
):
    a = LazyCollatzApplication(2, 0, (1, 1))
    b = LazyCollatzApplication(2, 0, (1, 1))
    expected = a.mul3_summary(a.initial)
    assert_rejected_atomically(a.ledger, lambda: a.mul3_summary(b.initial), ValueError)
    assert len(a._mul3_summaries) == 1
    a.ledger.evict_query_memos()
    assert len(a._mul3_summaries) == 0
    assert a.mul3_summary(a.initial) == expected
    report = collect_ledger_metrics(a.ledger)
    assert report.resource_accounting_mismatch == report.forbidden_future_payloads == 0


def test_extending_collatz_event_request_reuses_existing_program_summaries() -> None:
    application = LazyCollatzApplication(2, 0, (1, 1, 0, 1, 1))
    application.advance_events(8)
    before = dict(application.ledger.counters)
    application.advance_events(9)
    after = application.ledger.counters
    assert (
        after["collatz_event_endpoint_reuse"]
        - before.get("collatz_event_endpoint_reuse", 0)
        == 1
    )
    assert (
        after.get("collatz_event_summary_hits", 0)
        - before.get("collatz_event_summary_hits", 0)
        == 0
    )
    assert (
        after["collatz_event_summary_evaluations"]
        - before["collatz_event_summary_evaluations"]
        == 1
    )
    assert after["collatz_event_summary_requests"] == (
        after.get("collatz_event_summary_hits", 0)
        + after["collatz_event_summary_evaluations"]
    )

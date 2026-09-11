"""Source-backed Collatz parent transfers skip work without retaining bits."""

from __future__ import annotations

import random
from typing import Never

import pytest

from devtools.proofs.lazy_collatz import (
    CarryRangeSummary,
    CarryRangeTransfer,
    LazyCollatzApplication,
    _Program,
)
from devtools.proofs.lazy_collatz_range import CollatzRangeEffect, CollatzRangeEvaluator
from number_compiler.arithmetic.contracts.scoped_handles import (
    ExactSource,
    TransferSummaryID,
)
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics


def bits(value: int, width: int | None = None) -> tuple[int, ...]:
    return tuple(
        (value >> position) & 1
        for position in range(value.bit_length() if width is None else width)
    )


def physical(value: int, steps: int) -> int:
    for _ in range(steps):
        value = value // 2 if value % 2 == 0 else 3 * value + 1
    return value


def test_dag_queries_never_expand_or_stream_the_temporal_program(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("DAG query expanded a stream or exact endpoint")

    for name in ("_stream", "_operations", "materialize_bits", "_source_transfer"):
        monkeypatch.setattr(LazyCollatzApplication, name, forbidden)
    rng = random.Random(5612)
    for seed in (27, 64, 255, *(rng.randrange(1, 1 << 32) for _ in range(5))):
        for steps in (0, 1, 2, 16, 64):
            expected = physical(seed, steps)
            app = LazyCollatzApplication(2, steps, bits(seed))
            assert app.active_width() == expected.bit_length()
            for position in (0, expected.bit_length() // 2, expected.bit_length() - 1):
                assert app.point(position) == (expected >> position) & 1
            assert app.ledger.counters.get("collatz_stream_emitted_bits", 0) == 0
            assert collect_ledger_metrics(app.ledger).forbidden_future_payloads == 0


def test_warm_dyadic_parent_skips_all_descendants_and_keeps_action_ids() -> None:
    seed = (1 << 127) - 1
    app = LazyCollatzApplication(2, 0, bits(seed))
    view = app._append(app.initial, _Program("mul3"), 129)
    arena = app._range_evaluator
    first = arena.range_effect(view.program, 0, 64)
    before = app.ledger.snapshot()
    second = arena.range_effect(view.program, 0, 64)
    after = app.ledger.snapshot()
    assert first == second
    for counter in (
        "collatz_dag_visits",
        "collatz_source_reads",
        "bounded_limb_operations",
    ):
        assert after.counters.get(counter, 0) == before.counters.get(counter, 0)
    assert (
        after.counters["collatz_range_hits"]
        == before.counters.get("collatz_range_hits", 0) + 1
    )
    assert len(arena._compositions) > 0
    actions = tuple(arena._effects)
    app.ledger.evict_query_memos()
    assert arena.range_effect(view.program, 0, 64) == first
    assert tuple(arena._effects) == actions
    assert all(
        key.length >= 8 and key.length & (key.length - 1) == 0 for key in arena._ranges
    )
    assert collect_ledger_metrics(app.ledger).resource_accounting_mismatch == 0


def test_distinct_eight_bit_words_alias_without_an_inverse_word_projection() -> None:
    source = bits(11, 8) + bits(15, 8)
    app = LazyCollatzApplication(2, 0, source)
    arena = app._range_evaluator
    first = arena.range_effect(app.initial.program, 0, 8)
    second = arena.range_effect(app.initial.program, 8, 8)
    assert source[:8] != source[8:]
    assert first == second
    assert len({action for action in arena._ranges.values()}) == 1
    assert all(type(action) is TransferSummaryID for action in arena._ranges.values())
    assert len(arena._effects) == 1


def test_equal_original_source_tiles_reuse_transfer_before_reading_the_second_tile() -> (
    None
):
    source = (1, 0, 1, 0, 1, 0, 1, 1) * 2
    ledger = ResourceLedger()
    geometry = SourceGeometry(ledger, ExactSource(source, 2, "collatz", 2))
    geometry.span(source, 2, len(source))
    app = LazyCollatzApplication(2, 0, source, ledger, source_geometry=geometry)
    arena = app._range_evaluator
    first = arena.range_effect(app.initial.program, 0, 8)
    before = ledger.counters.get("collatz_source_reads", 0)
    assert arena.range_effect(app.initial.program, 8, 8) == first
    assert ledger.counters.get("collatz_source_reads", 0) == before
    assert ledger.counters["collatz_source_tile_effect_hits"] >= 1
    assert len(arena._source_tiles) == 1
    assert collect_ledger_metrics(ledger).forbidden_future_payloads == 0


def test_range_action_owner_validation_precedes_composition_work() -> None:
    first = LazyCollatzApplication(2, 0, bits(11, 8))
    other = LazyCollatzApplication(2, 0, bits(11, 8))
    a, b = first._range_evaluator, other._range_evaluator
    a.range_effect(first.initial.program, 0, 8)
    b.range_effect(other.initial.program, 0, 8)
    local, foreign = next(iter(a._ids.values())), next(iter(b._ids.values()))
    before = first.ledger.snapshot()
    with pytest.raises(ValueError):
        a.compose(local, foreign)
    assert first.ledger.snapshot().counters == before.counters


def test_distinct_evaluators_of_one_application_have_distinct_action_scopes() -> None:
    application = LazyCollatzApplication(2, 0, bits(27))
    first = application._range_evaluator
    second = CollatzRangeEvaluator(application)
    first_effect = first.range_effect(application.initial.program, 0, 8)
    second_effect = second.range_effect(application.initial.program, 8, 8)
    local = next(iter(first._ids.values()))
    foreign = next(iter(second._ids.values()))
    assert local.local_id == foreign.local_id
    assert local != foreign
    assert first_effect != second_effect
    for warm in (False, True):
        if warm:
            first.compose(local, local)
            second.compose(foreign, foreign)
        before = application.ledger.snapshot()
        with pytest.raises(ValueError):
            second.effect(local)
        with pytest.raises(ValueError):
            first.compose(local, foreign)
        with pytest.raises(ValueError):
            second.compose(foreign, local)
        assert application.ledger.snapshot() == before


def test_warm_covering_parent_cannot_change_truncated_event_prefix_semantics() -> None:
    cold = LazyCollatzApplication(2, 0, bits(27))
    expected = cold._range_evaluator.event_summary(cold.initial.program, 3)
    warm = LazyCollatzApplication(2, 0, bits(27))
    warm._range_evaluator.range_effect(warm.initial.program, 0, 8)
    assert warm._range_evaluator.event_summary(warm.initial.program, 3) == expected


def test_event_handle_and_extent_validation_precede_warm_shortcuts() -> None:
    first = LazyCollatzApplication(2, 0, bits(27))
    other = LazyCollatzApplication(2, 0, bits(27))
    evaluator = first._range_evaluator
    evaluator.event_summary(first.initial.program, 5)
    before = first.ledger.snapshot()
    with pytest.raises(ValueError):
        evaluator.event_summary(other.initial.program, 5)
    for width in (0, -1, True):
        with pytest.raises(ValueError):
            evaluator.event_summary(first.initial.program, width)
    assert first.ledger.snapshot().counters == before.counters


def test_range_witnesses_cannot_reverse_first_and_last() -> None:
    with pytest.raises(ValueError, match="ordered"):
        CarryRangeSummary(8, 0, 7, 1)
    with pytest.raises(ValueError, match="ordered"):
        CollatzRangeEffect(CarryRangeTransfer.bit(0).repeat(8), 7, 1)


def test_revisited_point_uses_parent_witness_after_another_point_query() -> None:
    application = LazyCollatzApplication(2, 32, bits(27))
    answer = application.point(0)
    application.point(3)
    before = application.ledger.snapshot()
    assert application.point(0) == answer
    after = application.ledger.snapshot()
    for name in (
        "collatz_leaf_dag_visits",
        "collatz_leaf_emitted_bits",
        "bounded_limb_operations",
    ):
        assert after.counters.get(name, 0) == before.counters.get(name, 0)
    assert (
        after.counters["collatz_point_parent_hits"]
        == before.counters.get("collatz_point_parent_hits", 0) + 1
    )

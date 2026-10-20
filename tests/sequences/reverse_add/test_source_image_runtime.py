"""Reverse/add source-image runtime and accounting assertions."""

from __future__ import annotations

import pytest

from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.stores import LedgerDict
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from tests.support.reference_arithmetic import literal_reverse_add
from tests.support.source_image_assertions import (
    assert_source_image_replay_stable,
    assert_source_image_runtime_bridge,
)

pytestmark = pytest.mark.validation


@pytest.mark.parametrize("generation", (16, 32, 64, 128, 256))
def test_reverse_runtime_reports_exact_source_image_outputs_and_publications(
    generation: int,
) -> None:
    term = ReverseAddPoweredTerm(196, generation)
    assert term.materialize(max_bits=10_000) == literal_reverse_add(196, generation)
    assert 0 <= term.digit(0) <= 9
    assert_source_image_runtime_bridge(term, "reverse-add-source-cylinder")


def test_identical_warm_point_does_not_rebuild_temporal_parents() -> None:
    term = ReverseAddPoweredTerm(196, 128)
    assert term.materialize(max_bits=10_000) == literal_reverse_add(196, 128)
    first = term.digit(0)
    metrics = term.metrics()
    publications = metrics.resource_work_counters["source_image_publications"]
    projection_publications = metrics.resource_work_counters[
        "source_image_projection_publications"
    ]
    assert publications > 0 and projection_publications > 0
    assert term.digit(0) == first
    after = term.metrics()
    assert after.resource_work_counters["source_image_publications"] == publications
    assert (
        after.resource_work_counters["source_image_projection_publications"]
        == projection_publications
    )


@pytest.mark.parametrize("seed,steps", ((196, 8),), ids=("reverse-add",))
@pytest.mark.accounting
def test_reverse_runtime_image_matches_oracle_and_replays_without_republication(
    seed: int, steps: int
) -> None:
    term = ReverseAddPoweredTerm(seed, steps)
    expected = literal_reverse_add(seed, steps)
    expected_low = expected % term.base
    assert term.digit(0) == expected_low
    assert collect_ledger_metrics(term.resource_ledger).resource_audit_complete == 1
    metrics = term.metrics()
    behavior = term.behavior_metrics()
    assert behavior.temporal_quotient_family == "reverse-add-source-cylinder"
    assert metrics.resource_audit_complete == 1
    assert metrics.resource_accounting_mismatch == 0
    assert metrics.forbidden_future_payloads == 0
    assert metrics.retained_unbounded_future_integers == 0
    expected_digits = tuple(map(int, reversed(str(expected))))
    assert term.digits() == expected_digits
    replay_counters = dict(term.resource_ledger.counters)
    assert term.digits() == expected_digits
    after = term.resource_ledger.counters
    assert_source_image_replay_stable(replay_counters, after)


@pytest.mark.validation
@pytest.mark.accounting
def test_metrics_are_snapshot_only_for_a_not_yet_constructed_reverse_image() -> None:
    term = ReverseAddPoweredTerm(196, 20)
    assert collect_ledger_metrics(term.resource_ledger).resource_audit_complete == 1
    before = term.resource_ledger.snapshot()
    report = term.behavior_metrics()
    after = term.resource_ledger.snapshot()
    assert before == after
    assert report.resource_audit_complete == 1
    assert report.resource_accounting_mismatch == 0
    assert term.published_workspace is None

    owner = term.resource_ledger.register("metrics-snapshot-invalidation", "query_memo")
    store: LedgerDict[str, int] = term.resource_ledger.make_dict(owner)
    term.resource_ledger.reserve(owner, entries=1)
    store["probe"] = 1
    changed = term.behavior_metrics()
    assert changed.resource_audit_complete == 0
    assert term.published_workspace is None

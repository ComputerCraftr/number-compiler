"""Collatz source-image runtime and accounting assertions."""

from __future__ import annotations

import pytest

from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from tests.support.collatz_images import projected_collatz_runtime_term
from tests.support.reference_arithmetic import physical_collatz_literal
from tests.support.source_image_assertions import (
    assert_source_image_replay_stable,
    assert_source_image_runtime_bridge,
)

pytestmark = pytest.mark.validation


@pytest.mark.parametrize("steps", (16, 32, 64, 128, 256))
def test_collatz_runtime_reports_actual_source_image_publications(steps: int) -> None:
    term = PoweredCollatzTerm(140137, steps)
    assert term.digit(0) in (0, 1)
    assert_source_image_runtime_bridge(term, "collatz-dyadic-source-image")


def test_collatz_radix_projection_reports_source_image_work() -> None:
    projected_term = projected_collatz_runtime_term(
        seed=140137, index=11, radix=3, checked_position=3
    )
    metrics = projected_term.metrics()
    assert metrics.temporal_parent_requests == 0
    assert metrics.temporal_parent_compositions == 0
    counters = metrics.resource_work_counters
    assert counters.get("source_image_publications", 0) > 0
    assert counters.get("collatz_image_radix_demands", 0) > 0
    assert projected_term.operator_nodes == 0
    assert metrics.whole_word_sweeps == metrics.proof_machine_applications == 0
    assert metrics.sequential_generation_advances == 0
    assert (
        collect_ledger_metrics(projected_term.resource_ledger).forbidden_future_payloads
        == 0
    )


@pytest.mark.parametrize("seed,steps", ((27, 8),), ids=("collatz",))
@pytest.mark.accounting
def test_collatz_runtime_image_matches_oracle_and_replays_without_republication(
    seed: int, steps: int
) -> None:
    term = PoweredCollatzTerm(seed, steps)
    expected = physical_collatz_literal(seed, steps)
    expected_low = expected & 1
    assert term.digit(0) == expected_low
    assert collect_ledger_metrics(term.resource_ledger).resource_audit_complete == 1
    metrics = term.metrics()
    behavior = term.behavior_metrics()
    assert behavior.temporal_quotient_family == "collatz-dyadic-source-image"
    assert metrics.resource_audit_complete == 1
    assert metrics.resource_accounting_mismatch == 0
    assert metrics.forbidden_future_payloads == 0
    assert metrics.retained_unbounded_future_integers == 0
    assert term.materialize(max_bits=10_000) == expected
    replay_counters = dict(term.resource_ledger.counters)
    assert term.materialize(max_bits=10_000) == expected
    after = term.resource_ledger.counters
    assert_source_image_replay_stable(replay_counters, after)

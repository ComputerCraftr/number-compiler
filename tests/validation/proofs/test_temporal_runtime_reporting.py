"""Runtime image publication, replay and accounting evidence."""

from __future__ import annotations

from collections.abc import Callable

import pytest

from number_compiler.hashlife.observation.hashlife_projection import HashLifeBlockIndex
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.stores import LedgerDict
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from tests.support.source_image_assertions import assert_source_image_replay_stable


def _reverse_add(value: int, steps: int) -> int:
    for _ in range(steps):
        value += int(str(value)[::-1])
    return value


def _collatz(value: int, steps: int) -> int:
    for _ in range(steps):
        value = 3 * value + 1 if value & 1 else value // 2
    return value


@pytest.mark.parametrize(
    "constructor,seed,steps,oracle,family",
    (
        (ReverseAddPoweredTerm, 196, 8, _reverse_add, "reverse-add-source-cylinder"),
        (PoweredCollatzTerm, 27, 8, _collatz, "collatz-dyadic-source-image"),
    ),
)
def test_family_runtime_image_matches_oracle_and_replays_without_republication(
    constructor: Callable[[int, int], PoweredCollatzTerm | ReverseAddPoweredTerm],
    seed: int,
    steps: int,
    oracle: Callable[[int, int], int],
    family: str,
) -> None:
    term = constructor(seed, steps)
    expected = oracle(seed, steps)
    expected_low = expected % term.base if hasattr(term, "base") else expected & 1
    assert term.digit(0) == expected_low
    assert collect_ledger_metrics(term._ledger).resource_audit_complete == 1
    metrics = term.metrics()
    behavior = term.behavior_metrics()
    assert behavior.temporal_quotient_family == family
    assert metrics.resource_audit_complete == 1
    assert metrics.resource_accounting_mismatch == 0
    assert metrics.forbidden_future_payloads == 0
    assert metrics.retained_unbounded_future_integers == 0

    if isinstance(term, PoweredCollatzTerm):
        assert term.materialize(max_bits=10_000) == expected
        replay_counters = dict(term._ledger.counters)
        assert term.materialize(max_bits=10_000) == expected
        after = term._ledger.counters
        assert_source_image_replay_stable(replay_counters, after)
    else:
        expected_digits = tuple(map(int, reversed(str(expected))))
        assert term.digits() == expected_digits
        replay_counters = dict(term._ledger.counters)
        assert term.digits() == expected_digits
        after = term._ledger.counters
        assert_source_image_replay_stable(replay_counters, after)


def test_metrics_are_snapshot_only_for_a_not_yet_constructed_reverse_image() -> None:
    term = ReverseAddPoweredTerm(196, 20)
    assert collect_ledger_metrics(term._ledger).resource_audit_complete == 1
    before = term._ledger.snapshot()
    report = term.behavior_metrics()
    after = term._ledger.snapshot()
    assert before == after
    assert report.resource_audit_complete == 1
    assert report.resource_accounting_mismatch == 0
    assert term._workspace is None

    owner = term._ledger.register("metrics-snapshot-invalidation", "query_memo")
    store: LedgerDict[str, int] = term._ledger.make_dict(owner)
    term._ledger.reserve(owner, entries=1)
    store["probe"] = 1
    changed = term.behavior_metrics()
    assert changed.resource_audit_complete == 0
    assert term._workspace is None


def test_generic_tile_point_retains_response_and_preserves_replay() -> None:
    from array import array

    from devtools.verification.block_power import compose_block_effects
    from number_compiler.arithmetic.contracts.block_effect import BlockContextBudget
    from number_compiler.arithmetic.contracts.block_kernel import FiniteBlockEffect
    from number_compiler.hashlife.observation.tile_projection import LazyProjection
    from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect

    identity = FiniteBlockEffect(
        base=2,
        exponent=1,
        left_count=1,
        right_count=1,
        alphabet_size=4,
        initial_left=0,
        initial_right=0,
        left_transitions=array("I", [0] * 4),
        right_transitions=array("I", [0] * 4),
        outputs=bytes(range(4)),
        kernel_name="runtime-image-audit",
        storage_bytes=0,
        uncompressed_bytes=0,
        blank_left_tail=0,
        blank_right_tail=0,
        stable_blank_output=True,
    )
    effect = compose_block_effects(
        identity, DigitNormalizeBlockEffect(2), budget=BlockContextBudget()
    )
    index = HashLifeBlockIndex(effect, (1, 2), logical_length=4)
    projection = index._lazy_application
    assert type(projection) is LazyProjection
    assert index.direct_powered_point(0) == 1
    cold = index.metrics()
    cold_counters = cold.resource_work_counters
    assert cold_counters["point_response_requests"] == 1
    assert cold_counters["point_response_evaluations"] == 1
    assert cold_counters.get("point_response_cache_hits", 0) == 0
    assert cold.retained_point_response_scalars == 1
    assert cold.resource_audit_complete == 1
    assert cold.resource_accounting_mismatch == 0
    before = dict(index._ledger.counters)
    assert index.direct_powered_point(0) == 1
    after = index._ledger.counters
    assert after["point_response_requests"] == before["point_response_requests"] + 1
    assert (
        after["point_response_cache_hits"]
        == before.get("point_response_cache_hits", 0) + 1
    )
    assert after["point_response_evaluations"] == before["point_response_evaluations"]

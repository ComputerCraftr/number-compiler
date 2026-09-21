"""Cache metrics consume authenticated causal admission metadata."""

from __future__ import annotations

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.tile_causal_admission import admit_run_actions
from number_compiler.resources.cache_gc_metrics import record_execution_cache_event
from tests.arithmetic.contracts.test_tile_kernel import _runtime


def test_admitted_cache_event_does_not_reenter_action_cocycle(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, tiles, adapter, action, scheduler = _runtime(BaseBlockEffect(3))
    source = tiles.leaf(adapter.alphabet(action), 0)
    tasks = scheduler._causal_tasks
    run = tasks.begin_run()
    token = admit_run_actions(adapter, tasks, ledger, action)
    try:

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("admitted cache metrics re-entered action cocycle")

        monkeypatch.setattr(type(adapter), "action_cocycle", forbidden)
        record_execution_cache_event(
            scheduler.results,
            "result",
            "miss",
            action,
            source.tile,
            action_admission=token,
        )
        assert ledger.counters.get("cache_event_histogram_dropped", 0) == 0
    finally:
        source.close()
        tasks.clear_action_admission(token)
        tasks.end_run(run)


def test_foreign_admission_is_rejected_before_metric_mutation() -> None:
    ledger, tiles, adapter, action, scheduler = _runtime(BaseBlockEffect(3))
    source = tiles.leaf(adapter.alphabet(action), 0)
    other_ledger, _other_tiles, other_adapter, other_action, other_scheduler = _runtime(
        BaseBlockEffect(3)
    )
    tasks = other_scheduler._causal_tasks
    run = tasks.begin_run()
    token = admit_run_actions(other_adapter, tasks, other_ledger, other_action)
    before = ledger.snapshot()
    try:
        with pytest.raises(ValueError, match="outside this run's admitted DAG"):
            record_execution_cache_event(
                scheduler.results,
                "result",
                "miss",
                action,
                source.tile,
                action_admission=token,
            )
        assert ledger.snapshot() == before
    finally:
        source.close()
        tasks.clear_action_admission(token)
        tasks.end_run(run)

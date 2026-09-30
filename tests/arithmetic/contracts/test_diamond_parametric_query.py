"""Higher parents answer through symbolic ports without midpoint observation."""

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.continuations.diamond_runtime import (
    DiamondRuntime,
)
from number_compiler.hashlife.observation.diamond_parametric_query import (
    parametric_point,
    parametric_width,
)
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from tests.support.diamond_query import build, bounded_case


@pytest.mark.parametrize("steps", [0, 1, 2, 3, 4, 5])
@pytest.mark.parametrize("effect", [CollatzPhysicalBlockEffect(), BaseBlockEffect(3)])
def test_higher_point_width_do_not_use_legacy_midpoint_scheduler(
    effect: BaseBlockEffect | CollatzPhysicalBlockEffect,
    steps: int,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    app, expected = bounded_case(effect, steps)

    def forbidden(*args: object) -> Never:
        raise AssertionError("higher parent must not ask the legacy midpoint evaluator")

    monkeypatch.setattr(DiamondRuntime, "_transfer", forbidden)
    monkeypatch.setattr(DiamondRuntime, "_output", forbidden)
    monkeypatch.setattr(DiamondRuntime, "_raw_output", forbidden)
    monkeypatch.setattr(DiamondRuntime, "execute", forbidden)
    assert [parametric_point(app.runtime, app.root, i) for i in range(8)] == expected
    for bound in (0, 1, 3, 5, 8):
        assert parametric_width(app.runtime, app.root, app.observer, bound) == max(
            (
                i + 1
                for i, digit in enumerate(expected[:bound])
                if digit != effect.blank
            ),
            default=0,
        )
    assert app.ledger.counters.get("sequential_generation_advances", 0) == 0
    assert app.ledger.counters.get("scalar_observation_requests", 0) == 0
    assert app.ledger.counters.get("generic_higher_action_publications", 0) > 0
    assert all(row.accounting_delta == 0 for row in app.ledger.inventory())
    from number_compiler.resources.metric_collection import collect_ledger_metrics

    snapshot = app.ledger.snapshot()
    report = collect_ledger_metrics(app.ledger)
    for counter in (
        "generic_higher_action_early_hits",
        "generic_higher_action_publications",
        "parametric_width_parent_visits",
        "parametric_width_forest_visits",
        "parametric_width_descent_steps",
        "parametric_width_contexts_peak",
    ):
        assert getattr(report, counter) == snapshot.counters.get(counter, 0)
    assert snapshot.counters["higher_width_observations"] == 4
    assert snapshot.counters["higher_point_observations"] == 8
    assert report.forbidden_future_payloads == 0
    assert report.resource_accounting_mismatch == 0
    assert app.ledger.snapshot() == snapshot


def test_generic_runtime_rejects_an_exhausted_budget_before_registration() -> None:
    app = build(BaseBlockEffect(3), (2, 4, 2), 8, 3)
    app.ledger.max_cache_entries = app.ledger.entries
    before = app.ledger.snapshot(), tuple(app.ledger.inventory())

    with pytest.raises(BlockContextBudgetExceeded):
        parametric_point(app.runtime, app.root, 0)

    assert (app.ledger.snapshot(), tuple(app.ledger.inventory())) == before
    assert not hasattr(app.runtime, "_generic_higher_runtime")

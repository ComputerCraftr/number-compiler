"""Closed events remain bounded consumers of the shared source scheduler."""

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicReturnImageID,
    _SourceNode,
)
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.dyadic_return_payload_audit import (
    audit_dyadic_return_payloads,
)
from number_compiler.sequences.antihydra import mahler_cache
from number_compiler.sequences.antihydra.mahler_action import associated_action
from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm


def _literal(h: int, width: int) -> tuple[int, int, int, int | None]:
    balance, minimum, failure = 0, 0, None
    for index in range(width):
        balance += -1 if h & 1 else 2
        minimum = min(minimum, balance)
        if failure is None and balance < 0:
            failure = index
        h += h // 2
    return h, balance, minimum, failure


@pytest.mark.parametrize("q", (2, 3, 6, 32, 64))
@pytest.mark.parametrize("tail", (-1, 0, 1))
def test_punctured_leaf_and_partial_zero_prefix_match_literal(
    q: int,
    tail: int,
) -> None:
    width = q + tail
    h = (5 << (q - 1)) + 1
    term = AntihydraArithmeticTerm(0)
    workspace = term._arithmetic_image()
    source = workspace._append_source(
        _SourceNode(h % (1 << width), width, h >> width, None, None, None, 0, True)
    )
    image = workspace.scheduler.source_image(
        workspace, source, workspace._action(width)
    )
    view = workspace.scheduler._source_image_core().view(image)
    assert type(view.payload) is DyadicReturnImageID
    summary = workspace.image_node(view.payload).summary
    expected_h, delta, minimum, failure = _literal(h, width)
    transfer = summary.transfer
    assert (transfer.upper * h + transfer.offset) // transfer.lower == expected_h
    assert (summary.delta, summary.minimum) == (delta, minimum)
    assert workspace.first_failure(view) == failure
    assert summary.support is not None
    support = workspace.support_node(summary.support)
    assert (
        support.saturated and support.branch_word is None and support.children is None
    )
    if tail == -1:
        assert (
            term.ledger.counters.get(
                "antihydra_arithmetic_temporal_punctured_event_actions", 0
            )
            == 0
        )
    elif width <= workspace.MAX_LEAF_STEPS:
        assert (
            term.ledger.counters[
                "antihydra_arithmetic_temporal_punctured_event_actions"
            ]
            >= 1
        )
    else:
        assert (
            term.ledger.counters["antihydra_arithmetic_temporal_balanced_routes"] >= 1
        )


def test_public_source_and_lazy_mahler_share_closed_leaf_publication(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = AntihydraArithmeticTerm(64)
    workspace = term._arithmetic_image()

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("closed event went through separate homogeneous runs")

    monkeypatch.setattr(workspace, "_runs", forbidden)
    with monkeypatch.context() as optional:
        optional.setattr(mahler_cache, "ExactRational", forbidden)
        optional.setattr(mahler_cache, "SaturatingAffineAction", forbidden)
        result = term.result()
    assert (result.h, result.balance, result.minimum, result.first_failure_index) == (
        _literal(8, 64)
    )
    assert not term.mahler_workspace and not term._segments_ready
    assert (
        term.ledger.counters["antihydra_arithmetic_temporal_punctured_event_actions"]
        > 0
    )
    assert associated_action(result)["first_failure"] == 2
    assert term.mahler_workspace is not None
    assert term.mahler_workspace.source_workspace is workspace
    assert term.ledger.counters["mahler_source_composed_image_reads"] == 1
    assert not audit_dyadic_return_payloads(term.ledger).invalid


@pytest.mark.parametrize("h", (6, 10, 14, 16))
def test_punctured_leaf_preserves_late_first_failure_without_event_replay(
    h: int,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    width = 64
    workspace = AntihydraArithmeticTerm(0)._arithmetic_image()
    source = workspace._append_source(
        _SourceNode(h, width, 0, None, None, None, 0, True)
    )
    image = workspace.scheduler.source_image(
        workspace, source, workspace._action(width)
    )
    view = workspace.scheduler._source_image_core().view(image)
    expected = _literal(h, width)[3]
    assert expected is not None and expected > 0

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("first-failure consumer replayed punctured events")

    monkeypatch.setattr(workspace, "_punctured_steps", forbidden)
    monkeypatch.setattr(workspace, "_source_value", forbidden)
    assert workspace.first_failure(view) == expected
    assert not workspace.demanded_support


def test_punctured_power_budget_releases_transient_workspace() -> None:
    term = AntihydraArithmeticTerm(0)
    workspace = term._arithmetic_image()
    ledger = term.ledger
    scratch = RunArithmeticWorkspace.for_ledger(ledger, workspace.counter_prefix)
    before = ledger.entries, ledger.nodes
    ledger.max_nodes = ledger.nodes + 23
    with pytest.raises(BlockContextBudgetExceeded), scratch.scope():
        tuple(workspace._punctured_steps((5 << 31) + 1, 32, scratch))
    assert (ledger.entries, ledger.nodes) == before
    assert scratch.nodes == 0 and not scratch.active

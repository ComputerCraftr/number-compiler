"""Closed events remain bounded consumers of the shared source scheduler."""

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.hashlife.execution.dyadic_return_actions import append_source
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicReturnSourceRecord,
)
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.dyadic_return_payload_audit import (
    audit_dyadic_return_payloads,
)
from number_compiler.sequences.antihydra import mahler_cache
from number_compiler.sequences.antihydra.mahler_action import associated_action
from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm
from tests.support.mahler_harmonic_reference import literal_antihydra_summary
from tests.support.source_image_assertions import dyadic_image_summary


@pytest.mark.parametrize("q", (2, 3, 6, 32, 64))
@pytest.mark.parametrize("tail", (-1, 0, 1))
def test_punctured_leaf_and_partial_zero_prefix_match_literal(
    q: int,
    tail: int,
) -> None:
    width = q + tail
    h = (5 << (q - 1)) + 1
    term = AntihydraArithmeticTerm(0)
    workspace = term.arithmetic_image()
    source = append_source(
        workspace,
        DyadicReturnSourceRecord(
            h % (1 << width), width, h >> width, None, None, None, 0, True
        ),
    )
    image = workspace.scheduler.source_image(
        workspace, source, workspace.action_for_extent(width)
    )
    view = workspace.scheduler.source_image_core().view(image)
    summary = dyadic_image_summary(workspace, view)
    expected_h, delta, minimum, _odd_steps, failure = literal_antihydra_summary(
        h, width
    )
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


def test_public_source_and_lazy_mahler_share_closed_leaf_publication(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = AntihydraArithmeticTerm(64)
    workspace = term.arithmetic_image()
    event_actions = term.ledger.counters[
        "antihydra_arithmetic_temporal_punctured_event_actions"
    ]

    def forbidden_event_replay(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("published source image replayed punctured events")

    # The scheduler has already published the complete source image. Results
    # and the later Mahler projection must consume that publication instead of
    # reopening the arithmetic event constructor.
    monkeypatch.setattr(workspace, "punctured_steps", forbidden_event_replay)
    assert event_actions > 0
    with monkeypatch.context() as optional:
        optional.setattr(mahler_cache, "ExactRational", forbidden_event_replay)
        optional.setattr(mahler_cache, "SaturatingAffineAction", forbidden_event_replay)
        result = term.result()
    expected = literal_antihydra_summary(8, 64)
    assert (result.h, result.balance, result.minimum, result.first_failure_index) == (
        expected[0],
        expected[1],
        expected[2],
        expected[4],
    )
    assert not term.mahler_workspace and not term.audit_snapshot().segments_ready
    assert (
        term.ledger.counters["antihydra_arithmetic_temporal_punctured_event_actions"]
        == event_actions
    )
    assert associated_action(result)["first_failure"] == 2
    assert (
        term.ledger.counters["antihydra_arithmetic_temporal_punctured_event_actions"]
        == event_actions
    )
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
    workspace = AntihydraArithmeticTerm(0).arithmetic_image()
    source = append_source(
        workspace, DyadicReturnSourceRecord(h, width, 0, None, None, None, 0, True)
    )
    image = workspace.scheduler.source_image(
        workspace, source, workspace.action_for_extent(width)
    )
    view = workspace.scheduler.source_image_core().view(image)
    expected = literal_antihydra_summary(h, width)[4]
    assert expected is not None and expected > 0

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("first-failure consumer replayed punctured events")

    monkeypatch.setattr(workspace, "punctured_steps", forbidden)
    monkeypatch.setattr(workspace, "source_value", forbidden)
    assert workspace.first_failure(view) == expected
    assert not workspace.demanded_support


def test_punctured_power_budget_releases_transient_workspace() -> None:
    term = AntihydraArithmeticTerm(0)
    workspace = term.arithmetic_image()
    ledger = term.ledger
    scratch = RunArithmeticWorkspace.for_ledger(ledger, workspace.counter_prefix)
    before = ledger.entries, ledger.nodes
    ledger.max_nodes = ledger.nodes + 23
    with pytest.raises(BlockContextBudgetExceeded), scratch.scope():
        tuple(workspace.punctured_steps((5 << 31) + 1, 32, scratch))
    assert (ledger.entries, ledger.nodes) == before
    assert scratch.nodes == 0 and not scratch.active

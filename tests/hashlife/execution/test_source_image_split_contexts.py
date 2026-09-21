"""Child-local execution must reconstruct, rather than replace, its parent."""

from __future__ import annotations

from dataclasses import replace

import pytest

from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundSchedulerCore,
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageView,
)
from number_compiler.resources.ledger import ResourceLedger
from tests.hashlife.execution.test_source_bound_images import _Action, _DecimalAdapter


class _SplitDecimal(_DecimalAdapter):
    def admitted_input_key(self, action: object, source: SourceImageView) -> None:
        self.validate_action(action)
        self.validate_payload(source.payload)

    def first_child_source(
        self,
        parent_action: object,
        parent_source: SourceImageView,
        before_action: object,
        after_action: object,
    ) -> int:
        assert self.compose_actions(before_action, after_action) == parent_action
        self.validate_payload(parent_source.payload)
        return 0

    def second_child_source(
        self,
        parent_action: object,
        parent_source: SourceImageView,
        before_result: SourceImageView,
        after_action: object,
    ) -> int:
        children = self.action_children(parent_action)
        assert children is not None
        assert before_result.binding.source == 0
        assert before_result.binding.action == children[0]
        assert after_action == children[1]
        self.validate_payload(parent_source.payload)
        return 0

    def compose_chronological(
        self,
        action: object,
        source: SourceImageView,
        before: SourceImageView,
        after: SourceImageView,
    ) -> SourceImageCandidate:
        assert type(action) is _Action
        children = self.action_children(action)
        assert children is not None
        assert before.binding.action == children[0]
        assert after.binding.action == children[1]
        assert before.binding.source == after.binding.source == 0
        assert type(source.payload) is int
        assert type(before.payload) is int
        assert type(after.payload) is int
        value = (
            source.payload * 10 ** len(action.digits)
            + before.payload * 10 ** len(children[1].digits)
            + after.payload
        )
        return SourceImageCandidate(value, 1, (value % 2, value % 3), radix=10)


def test_split_contexts_keep_local_children_and_exact_parent_binding() -> None:
    ledger = ResourceLedger()
    core = SourceBoundSchedulerCore(ledger)
    adapter = _SplitDecimal(ledger)
    core.register(adapter)
    action = _Action((2, 4, 6, 8))
    first = core.apply(adapter, 7, action)
    assert core.projection(adapter, first, SourceImageDemand("value")).value == 72468
    assert core.view(first).binding.source == 7
    assert core.view(first).binding.action == action
    assert ledger.counters["source_image_first_child_contexts"] == 3
    assert ledger.counters["source_image_second_child_contexts"] == 3
    calls = adapter.primitive_calls
    assert core.apply(adapter, 7, action) == first
    second = core.apply(adapter, 9, action)
    assert core.view(second).payload == 92468
    assert adapter.primitive_calls == calls


def test_split_context_rejection_releases_shared_work_stack(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    core = SourceBoundSchedulerCore(ledger)
    adapter = _SplitDecimal(ledger)
    core.register(adapter)

    def invalid(*_args: object) -> int:
        return -1

    monkeypatch.setattr(adapter, "second_child_source", invalid)
    with pytest.raises(ValueError, match="invalid decimal source"):
        core.apply(adapter, 7, _Action((2, 4)))
    workspace = next(
        row for row in ledger.inventory() if row.role == "source_image_workspace"
    )
    assert workspace.entries == workspace.nodes == 0
    assert not any(key.action == _Action((2, 4)) for key in core._applications)


def test_split_contexts_do_not_discard_a_guarded_failure() -> None:
    class FailingSource(_SplitDecimal):
        def admit_source(self, source: object) -> SourceImageCandidate:
            return replace(super().admit_source(source), failure_prefix=0)

    ledger = ResourceLedger()
    core = SourceBoundSchedulerCore(ledger)
    adapter = FailingSource(ledger)
    core.register(adapter)
    with pytest.raises(ValueError, match="guarded failure"):
        core.apply(adapter, 7, _Action((2, 4)))
    assert adapter.primitive_calls == 0
    assert not core._applications

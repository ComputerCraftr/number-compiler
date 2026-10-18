from __future__ import annotations

from dataclasses import dataclass

import pytest

from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundSchedulerCore,
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageID,
    SourceImageProjection,
    SourceImageView,
    _ImageRecord,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.source_bound_payload_audit import (
    SourceBoundPayloadAudit,
    audit_source_bound_payloads,
)


@dataclass(frozen=True, slots=True)
class _Action:
    digits: tuple[int, ...]


class _DecimalAdapter:
    family = "test-decimal"
    semantic_version = "test-decimal-v1"

    def __init__(self, ledger: ResourceLedger) -> None:
        self.ledger = ledger
        self.primitive_calls = 0
        self.projection_calls = 0

    def validate_source(self, source: object) -> None:
        if type(source) is not int or source < 0:
            raise ValueError("invalid decimal source")

    def validate_action(self, action: object) -> None:
        if type(action) is not _Action or any(
            type(digit) is not int or not 0 <= digit < 10 for digit in action.digits
        ):
            raise ValueError("invalid decimal action")

    def validate_payload(self, payload: object) -> None:
        if type(payload) is not int or payload < 0:
            raise ValueError("invalid decimal payload")

    def identity_action(self, source: object) -> _Action:
        return _Action(())

    def action_children(self, action: object) -> tuple[_Action, _Action] | None:
        self.validate_action(action)
        assert isinstance(action, _Action)
        if len(action.digits) <= 1:
            return None
        split = len(action.digits) // 2
        return _Action(action.digits[:split]), _Action(action.digits[split:])

    def compose_actions(self, before: object, after: object) -> _Action:
        self.validate_action(before)
        self.validate_action(after)
        assert isinstance(before, _Action) and isinstance(after, _Action)
        return _Action(before.digits + after.digits)

    def admit_source(self, source: object) -> SourceImageCandidate:
        self.validate_source(source)
        assert isinstance(source, int)
        return SourceImageCandidate(source, 1, (0, 0), radix=10)

    def apply_primitive(
        self, action: object, source: SourceImageView
    ) -> SourceImageCandidate:
        self.validate_action(action)
        assert isinstance(action, _Action) and len(action.digits) == 1
        assert isinstance(source.payload, int)
        previous = source.binding.action
        assert isinstance(previous, _Action)
        self.primitive_calls += 1
        value = source.payload * 10 + action.digits[0]
        failure = source.failure_prefix
        if failure is None and value == 123:
            failure = len(previous.digits)
        return SourceImageCandidate(
            value,
            1,
            (value % 2, value % 3),
            radix=10,
            failure_prefix=failure,
        )

    def compose_chronological(
        self,
        action: object,
        source: SourceImageView,
        before: SourceImageView,
        after: SourceImageView,
    ) -> SourceImageCandidate:
        self.validate_action(action)
        assert before.binding.source == source.binding.source
        return SourceImageCandidate(
            after.payload,
            after.binding.extent,
            after.binding.boundary_ports,
            after.binding.orientation,
            after.binding.radix,
            after.binding.precision,
            after.failure_prefix,
        )

    def admitted_input_key(
        self, action: object, source: SourceImageView
    ) -> object | None:
        self.validate_action(action)
        # Decimal append has one relative transfer law for every exact action.
        assert isinstance(source.payload, int)
        return 0

    def transport_reuse(
        self,
        action: object,
        cached_source: SourceImageView,
        cached_result: SourceImageView,
        source: SourceImageView,
    ) -> SourceImageCandidate:
        self.validate_action(action)
        assert isinstance(action, _Action)
        assert isinstance(source.payload, int)
        # This adapter only admits relative reuse for a one-digit source state.
        value = source.payload
        for digit in action.digits:
            value = value * 10 + digit
        assert cached_source.binding.source == cached_result.binding.source
        return SourceImageCandidate(
            value,
            cached_result.binding.extent,
            (value % 2, value % 3),
            cached_result.binding.orientation,
            cached_result.binding.radix,
            cached_result.binding.precision,
            cached_result.failure_prefix,
        )

    def project(
        self, image: SourceImageView, demand: SourceImageDemand
    ) -> SourceImageProjection:
        self.projection_calls += 1
        if demand.name != "value":
            raise ValueError("unsupported projection")
        return SourceImageProjection(image.payload)

    def first_failure(self, image: SourceImageView) -> object | None:
        return (
            None
            if image.failure_prefix is None
            else (image.failure_prefix, image.payload)
        )


def _runtime(
    *, max_nodes: int | None = None, max_entries: int | None = None
) -> tuple[ResourceLedger, SourceBoundSchedulerCore, _DecimalAdapter]:
    ledger = ResourceLedger(max_nodes=max_nodes, max_cache_entries=max_entries)
    core = SourceBoundSchedulerCore(ledger)
    adapter = _DecimalAdapter(ledger)
    core.register(adapter)
    return ledger, core, adapter


def _source_audit(
    ledger: ResourceLedger, core: SourceBoundSchedulerCore
) -> SourceBoundPayloadAudit:
    return audit_source_bound_payloads(
        ledger,
        (core,),
        dict(ledger.iter_containers()),
    )


def one_image() -> tuple[
    ResourceLedger,
    SourceBoundSchedulerCore,
    _DecimalAdapter,
    SourceImageID,
    _ImageRecord,
]:
    ledger, core, adapter = _runtime()
    image = core.apply(adapter, 0, _Action((1,)))
    return ledger, core, adapter, image, core.resolve(image)


def assert_budget_refusal(
    ledger: ResourceLedger, core: SourceBoundSchedulerCore, adapter: _DecimalAdapter
) -> None:
    before = ledger.snapshot()
    with pytest.raises(Exception, match="budget exceeded"):
        core.apply(adapter, 0, _Action((1,)))
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)

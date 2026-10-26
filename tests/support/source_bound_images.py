from __future__ import annotations

from dataclasses import dataclass

import pytest

from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundSchedulerCore,
    SourceImageRecord,
)
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageID,
    SourceImageProjection,
    SourceImageView,
)
from number_compiler.resources.ledger import LedgerSnapshot, ResourceLedger
from number_compiler.resources.source_bound_payload_audit import (
    SourceBoundPayloadAudit,
    audit_source_bound_payloads,
)


@dataclass(frozen=True, slots=True)
class DecimalImageAction:
    digits: tuple[int, ...]


class DecimalImageAdapter:
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
        if type(action) is not DecimalImageAction or any(
            type(digit) is not int or not 0 <= digit < 10 for digit in action.digits
        ):
            raise ValueError("invalid decimal action")

    def validate_payload(self, payload: object) -> None:
        if type(payload) is not int or payload < 0:
            raise ValueError("invalid decimal payload")

    def identity_action(self, source: object) -> DecimalImageAction:
        return DecimalImageAction(())

    def action_children(
        self, action: object
    ) -> tuple[DecimalImageAction, DecimalImageAction] | None:
        self.validate_action(action)
        assert isinstance(action, DecimalImageAction)
        if len(action.digits) <= 1:
            return None
        split = len(action.digits) // 2
        return DecimalImageAction(action.digits[:split]), DecimalImageAction(
            action.digits[split:]
        )

    def compose_actions(self, before: object, after: object) -> DecimalImageAction:
        self.validate_action(before)
        self.validate_action(after)
        assert isinstance(before, DecimalImageAction) and isinstance(
            after, DecimalImageAction
        )
        return DecimalImageAction(before.digits + after.digits)

    def admit_source(self, source: object) -> SourceImageCandidate:
        self.validate_source(source)
        assert isinstance(source, int)
        return SourceImageCandidate(source, 1, (0, 0), radix=10)

    def apply_primitive(
        self, action: object, source: SourceImageView
    ) -> SourceImageCandidate:
        self.validate_action(action)
        assert isinstance(action, DecimalImageAction) and len(action.digits) == 1
        assert isinstance(source.payload, int)
        previous = source.binding.action
        assert isinstance(previous, DecimalImageAction)
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
        assert isinstance(action, DecimalImageAction)
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


def source_image_runtime(
    *, max_nodes: int | None = None, max_entries: int | None = None
) -> tuple[ResourceLedger, SourceBoundSchedulerCore, DecimalImageAdapter]:
    ledger = ResourceLedger(max_nodes=max_nodes, max_cache_entries=max_entries)
    core = SourceBoundSchedulerCore(ledger)
    adapter = DecimalImageAdapter(ledger)
    core.register(adapter)
    return ledger, core, adapter


def source_audit(
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
    DecimalImageAdapter,
    SourceImageID,
    SourceImageRecord,
]:
    ledger, core, adapter = source_image_runtime()
    image = core.apply(adapter, 0, DecimalImageAction((1,)))
    return ledger, core, adapter, image, core.resolve(image)


def assert_budget_refusal(
    ledger: ResourceLedger, core: SourceBoundSchedulerCore, adapter: DecimalImageAdapter
) -> None:
    before = ledger.snapshot()
    with pytest.raises(Exception, match="budget exceeded"):
        core.apply(adapter, 0, DecimalImageAction((1,)))
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)


def assert_publication_retry_committed(
    ledger: ResourceLedger,
    before: LedgerSnapshot,
    counters: tuple[str, ...],
    core: SourceBoundSchedulerCore,
) -> None:
    after_retry = ledger.snapshot()
    for counter in counters:
        assert after_retry.counters[counter] == before.counters[counter] + 1
    assert not source_audit(ledger, core).invalid

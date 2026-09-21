"""Source-bound execution adapter for exact associated scalar actions."""

from __future__ import annotations

from collections.abc import Hashable
from dataclasses import dataclass

from number_compiler.arithmetic.fields.consumer_pullback import (
    ZERO,
    AssociatedActionArena,
    AssociatedActionID,
    ExactRational,
    ThresholdDemand,
)
from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundImageAdapter,
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageProjection,
    SourceImageView,
)
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class AssociatedScalarSource:
    """An exact scalar origin and optional invariant threshold demand.

    ``None`` is positive infinity.  A threshold stored here makes first-failure
    metadata part of the source identity rather than a projection side effect.
    """

    value: ExactRational | None
    threshold: ThresholdDemand | None = None

    def __post_init__(self) -> None:
        if self.value is not None and type(self.value) is not ExactRational:
            raise TypeError("associated scalar source requires an exact value")
        if self.threshold is not None and type(self.threshold) is not ThresholdDemand:
            raise TypeError("associated scalar threshold requires an exact demand")
        if self.value is not None:
            self.value.validate()
        if self.threshold is not None:
            self.threshold.__post_init__()


@dataclass(frozen=True, slots=True)
class AssociatedScalarPayload:
    """The current exact scalar for one authenticated source image."""

    value: ExactRational | None

    def __post_init__(self) -> None:
        if self.value is not None and type(self.value) is not ExactRational:
            raise TypeError("associated scalar payload requires an exact value")
        if self.value is not None:
            self.value.validate()


class AssociatedActionSourceAdapter(SourceBoundImageAdapter):
    """Lawful exact adapter executed only through the shared tile scheduler."""

    family = "associated-affine-scalar"
    semantic_version = "associated-affine-scalar-v1"

    def __init__(self, arena: AssociatedActionArena) -> None:
        if type(arena) is not AssociatedActionArena:
            raise TypeError("associated scalar adapter requires its action arena")
        self.arena = arena
        self.ledger: ResourceLedger = arena.ledger

    def validate_source(self, source: Hashable) -> None:
        if type(source) is not AssociatedScalarSource:
            raise TypeError("associated scalar adapter requires its exact source")
        source.__post_init__()

    def validate_action(self, action: Hashable) -> None:
        if type(action) is not AssociatedActionID:
            raise TypeError("associated scalar adapter requires an action ID")
        self.arena.record(action)

    def validate_payload(self, payload: Hashable) -> None:
        if type(payload) is not AssociatedScalarPayload:
            raise TypeError("associated scalar adapter requires its exact payload")
        payload.__post_init__()

    def identity_action(self, source: Hashable) -> AssociatedActionID:
        self.validate_source(source)
        return self.arena.identity

    def action_children(
        self, action: Hashable
    ) -> tuple[AssociatedActionID, AssociatedActionID] | None:
        self.validate_action(action)
        assert type(action) is AssociatedActionID
        return self.arena.action_children(action)

    def compose_actions(self, before: Hashable, after: Hashable) -> AssociatedActionID:
        self.validate_action(before)
        self.validate_action(after)
        assert type(before) is AssociatedActionID
        assert type(after) is AssociatedActionID
        return self.arena.compose(before, after)

    def admit_source(self, source: Hashable) -> SourceImageCandidate:
        self.validate_source(source)
        assert type(source) is AssociatedScalarSource
        failed = source.threshold is not None and not source.threshold.evaluate(
            source.value
        )
        return SourceImageCandidate(
            AssociatedScalarPayload(source.value),
            0,
            failure_prefix=0 if failed else None,
        )

    def _candidate(
        self, action: AssociatedActionID, source: SourceImageView
    ) -> SourceImageCandidate:
        self.validate_payload(source.payload)
        assert type(source.payload) is AssociatedScalarPayload
        assert type(source.binding.source) is AssociatedScalarSource
        record = self.arena.record(action)
        value = self.arena.semantic(action).apply(source.payload.value)
        failure = source.failure_prefix
        threshold = source.binding.source.threshold
        if failure is None and threshold is not None and not threshold.evaluate(value):
            if record.children is not None:
                raise ValueError("composite first failure requires demanded descent")
            if record.logical_extent not in (0, 1):
                raise ValueError(
                    "opaque multi-step actions cannot locate their first failure"
                )
            failure = source.binding.extent + record.logical_extent
        return SourceImageCandidate(
            AssociatedScalarPayload(value),
            source.binding.extent + record.logical_extent,
            failure_prefix=failure,
        )

    def apply_primitive(
        self, action: Hashable, source: SourceImageView
    ) -> SourceImageCandidate:
        self.validate_action(action)
        assert type(action) is AssociatedActionID
        if self.arena.action_children(action) is not None:
            raise ValueError("associated primitive application received a composite")
        return self._candidate(action, source)

    def apply_composite(
        self,
        action: Hashable,
        source: SourceImageView,
        demand: SourceImageDemand | None,
    ) -> SourceImageCandidate | None:
        if demand is None:
            return None
        self.validate_action(action)
        assert type(action) is AssociatedActionID
        record = self.arena.record(action)
        if record.children is None:
            raise ValueError("associated composite application requires children")
        if source.failure_prefix is not None:
            return self._candidate(action, source)
        origin = source.binding.source
        assert type(origin) is AssociatedScalarSource
        if demand == SourceImageDemand("value") and origin.threshold is None:
            return self._candidate(action, source)
        if demand.name != "threshold" or len(demand.parameters) != 1:
            return None
        threshold = demand.parameters[0]
        if type(threshold) is not ThresholdDemand:
            raise TypeError("associated threshold projection requires an exact demand")
        if origin.threshold != threshold:
            return None
        value = self.arena.semantic(action).apply(
            source.payload.value
            if type(source.payload) is AssociatedScalarPayload
            else None
        )
        if (
            threshold.threshold == ZERO
            and threshold.strict
            and record.zero_failure_absorbing
            and threshold.evaluate(value)
        ):
            return self._candidate(action, source)
        return None

    def compose_chronological(
        self,
        action: Hashable,
        source: SourceImageView,
        before: SourceImageView,
        after: SourceImageView,
    ) -> SourceImageCandidate:
        self.validate_action(action)
        self.validate_payload(source.payload)
        self.validate_payload(before.payload)
        self.validate_payload(after.payload)
        if before.binding.extent < source.binding.extent:
            raise ValueError("associated chronology moved before its source")
        if after.binding.extent < before.binding.extent:
            raise ValueError("associated chronology moved after before")
        return SourceImageCandidate(
            after.payload,
            after.binding.extent,
            failure_prefix=after.failure_prefix,
        )

    def admitted_input_key(
        self, action: Hashable, source: SourceImageView
    ) -> Hashable | None:
        self.validate_action(action)
        self.validate_payload(source.payload)
        assert type(action) is AssociatedActionID
        assert type(source.binding.source) is AssociatedScalarSource
        if (
            self.arena.action_children(action) is not None
            and source.binding.source.threshold is not None
        ):
            return None
        return (
            source.binding.source.threshold,
            source.failure_prefix,
        )

    def transport_reuse(
        self,
        action: Hashable,
        cached_source: SourceImageView,
        cached_result: SourceImageView,
        source: SourceImageView,
    ) -> SourceImageCandidate:
        self.validate_action(action)
        self.validate_payload(cached_source.payload)
        self.validate_payload(cached_result.payload)
        self.validate_payload(source.payload)
        assert type(action) is AssociatedActionID
        return self._candidate(action, source)

    def project(
        self, image: SourceImageView, demand: SourceImageDemand
    ) -> SourceImageProjection:
        self.validate_payload(image.payload)
        assert type(image.payload) is AssociatedScalarPayload
        if demand == SourceImageDemand("value"):
            return SourceImageProjection(image.payload.value)
        if demand.name == "threshold" and len(demand.parameters) == 1:
            threshold = demand.parameters[0]
            if type(threshold) is not ThresholdDemand:
                raise TypeError(
                    "associated threshold projection requires an exact demand"
                )
            return SourceImageProjection(threshold.evaluate(image.payload.value))
        raise ValueError("unsupported associated scalar image demand")

    def first_failure(self, image: SourceImageView) -> int | None:
        self.validate_payload(image.payload)
        return image.failure_prefix


__all__ = [
    "AssociatedActionSourceAdapter",
    "AssociatedScalarPayload",
    "AssociatedScalarSource",
]

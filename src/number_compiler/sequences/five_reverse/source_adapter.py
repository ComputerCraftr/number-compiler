"""Five-reversal source images hosted by the shared TileScheduler."""

from __future__ import annotations

from collections.abc import Hashable
from dataclasses import dataclass
from enum import StrEnum
from typing import TYPE_CHECKING, Final, cast

from number_compiler.arithmetic.contracts.family_identity import FamilyId
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageBinding,
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageID,
    SourceImageProjection,
    SourceImageView,
)
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from .term import FiveReverseTerm


FIVE_REVERSE_IMAGE_VERSION: Final[str] = "five-reverse-decimal-source-v1"
# Matched source-owner measurements show savings beginning at this horizon.
_MIN_PACKED_STEPS: Final = 64


@dataclass(frozen=True, slots=True, eq=False)
class FiveReverseSource:
    issuer: ArenaToken
    seed: int


@dataclass(frozen=True, slots=True)
class FiveReverseAction:
    steps: int

    def __post_init__(self) -> None:
        if type(self.steps) is not int or self.steps < 0:
            raise ValueError("five-reversal action needs nonnegative physical ticks")


class FiveReverseDemand(StrEnum):
    VALUE = "five-reversal-value"
    PORT = "five-reversal-port"


class FiveReverseSourceAdapter:
    """Family transition rules for scheduler-owned bounded exact images.

    The composite route applies the actual bounded recurrence to the admitted
    source once. It does not claim a logarithmic full-integer powering law.
    """

    family = FamilyId.FIVE_REVERSE.value
    semantic_version = FIVE_REVERSE_IMAGE_VERSION

    def __init__(
        self,
        term: FiveReverseTerm,
        ledger: ResourceLedger,
        source: FiveReverseSource,
        issuer: ArenaToken,
    ) -> None:
        from .term import FiveReverseTerm

        if type(term) is not FiveReverseTerm or type(ledger) is not ResourceLedger:
            raise TypeError("five-reversal adapter needs its exact term and ledger")
        if type(source) is not FiveReverseSource or source.issuer is not issuer:
            raise TypeError("five-reversal adapter source has another issuer")
        self.term = term
        self.ledger = ledger
        self.source = source
        self.issuer = issuer

    def validate_source(self, source: object) -> None:
        if (
            type(source) is not FiveReverseSource
            or source is not self.source
            or source.issuer is not self.issuer
            or type(source.seed) is not int
            or source.seed < 0
            or source.seed != self.term.seed
        ):
            raise ValueError("five-reversal source is foreign or malformed")

    def validate_action(self, action: object) -> None:
        if type(action) is not FiveReverseAction:
            raise TypeError("five-reversal action has the wrong type")
        if (
            type(action.steps) is not int
            or not 0 <= action.steps <= self.term.max_steps
        ):
            raise ValueError("five-reversal action exceeds its admitted horizon")

    def validate_payload(self, payload: object) -> None:
        if type(payload) is not int or payload < 0:
            raise TypeError("five-reversal image payload must be a nonnegative integer")
        if payload.bit_length() > self.term.max_state_bits:
            raise ValueError("five-reversal image exceeds the admitted state-bit bound")

    def identity_action(self, source: object) -> FiveReverseAction:
        self.term.check_open()
        self.validate_source(source)
        return FiveReverseAction(0)

    def action_children(
        self, action: object
    ) -> tuple[FiveReverseAction, FiveReverseAction] | None:
        self.validate_action(action)
        exact = cast(FiveReverseAction, action)
        if exact.steps < 2:
            return None
        first = exact.steps // 2
        return FiveReverseAction(first), FiveReverseAction(exact.steps - first)

    def compose_actions(self, before: object, after: object) -> FiveReverseAction:
        self.validate_action(before)
        self.validate_action(after)
        total = (
            cast(FiveReverseAction, before).steps + cast(FiveReverseAction, after).steps
        )
        self.validate_action(FiveReverseAction(total))
        return FiveReverseAction(total)

    def admit_source(self, source: object) -> SourceImageCandidate:
        self.term.check_open()
        self.validate_source(source)
        exact = cast(FiveReverseSource, source)
        return self._candidate(exact.seed, FiveReverseAction(0))

    def apply_primitive(
        self, action: Hashable, source: SourceImageView
    ) -> SourceImageCandidate:
        self.validate_action(action)
        self._validate_view_source(source)
        exact_action = cast(FiveReverseAction, action)
        if exact_action.steps not in (0, 1):
            raise ValueError("five-reversal primitive must be identity or one tick")
        cumulative = self.compose_actions(source.binding.action, exact_action)
        return self._candidate(
            self._apply_steps(cast(int, source.payload), exact_action.steps),
            cumulative,
        )

    def compose_chronological(
        self,
        action: object,
        source: SourceImageView,
        before: SourceImageView,
        after: SourceImageView,
    ) -> SourceImageCandidate:
        self.validate_action(action)
        self._validate_view_source(source)
        self._validate_view_image(before)
        self._validate_view_image(after)
        if before.binding.source is not source.binding.source:
            raise ValueError("five-reversal before image is detached from its source")
        if after.binding.source is not source.binding.source:
            raise ValueError("five-reversal after image is detached from its source")
        children = self.action_children(action)
        if children is None:
            raise ValueError(
                "five-reversal chronological composition needs two children"
            )
        if before.binding.action != self.compose_actions(
            source.binding.action, children[0]
        ):
            raise ValueError("five-reversal before action is detached from its parent")
        if after.binding.action != self.compose_actions(
            before.binding.action, children[1]
        ):
            raise ValueError("five-reversal after action is detached from its parent")
        expected = self.compose_actions(source.binding.action, action)
        if after.binding.action != expected:
            raise ValueError(
                "five-reversal child actions do not compose chronologically"
            )
        return self._candidate(cast(int, after.payload), expected)

    def admitted_input_key(
        self, action: Hashable, source: SourceImageView
    ) -> Hashable | None:
        self.validate_action(action)
        self._validate_view_source(source)
        return source.payload

    def transport_reuse(
        self,
        action: object,
        cached_source: SourceImageView,
        cached_result: SourceImageView,
        source: SourceImageView,
    ) -> SourceImageCandidate:
        self.validate_action(action)
        self._validate_view_image(cached_source)
        self._validate_view_source(source)
        self._validate_view_image(cached_result)
        if cached_source.payload != source.payload:
            raise ValueError("five-reversal relative reuse has another exact source")
        if cached_result.binding.source is not cached_source.binding.source:
            raise ValueError("five-reversal cached result is detached from its source")
        cached_expected = self.compose_actions(cached_source.binding.action, action)
        if cached_result.binding.action != cached_expected:
            raise ValueError("five-reversal relative result has another action")
        receiver_expected = self.compose_actions(source.binding.action, action)
        return self._candidate(cast(int, cached_result.payload), receiver_expected)

    def project(
        self, image: SourceImageView, demand: SourceImageDemand
    ) -> SourceImageProjection:
        self._validate_view_image(image)
        if type(demand) is not SourceImageDemand:
            raise TypeError("five-reversal projection needs a typed demand")
        if demand.parameters:
            raise ValueError("five-reversal projection does not accept parameters")
        try:
            kind = FiveReverseDemand(demand.name)
        except ValueError as error:
            raise ValueError("unknown five-reversal source-image demand") from error
        if kind is FiveReverseDemand.VALUE:
            return SourceImageProjection(image.payload)
        if kind is FiveReverseDemand.PORT:
            return SourceImageProjection(
                self.term.source_port(cast(int, image.payload))
            )
        raise AssertionError("unreachable five-reversal demand")

    def first_failure(self, image: SourceImageView) -> object | None:
        self._validate_view_image(image)
        return None

    def apply_composite(
        self,
        action: Hashable,
        source: SourceImageView,
        demand: SourceImageDemand | None,
    ) -> SourceImageCandidate | None:
        del demand
        self.validate_action(action)
        self._validate_view_source(source)
        exact = cast(FiveReverseAction, action)
        cumulative = self.compose_actions(source.binding.action, exact)
        return self._candidate(
            self._apply_steps(cast(int, source.payload), exact.steps), cumulative
        )

    def _apply_steps(self, source: int, steps: int) -> int:
        self.validate_payload(source)
        if (
            steps >= _MIN_PACKED_STEPS
            and self.ledger.max_nodes is None
            and self.ledger.max_cache_entries is None
        ):
            return self.term.packed_value(source, steps)
        value = source
        for _ in range(steps):
            value = self.term.step_value(value)
        return value

    def padded_source_candidate(
        self, action: Hashable, source: SourceImageView
    ) -> SourceImageCandidate:
        """Compile an explicit candidate from this owner's initial source."""
        self.validate_action(action)
        self._validate_view_source(source)
        if (
            source.binding.action != FiveReverseAction(0)
            or source.payload != self.source.seed
        ):
            raise ValueError("padded action requires its original source image")
        exact = cast(FiveReverseAction, action)
        return self._candidate(self.term.padded_source_value(exact.steps), exact)

    def _candidate(self, value: int, action: FiveReverseAction) -> SourceImageCandidate:
        self.validate_payload(value)
        self.validate_action(action)
        port = self.term.source_port(value)
        return SourceImageCandidate(
            payload=value,
            extent=action.steps,
            boundary_ports=(port.high_digits, port.low_digits, port.residue45),
            orientation=1,
            radix=10,
            precision=port.decimal_width,
        )

    def _validate_view_source(self, view: SourceImageView) -> None:
        self._validate_view_image(view)
        if view.binding.source is not self.source:
            raise ValueError("five-reversal source image belongs to another source")

    def _validate_view_image(self, view: SourceImageView) -> None:
        self.term.check_open()
        if (
            type(view) is not SourceImageView
            or type(view.identity) is not SourceImageID
        ):
            raise TypeError(
                "five-reversal operation needs an authenticated scheduler view"
            )
        self.term.require_issued_view(view)
        binding = view.binding
        if type(binding) is not SourceImageBinding or binding.family != self.family:
            raise ValueError("five-reversal source image belongs to another family")
        if binding.semantic_version != self.semantic_version:
            raise ValueError("five-reversal source image has another semantic version")
        self.validate_source(binding.source)
        if type(binding.action) is not FiveReverseAction:
            raise TypeError("five-reversal image has an unknown action identity")
        action = binding.action
        self.validate_action(action)
        self.validate_payload(view.payload)
        payload = cast(int, view.payload)
        port = self.term.source_port(payload)
        if (
            view.failure_prefix is not None
            or binding.extent != action.steps
            or binding.boundary_ports
            != (port.high_digits, port.low_digits, port.residue45)
            or binding.orientation != 1
            or binding.radix != 10
            or binding.precision != port.decimal_width
        ):
            raise ValueError("five-reversal image binding is inconsistent")

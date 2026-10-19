"""Source-bound scheduler adapter for fresh-prime successor actions."""

from __future__ import annotations

from collections.abc import Hashable
from typing import cast

from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundImageAdapter,
)
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageBinding,
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageProjection,
    SourceImageView,
)
from number_compiler.resources.metric_keys import prime as _prime_keys
from number_compiler.sequences.prime.successor_action import PrimeSuccessorActionArena
from number_compiler.sequences.prime.successor_action_contracts import (
    PRIME_SUCCESSOR_WHEEL_VERSION,
    PrimeSuccessorActionID,
    PrimeSuccessorDescriptorID,
    PrimeSuccessorImagePayload,
    PrimeSuccessorPortEffect,
    PrimeSuccessorSource,
)


class PrimeSuccessorImageAdapter(SourceBoundImageAdapter):
    """Connect fresh-prime actions to the shared chronological image owner."""

    family = "prime"
    semantic_version = PRIME_SUCCESSOR_WHEEL_VERSION

    def __init__(self, arena: PrimeSuccessorActionArena) -> None:
        if type(arena) is not PrimeSuccessorActionArena:
            raise TypeError("prime image adapter requires its action arena")
        self.arena = arena
        self.ledger = arena.rank.ledger

    def _charge(self) -> None:
        self.arena.validate_open()
        self.arena.rank.charge()
        self.ledger.bump(_prime_keys.PRIME_SUCCESSOR_SCHEDULER_WORK)

    def _check_capacity(self, additional: int) -> None:
        maximum = self.arena.rank.max_states
        retained = self.ledger.entries - self.arena.rank.factor_count
        if maximum is not None and retained + additional > maximum:
            raise ValueError("prime state budget exceeded (--max-prime-states)")

    def validate_source(self, source: Hashable) -> None:
        self._charge()
        if type(source) is not PrimeSuccessorSource:
            raise TypeError("prime successor image requires its exact source")
        try:
            self.arena.validate_descriptor(source.descriptor)
        except (TypeError, ValueError) as error:
            raise ValueError(
                "prime successor source belongs to another descriptor"
            ) from error
        if not 0 <= source.entering_phase < self.arena.descriptor.fresh_prime:
            raise ValueError("prime successor source phase is not canonical")

    def validate_action(self, action: Hashable) -> None:
        self._charge()
        if type(action) is not PrimeSuccessorActionID:
            raise TypeError("prime successor image requires a scoped action")
        self.arena.node(action)

    def validate_payload(self, payload: Hashable) -> None:
        self._charge()
        if type(payload) is not PrimeSuccessorImagePayload:
            raise TypeError("prime successor image has another payload sort")
        self.arena.validate_descriptor(payload.descriptor)
        node = self.arena.node(payload.action)
        q = self.arena.descriptor.fresh_prime
        from number_compiler.sequences.prime.payload_audit import (
            validate_prime_payload_fields,
        )

        validate_prime_payload_fields(payload, node.width, q)

    def audit_image_binding(
        self,
        binding: SourceImageBinding,
        payload: object,
        failure_prefix: Hashable | None,
    ) -> None:
        from number_compiler.sequences.prime.payload_audit import (
            audit_prime_image_binding,
        )

        audit_prime_image_binding(self, binding, payload, failure_prefix)

    def identity_action(self, source: Hashable) -> PrimeSuccessorActionID:
        self.validate_source(source)
        return self.arena.identity

    def action_children(
        self, action: Hashable
    ) -> tuple[PrimeSuccessorActionID, PrimeSuccessorActionID] | None:
        self.validate_action(action)
        node = self.arena.node(cast(PrimeSuccessorActionID, action))
        if node.before is None or node.after is None:
            return None
        return node.before, node.after

    def compose_actions(
        self, before: Hashable, after: Hashable
    ) -> PrimeSuccessorActionID:
        self.validate_action(before)
        self.validate_action(after)
        return self.arena.compose(
            cast(PrimeSuccessorActionID, before),
            cast(PrimeSuccessorActionID, after),
        )

    def admit_source(self, source: Hashable) -> SourceImageCandidate:
        self.validate_source(source)
        exact_source = cast(PrimeSuccessorSource, source)
        payload = PrimeSuccessorImagePayload(
            self.arena.descriptor_id,
            self.arena.identity,
            exact_source.entering_phase,
            exact_source.entering_phase,
            0,
            0,
            0,
        )
        self._check_capacity(3)
        return SourceImageCandidate(
            payload, 0, (exact_source.entering_phase, exact_source.entering_phase)
        )

    def apply_primitive(
        self, action: Hashable, source: SourceImageView
    ) -> SourceImageCandidate:
        self.validate_action(action)
        self.validate_payload(source.payload)
        payload = cast(PrimeSuccessorImagePayload, source.payload)
        exact_action = cast(PrimeSuccessorActionID, action)
        node = self.arena.node(exact_action)
        if not node.identity and not node.primitive:
            raise ValueError("shared scheduler must refine composite prime actions")
        if (
            node.width == self.arena.descriptor.parent_period
            and source.binding.extent % self.arena.descriptor.parent_period == 0
        ):
            effect = self.arena.port_effect(exact_action, payload.outgoing_phase)
        else:
            effect = self.arena.interval_effect(
                source.binding.extent, node.width, payload.outgoing_phase
            )
        cumulative = self.arena.compose(payload.action, exact_action)
        result = PrimeSuccessorImagePayload(
            self.arena.descriptor_id,
            cumulative,
            payload.entering_phase,
            effect.outgoing_phase,
            payload.parent_survivors + effect.parent_survivors,
            payload.deleted_survivors + effect.deleted_survivors,
            payload.surviving_values + effect.surviving_values,
        )
        if node.primitive:
            self.ledger.bump(_prime_keys.PRIME_PARTIAL_SUCCESSOR_FILTERS)
        self._check_capacity(4)
        return SourceImageCandidate(
            result,
            source.binding.extent + node.width,
            (result.entering_phase, result.outgoing_phase),
        )

    def apply_composite(
        self,
        action: Hashable,
        source: SourceImageView,
        demand: SourceImageDemand | None,
    ) -> SourceImageCandidate | None:
        """Admit the exact zero-phase fresh-prime specialization as one image."""
        self.validate_action(action)
        self.validate_payload(source.payload)
        payload = cast(PrimeSuccessorImagePayload, source.payload)
        exact_action = cast(PrimeSuccessorActionID, action)
        node = self.arena.node(exact_action)
        if (
            demand is None
            or node.primitive
            or node.identity
            or payload.outgoing_phase != 0
            or self.arena.descriptor.forbidden_residues != (0,)
            or demand.name != "rank-before"
            or len(demand.parameters) != 1
        ):
            return None
        width = node.width
        effect = self.arena.interval_effect(
            source.binding.extent, width, payload.outgoing_phase
        )
        cumulative = self.arena.compose(payload.action, exact_action)
        result = PrimeSuccessorImagePayload(
            self.arena.descriptor_id,
            cumulative,
            payload.entering_phase,
            effect.outgoing_phase,
            payload.parent_survivors + effect.parent_survivors,
            payload.deleted_survivors + effect.deleted_survivors,
            payload.surviving_values + effect.surviving_values,
        )
        self.ledger.bump(_prime_keys.PRIME_PARTIAL_SUCCESSOR_FILTERS)
        self._check_capacity(4)
        return SourceImageCandidate(
            result,
            source.binding.extent + width,
            (result.entering_phase, result.outgoing_phase),
        )

    def admitted_input_key(
        self, action: Hashable, source: SourceImageView
    ) -> tuple[PrimeSuccessorDescriptorID, int, int]:
        self.validate_action(action)
        self.validate_payload(source.payload)
        payload = cast(PrimeSuccessorImagePayload, source.payload)
        # Arbitrary admitted prefixes need both translation coordinates.  Equal
        # fresh-prime phase alone does not determine which parent-wheel slots
        # survive when the source extent is not parent-period aligned.
        return (
            payload.descriptor,
            payload.outgoing_phase,
            source.binding.extent % self.arena.descriptor.parent_period,
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
        old_source = cast(PrimeSuccessorImagePayload, cached_source.payload)
        old_result = cast(PrimeSuccessorImagePayload, cached_result.payload)
        new = cast(PrimeSuccessorImagePayload, source.payload)
        parent_period = self.arena.descriptor.parent_period
        if (
            old_source.outgoing_phase != new.outgoing_phase
            or cached_source.binding.extent % parent_period
            != source.binding.extent % parent_period
        ):
            raise ValueError("prime relative transfer has another incoming state")
        exact_action = cast(PrimeSuccessorActionID, action)
        cumulative = self.arena.compose(new.action, exact_action)
        result = PrimeSuccessorImagePayload(
            self.arena.descriptor_id,
            cumulative,
            new.entering_phase,
            old_result.outgoing_phase,
            new.parent_survivors
            + old_result.parent_survivors
            - old_source.parent_survivors,
            new.deleted_survivors
            + old_result.deleted_survivors
            - old_source.deleted_survivors,
            new.surviving_values
            + old_result.surviving_values
            - old_source.surviving_values,
        )
        node = self.arena.node(exact_action)
        self._check_capacity(3)
        return SourceImageCandidate(
            result,
            source.binding.extent + node.width,
            (result.entering_phase, result.outgoing_phase),
        )

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
        source_payload = cast(PrimeSuccessorImagePayload, source.payload)
        after_payload = cast(PrimeSuccessorImagePayload, after.payload)
        exact_action = cast(PrimeSuccessorActionID, action)
        node = self.arena.node(exact_action)
        if source.binding.extent % self.arena.descriptor.parent_period:
            effect = self.arena.interval_effect(
                source.binding.extent, node.width, source_payload.outgoing_phase
            )
        else:
            effect = self.arena.port_effect(exact_action, source_payload.outgoing_phase)
        if (
            after.binding.extent != source.binding.extent + node.width
            or after_payload.outgoing_phase != effect.outgoing_phase
            or after_payload.parent_survivors - source_payload.parent_survivors
            != effect.parent_survivors
            or after_payload.deleted_survivors - source_payload.deleted_survivors
            != effect.deleted_survivors
            or after_payload.surviving_values - source_payload.surviving_values
            != effect.surviving_values
        ):
            raise ValueError("prime chronological image disagrees with its action")
        self._check_capacity(4)
        return SourceImageCandidate(
            after_payload,
            after.binding.extent,
            (after_payload.entering_phase, after_payload.outgoing_phase),
        )

    def project(
        self, image: SourceImageView, demand: SourceImageDemand
    ) -> SourceImageProjection:
        self.validate_payload(image.payload)
        payload = cast(PrimeSuccessorImagePayload, image.payload)
        if demand.name == "effect" and not demand.parameters:
            self._check_capacity(2)
            self.ledger.bump(_prime_keys.PRIME_SUCCESSOR_IMAGE_EFFECT_PROJECTIONS)
            return SourceImageProjection(
                PrimeSuccessorPortEffect(
                    payload.entering_phase,
                    payload.outgoing_phase,
                    payload.parent_survivors,
                    payload.deleted_survivors,
                    payload.surviving_values,
                )
            )
        if demand.name == "rank-before" and len(demand.parameters) == 1:
            stop = demand.parameters[0]
            if type(stop) is not int:
                raise TypeError("prime rank demand must contain an integer stop")
            self._check_capacity(2)
            # The scheduler authenticates this image's publication before
            # calling the adapter. Its whole-extent rank is already part of
            # the admitted support; only interior queries need count descent.
            width = self.arena.node(payload.action).width
            if stop == 0 or stop == width:
                self.ledger.bump(
                    _prime_keys.PRIME_SUCCESSOR_IMAGE_ENDPOINT_RANK_PROJECTIONS
                )
                return SourceImageProjection(
                    0 if stop == 0 else payload.surviving_values
                )
            return SourceImageProjection(
                self.arena.rank_before(payload.action, payload.entering_phase, stop)
            )
        if demand.name == "select" and len(demand.parameters) == 1:
            rank = demand.parameters[0]
            if type(rank) is not int:
                raise TypeError("prime select demand must contain an integer rank")
            self._check_capacity(2)
            return SourceImageProjection(
                self.arena.select(payload.action, payload.entering_phase, rank)
            )
        raise ValueError("unsupported prime successor image demand")

    def first_failure(self, image: SourceImageView) -> None:
        self.validate_payload(image.payload)


__all__ = ["PrimeSuccessorImageAdapter"]

"""Finite-horizon fresh-prime images for production prime rank/select.

The source image is a parent wheel restricted to one demanded interval.  Its
primitive action adjoins the authenticated final prime ``q`` using the exact
multiplication bijection, so construction never touches the full parent period.
"""

from __future__ import annotations

from collections.abc import Hashable
from dataclasses import dataclass
from typing import NamedTuple, cast

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundImageAdapter,
    SourceBoundSchedulerCore,
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageID,
    SourceImageProjection,
    SourceImageView,
)
from number_compiler.resources.stores import LedgerDict, LedgerList
from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG


@dataclass(frozen=True, slots=True)
class PrimePartialStageID(ArenaHandle):
    """Query-scoped authority for one authenticated parent/q split."""


class _PrimePartialStage(NamedTuple):
    """Immutable snapshot issued from an append-only consecutive prefix."""

    depth: int
    fresh_prime: int
    factors: tuple[int, ...]


class _PrimeRankAuthority(NamedTuple):
    """Exact process-local owner identities captured when the adapter is issued."""

    rank: CoprimeRankDAG
    ledger: object
    factor_store: LedgerList[int]


@dataclass(frozen=True, slots=True)
class PrimePartialSource:
    stage: PrimePartialStageID
    lower: int
    upper: int


@dataclass(frozen=True, slots=True)
class PrimePartialAction:
    stage: PrimePartialStageID
    filtered: bool


@dataclass(frozen=True, slots=True)
class PrimePartialPayload:
    stage: PrimePartialStageID
    lower: int
    upper: int
    filtered: bool
    survivors: int


class PrimePartialSuccessorAdapter(SourceBoundImageAdapter):
    """Actual fresh-q operator consumed by the shared source-image scheduler."""

    family = "prime"
    semantic_version = "partial-fresh-successor-v1"

    def __init__(self, rank: CoprimeRankDAG) -> None:
        self.rank = rank
        self.ledger = rank.ledger
        self._authority = _PrimeRankAuthority(
            rank, rank.ledger, rank._factor_store_authority
        )
        self._token = ArenaToken("prime-partial-successor")
        prefix = f"prime-partial-successor-{len(self.ledger.inventory())}"
        self._stage_owner = self.ledger.register(
            prefix + "-stages", "prime_fresh_successor_stage"
        )
        self._index_owner = self.ledger.register(
            prefix + "-index", "prime_fresh_successor_stage_index"
        )
        self._stages: LedgerList[_PrimePartialStage] = self.ledger.make_list(
            self._stage_owner, append_only=True
        )
        self._by_depth: LedgerDict[int, PrimePartialStageID] = self.ledger.make_dict(
            self._index_owner
        )
        self._closed = False

    def _charge(self) -> None:
        self._check_authority()
        self.rank.charge()
        self.ledger.bump("prime_partial_successor_scheduler_work")

    def _check_authority(self) -> None:
        authority = self._authority
        if (
            self.rank is not authority.rank
            or self.ledger is not authority.ledger
            or authority.rank._factor_store_authority is not authority.factor_store
        ):
            raise ValueError("prime partial adapter lost its source authority")

    def _check_open(self) -> None:
        self._check_authority()
        if self._closed:
            raise RuntimeError("prime partial successor adapter is closed")

    def _check_capacity(self, additional: int) -> None:
        maximum = self.rank.max_states
        retained = self.ledger.entries - self.rank.factor_count
        if maximum is not None and retained + additional > maximum:
            raise ValueError("prime state budget exceeded (--max-prime-states)")

    def stage(self, depth: int) -> PrimePartialStageID:
        self._check_open()
        if type(depth) is not int or not 1 <= depth <= self.rank.factor_count:
            raise ValueError("prime partial stage depth is outside the source")
        found = self._by_depth.get(depth)
        if found is not None:
            self._stage(found)
            return found
        self.rank.validate_consecutive_prefix(depth)
        self._check_capacity(2)
        factors = self.rank.primes[:depth]
        record = _PrimePartialStage(depth, factors[-1], factors)
        self.ledger.reserve_many(
            ((self._stage_owner, 1, 1), (self._index_owner, 1, 0))
        )
        try:
            local_id = len(self._stages)
            handle = PrimePartialStageID(
                self._token, "prime-partial-successor-stage", local_id
            )
            self._stages.append(record)
            self._by_depth[depth] = handle
        except BaseException:
            self.ledger.release(self._stage_owner, entries=1, nodes=1)
            self.ledger.release(self._index_owner, entries=1)
            raise
        return handle

    def _stage(self, stage: PrimePartialStageID) -> _PrimePartialStage:
        self._check_open()
        if type(stage) is not PrimePartialStageID:
            raise TypeError("expected a prime partial successor stage")
        stage.validate(
            self._token, "prime-partial-successor-stage", size=len(self._stages)
        )
        record = self._stages[stage.local_id]
        if (
            record.depth > self.rank.factor_count
            or record.factors[-1] != record.fresh_prime
        ):
            raise ValueError("prime partial stage lost its source binding")
        return record

    def validate_source(self, source: Hashable) -> None:
        self._charge()
        if type(source) is not PrimePartialSource:
            raise TypeError("prime partial image requires its exact source")
        self._stage(source.stage)
        if (
            type(source.lower) is not int
            or type(source.upper) is not int
            or source.lower < 1
            or source.lower > source.upper
        ):
            raise ValueError("invalid prime partial source interval")

    def validate_action(self, action: Hashable) -> None:
        self._charge()
        if type(action) is not PrimePartialAction:
            raise TypeError("prime partial image requires its exact action")
        self._stage(action.stage)
        if type(action.filtered) is not bool:
            raise TypeError("prime partial action flag must be a boolean")

    def validate_payload(self, payload: Hashable) -> None:
        self._charge()
        if type(payload) is not PrimePartialPayload:
            raise TypeError("prime partial image has another payload sort")
        self._stage(payload.stage)
        if (
            type(payload.lower) is not int
            or type(payload.upper) is not int
            or payload.lower < 1
            or payload.lower > payload.upper
            or type(payload.filtered) is not bool
            or type(payload.survivors) is not int
            or payload.survivors < 0
            or payload.survivors > payload.upper - payload.lower
        ):
            raise ValueError("invalid prime partial image payload")

    def identity_action(self, source: Hashable) -> PrimePartialAction:
        self.validate_source(source)
        return PrimePartialAction(cast(PrimePartialSource, source).stage, False)

    def action_children(
        self, action: Hashable
    ) -> tuple[Hashable, Hashable] | None:
        self.validate_action(action)
        return None

    def compose_actions(
        self, before: Hashable, after: Hashable
    ) -> PrimePartialAction:
        self.validate_action(before)
        self.validate_action(after)
        left, right = cast(PrimePartialAction, before), cast(PrimePartialAction, after)
        if left.stage != right.stage:
            raise ValueError("prime partial actions belong to different stages")
        if not left.filtered:
            return right
        if not right.filtered:
            return left
        raise ValueError("fresh-prime filter cannot be applied twice")

    def _parent_count(self, source: PrimePartialSource) -> int:
        stage = self._stage(source.stage)
        parent_depth = stage.depth - 1
        return self.rank.count(source.upper - 1, parent_depth) - self.rank.count(
            source.lower - 1, parent_depth
        )

    def admit_source(self, source: Hashable) -> SourceImageCandidate:
        self.validate_source(source)
        exact = cast(PrimePartialSource, source)
        payload = PrimePartialPayload(
            exact.stage, exact.lower, exact.upper, False, self._parent_count(exact)
        )
        # The scheduler publishes an origin node, source binding, and external
        # integrity seal after this method returns. Recheck after recurrence
        # growth, not only before.
        self._check_capacity(3)
        return SourceImageCandidate(
            payload,
            exact.upper - exact.lower,
            (exact.stage, exact.lower, exact.upper),
        )

    def apply_primitive(
        self, action: Hashable, source: SourceImageView
    ) -> SourceImageCandidate:
        self.validate_action(action)
        self.validate_payload(source.payload)
        exact_action = cast(PrimePartialAction, action)
        payload = cast(PrimePartialPayload, source.payload)
        if exact_action.stage != payload.stage:
            raise ValueError("fresh-prime action has another source stage")
        if not exact_action.filtered:
            return SourceImageCandidate(
                payload,
                payload.upper - payload.lower,
                (payload.stage, payload.lower, payload.upper),
            )
        if payload.filtered:
            raise ValueError("fresh-prime source is already filtered")
        stage = self._stage(payload.stage)
        parent_depth, q = stage.depth - 1, stage.fresh_prime
        deleted = self.rank.count((payload.upper - 1) // q, parent_depth) - (
            self.rank.count((payload.lower - 1) // q, parent_depth)
        )
        result = PrimePartialPayload(
            payload.stage,
            payload.lower,
            payload.upper,
            True,
            payload.survivors - deleted,
        )
        self.ledger.bump("prime_partial_successor_filters")
        # Application publication retains its result node, binding, and seal.
        self._check_capacity(3)
        return SourceImageCandidate(
            result,
            payload.upper - payload.lower,
            (payload.stage, payload.lower, payload.upper),
        )

    def admitted_input_key(
        self, action: Hashable, source: SourceImageView
    ) -> None:
        self.validate_action(action)
        self.validate_payload(source.payload)
        return None

    def transport_reuse(
        self,
        action: Hashable,
        cached_source: SourceImageView,
        cached_result: SourceImageView,
        source: SourceImageView,
    ) -> SourceImageCandidate:
        raise ValueError("finite prime partial images do not transport")

    def compose_chronological(
        self,
        action: Hashable,
        source: SourceImageView,
        before: SourceImageView,
        after: SourceImageView,
    ) -> SourceImageCandidate:
        raise ValueError("fresh-prime partial action has no composite children")

    def project(
        self, image: SourceImageView, demand: SourceImageDemand
    ) -> SourceImageProjection:
        self.validate_payload(image.payload)
        payload = cast(PrimePartialPayload, image.payload)
        if not payload.filtered:
            raise ValueError("prime count requires the admitted fresh-prime image")
        if demand == SourceImageDemand("survivor-count"):
            self._check_capacity(2)
            return SourceImageProjection(payload.survivors)
        if demand == SourceImageDemand("prime-count"):
            known = self.rank.factor_rank(payload.upper - 1) - self.rank.factor_rank(
                payload.lower - 1
            )
            self._check_capacity(2)
            return SourceImageProjection(payload.survivors + known)
        if demand.name == "prime-count-range" and len(demand.parameters) == 2:
            lower, upper = demand.parameters
            if (
                type(lower) is not int
                or type(upper) is not int
                or not payload.lower <= lower <= upper <= payload.upper
            ):
                raise ValueError("prime range demand lies outside its admitted image")
            if lower == payload.lower and upper == payload.upper:
                known = self.rank.factor_rank(upper - 1) - self.rank.factor_rank(
                    lower - 1
                )
                self._check_capacity(2)
                return SourceImageProjection(payload.survivors + known)
            stage = self._stage(payload.stage)
            # The admitted zero-phase/single-residue action specializes to the
            # canonical numerical Phi owner.  Use that exact specialization
            # for descendants instead of re-evaluating both sides of the
            # parent-minus-deletion identity.  The enclosing image itself was
            # still constructed by the fresh-q primitive above.
            survivors = self.rank.count(upper - 1, stage.depth) - self.rank.count(
                lower - 1, stage.depth
            )
            known = self.rank.factor_rank(upper - 1) - self.rank.factor_rank(lower - 1)
            self._check_capacity(2)
            return SourceImageProjection(survivors + known)
        raise ValueError("unsupported prime partial image demand")

    def first_failure(self, image: SourceImageView) -> None:
        self.validate_payload(image.payload)
        return None

    def close(self) -> None:
        if self._closed:
            return
        stages, indices = len(self._stages), len(self._by_depth)
        self._by_depth.clear()
        self._stages._rollback_unpublished(0)
        self.ledger.release(self._index_owner, entries=indices)
        self.ledger.release(self._stage_owner, entries=stages, nodes=stages)
        self._closed = True


class PrimePartialSuccessorQuery:
    """One production query context sharing rank source and image authority."""

    def __init__(self, rank: CoprimeRankDAG) -> None:
        self.rank = rank
        self.adapter = PrimePartialSuccessorAdapter(rank)
        self.adapter._check_capacity(1)
        self.core = SourceBoundSchedulerCore(rank.ledger)
        self.core.register(self.adapter)
        self._closed = False
        self.peak_scheduler_entries = 1
        self._last_image: SourceImageID | None = None
        self._last_stage: PrimePartialStageID | None = None
        self._last_depth = 0
        self._last_lower = self._last_upper = 0

    def count_primes(self, lower: int, upper: int, depth: int) -> int:
        if self._closed:
            raise RuntimeError("prime partial successor query is closed")
        if type(depth) is not int or depth < 1:
            raise ValueError("prime partial stage depth is outside the source")
        # A selected interval descends repeatedly through the same admitted
        # factor stage.  The core reauthenticates the source/action/payload on
        # every demand, so repeating the stage-index lookup here adds no
        # boundary check.
        stage = (
            self._last_stage
            if self._last_stage is not None and self._last_depth == depth
            else self.adapter.stage(depth)
        )
        contained = (
            self._last_image is not None
            and self._last_stage == stage
            and self._last_lower <= lower <= upper <= self._last_upper
        )
        if contained:
            image = self._last_image
            self.rank.charge()
        else:
            source = PrimePartialSource(stage, lower, upper)
            action = PrimePartialAction(stage, True)
            self.adapter._check_capacity(8)
            # Origin, application, and projection publications each retain an
            # external exact seal in addition to their prior scheduler entries.
            self.rank.charge_many(2)
            image = self.core.apply(self.adapter, source, action)
            self._last_image = image
            self._last_stage = stage
            self._last_depth = depth
            self._last_lower, self._last_upper = lower, upper
        if image is None:
            raise AssertionError("prime partial successor lost its admitted image")
        projected = self.core.projection(
            self.adapter,
            image,
            SourceImageDemand("prime-count-range", (lower, upper)),
        )
        non_scheduler = (
            self.rank.factor_count
            + len(self.rank.memo)
            + len(self.rank.progression_memo)
        )
        self.peak_scheduler_entries = max(
            self.peak_scheduler_entries, self.rank.ledger.entries - non_scheduler
        )
        if type(projected.value) is not int:
            raise RuntimeError("prime partial image returned a noninteger count")
        return projected.value

    def close(self) -> None:
        if self._closed:
            return
        self.core.dispose()
        self.adapter.close()
        self._closed = True


__all__ = [
    "PrimePartialAction",
    "PrimePartialPayload",
    "PrimePartialSource",
    "PrimePartialStageID",
    "PrimePartialSuccessorAdapter",
    "PrimePartialSuccessorQuery",
]

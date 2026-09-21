"""Exact shared scalar actions and monotone consumer pullbacks."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from math import gcd

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict, LedgerList


@dataclass(frozen=True, slots=True)
class ExactRational:
    """A normalized arbitrary-precision rational packet."""

    numerator: int
    denominator: int = 1

    def __post_init__(self) -> None:
        if type(self.numerator) is not int or type(self.denominator) is not int:
            raise TypeError("exact rational components must be integers")
        if self.denominator == 0:
            raise ValueError("exact rational denominator cannot be zero")
        divisor = gcd(self.numerator, self.denominator)
        numerator = self.numerator // divisor
        denominator = self.denominator // divisor
        if denominator < 0:
            numerator, denominator = -numerator, -denominator
        object.__setattr__(self, "numerator", numerator)
        object.__setattr__(self, "denominator", denominator)

    def validate(self) -> None:
        """Reject reflected or otherwise noncanonical coefficient packets."""
        if type(self.numerator) is not int or type(self.denominator) is not int:
            raise TypeError("exact rational components must be integers")
        if self.denominator <= 0 or gcd(self.numerator, self.denominator) != 1:
            raise ValueError("exact rational packet is not normalized")

    def _require(self, other: object) -> ExactRational:
        if type(other) is not ExactRational:
            raise TypeError("exact rational arithmetic requires exact rational packets")
        return other

    def __add__(self, other: object) -> ExactRational:
        value = self._require(other)
        return ExactRational(
            self.numerator * value.denominator + value.numerator * self.denominator,
            self.denominator * value.denominator,
        )

    def __sub__(self, other: object) -> ExactRational:
        value = self._require(other)
        return ExactRational(
            self.numerator * value.denominator - value.numerator * self.denominator,
            self.denominator * value.denominator,
        )

    def __mul__(self, other: object) -> ExactRational:
        value = self._require(other)
        return ExactRational(
            self.numerator * value.numerator,
            self.denominator * value.denominator,
        )

    def __truediv__(self, other: object) -> ExactRational:
        value = self._require(other)
        if value.numerator == 0:
            raise ZeroDivisionError("exact rational division by zero")
        return ExactRational(
            self.numerator * value.denominator,
            self.denominator * value.numerator,
        )

    def __neg__(self) -> ExactRational:
        return ExactRational(-self.numerator, self.denominator)

    def __lt__(self, other: object) -> bool:
        value = self._require(other)
        return self.numerator * value.denominator < value.numerator * self.denominator

    def __le__(self, other: object) -> bool:
        value = self._require(other)
        return self.numerator * value.denominator <= value.numerator * self.denominator

    def __gt__(self, other: object) -> bool:
        value = self._require(other)
        return self.numerator * value.denominator > value.numerator * self.denominator

    def __ge__(self, other: object) -> bool:
        value = self._require(other)
        return self.numerator * value.denominator >= value.numerator * self.denominator


ZERO = ExactRational(0)
ONE = ExactRational(1)


@dataclass(frozen=True, slots=True)
class ThresholdDemand:
    """A strict or non-strict threshold predicate on an exact scalar."""

    possible: bool = True
    threshold: ExactRational = ZERO
    strict: bool = True

    def __post_init__(self) -> None:
        if type(self.possible) is not bool or type(self.strict) is not bool:
            raise TypeError("threshold demand flags must be booleans")
        if type(self.threshold) is not ExactRational:
            raise TypeError("threshold demand requires an exact rational threshold")
        self.threshold.validate()

    def evaluate(self, value: ExactRational | None) -> bool:
        """Evaluate the demand, treating ``None`` as positive infinity."""
        if not self.possible:
            return False
        if value is None:
            return True
        if type(value) is not ExactRational:
            raise TypeError("threshold demand requires an exact rational value")
        return value > self.threshold if self.strict else value >= self.threshold


@dataclass(frozen=True, slots=True)
class SaturatingAffineAction:
    """The increasing min-plus action ``min(cap, scale*x + offset)``."""

    scale: ExactRational = ONE
    offset: ExactRational = ZERO
    cap: ExactRational | None = None

    def __post_init__(self) -> None:
        if (
            type(self.scale) is not ExactRational
            or type(self.offset) is not ExactRational
        ):
            raise TypeError("associated action coefficients must be exact rationals")
        if self.cap is not None and type(self.cap) is not ExactRational:
            raise TypeError("associated action cap must be an exact rational")
        self.scale.validate()
        self.offset.validate()
        if self.cap is not None:
            self.cap.validate()
        if self.scale <= ZERO:
            raise ValueError("associated action requires positive scale")

    @classmethod
    def identity(cls) -> SaturatingAffineAction:
        return cls()

    def apply(self, value: ExactRational | None) -> ExactRational | None:
        """Apply exactly; ``None`` denotes positive infinity."""
        if value is None:
            return self.cap
        if type(value) is not ExactRational:
            raise TypeError("associated action requires an exact rational value")
        affine = self.scale * value + self.offset
        return self.cap if self.cap is not None and self.cap < affine else affine

    def then(self, downstream: SaturatingAffineAction) -> SaturatingAffineAction:
        """Compose in temporal order: this action first, then ``downstream``."""
        if type(downstream) is not SaturatingAffineAction:
            raise TypeError("associated action composition requires exact actions")
        transported = (
            None
            if self.cap is None
            else downstream.scale * self.cap + downstream.offset
        )
        if downstream.cap is None:
            cap = transported
        elif transported is None or downstream.cap < transported:
            cap = downstream.cap
        else:
            cap = transported
        return SaturatingAffineAction(
            downstream.scale * self.scale,
            downstream.scale * self.offset + downstream.offset,
            cap,
        )

    def pullback(self, demand: ThresholdDemand) -> ThresholdDemand:
        if type(demand) is not ThresholdDemand:
            raise TypeError("associated pullback requires an exact threshold demand")
        if not demand.possible:
            return demand
        if self.cap is not None:
            impossible = (
                self.cap <= demand.threshold
                if demand.strict
                else self.cap < demand.threshold
            )
            if impossible:
                return ThresholdDemand(False, ZERO, demand.strict)
        return ThresholdDemand(
            True, (demand.threshold - self.offset) / self.scale, demand.strict
        )


def power_action(base: SaturatingAffineAction, copies: int) -> SaturatingAffineAction:
    """Power an action by iterative binary composition."""
    if type(base) is not SaturatingAffineAction:
        raise TypeError("associated action power requires an exact action")
    if type(copies) is not int or copies < 0:
        raise ValueError("associated action power must be nonnegative")
    result = SaturatingAffineAction.identity()
    while copies:
        if copies & 1:
            result = result.then(base)
        copies >>= 1
        if copies:
            base = base.then(base)
    return result


class SurvivalAggregation(Enum):
    ALL = "all"
    ANY = "any"


@dataclass(frozen=True, slots=True)
class MonotoneSurvivalClock:
    """A nonempty ALL/min or ANY/max monotone survival clock."""

    aggregation: SurvivalAggregation
    last_passing_level: int | None

    def __post_init__(self) -> None:
        if type(self.aggregation) is not SurvivalAggregation:
            raise TypeError("survival clock requires an exact aggregation")
        if self.last_passing_level is not None and (
            type(self.last_passing_level) is not int or self.last_passing_level < 0
        ):
            raise ValueError("last passing level must be nonnegative")

    @classmethod
    def from_depths(
        cls, depths: tuple[int, ...], aggregation: SurvivalAggregation
    ) -> MonotoneSurvivalClock:
        if type(depths) is not tuple:
            raise TypeError("survival depths must be an immutable tuple")
        if type(aggregation) is not SurvivalAggregation:
            raise TypeError("survival clock requires an exact aggregation")
        if any(type(depth) is not int or depth < 0 for depth in depths):
            raise ValueError("survival depths must be nonnegative integers")
        if not depths:
            return cls(aggregation, None)
        reduction = min if aggregation is SurvivalAggregation.ALL else max
        return cls(aggregation, reduction(depths))

    def output(self, level: int) -> bool:
        if type(level) is not int or level < 0:
            raise ValueError("survival level must be nonnegative")
        return self.last_passing_level is not None and level <= self.last_passing_level

    def first_failure_level(self) -> int:
        return 0 if self.last_passing_level is None else self.last_passing_level + 1


@dataclass(frozen=True, slots=True)
class AssociatedActionID(ArenaHandle):
    """Ledger-scoped identity of one action and logical extent."""


@dataclass(frozen=True, slots=True)
class AssociatedActionRecord:
    semantic_id: int
    logical_extent: int
    children: tuple[AssociatedActionID, AssociatedActionID] | None
    zero_failure_absorbing: bool


class AssociatedActionArena:
    """Ledger-owned action DAG with semantics interned apart from logical work."""

    _KIND = "associated-affine-action"

    def __init__(self, ledger: ResourceLedger) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("associated action arena requires a resource ledger")
        self.ledger = ledger
        self.owner = ArenaToken("associated-affine-actions")
        self._closed = False
        prefix = f"associated-actions-{len(ledger.inventory())}"
        self._semantic_owner = ledger.register(
            prefix + "-semantics", "associated_action_semantic"
        )
        self._semantic_key_owner = ledger.register(
            prefix + "-semantic-keys", "associated_action_interner"
        )
        self._semantic_fingerprint_owner = ledger.register(
            prefix + "-semantic-fingerprints", "associated_action_fingerprint"
        )
        self._action_owner = ledger.register(prefix + "-actions", "associated_action")
        self._action_key_owner = ledger.register(
            prefix + "-action-keys", "associated_action_interner"
        )
        self._action_fingerprint_owner = ledger.register(
            prefix + "-action-fingerprints", "associated_action_fingerprint"
        )
        self._semantics: LedgerList[SaturatingAffineAction] = ledger.make_list(
            self._semantic_owner
        )
        self._semantic_keys: LedgerDict[SaturatingAffineAction, int] = ledger.make_dict(
            self._semantic_key_owner
        )
        self._semantic_fingerprints: LedgerList[tuple[int, ...]] = ledger.make_list(
            self._semantic_fingerprint_owner, nodes_per_entry=0
        )
        self._actions: LedgerList[AssociatedActionRecord] = ledger.make_list(
            self._action_owner
        )
        self._action_keys: LedgerDict[
            tuple[
                int,
                int,
                tuple[AssociatedActionID, AssociatedActionID] | None,
            ],
            int,
        ] = ledger.make_dict(self._action_key_owner)
        self._action_fingerprints: LedgerList[tuple[int, ...]] = ledger.make_list(
            self._action_fingerprint_owner, nodes_per_entry=0
        )
        ledger.register_execution_root(self)
        try:
            self.identity = self.admit(
                SaturatingAffineAction.identity(), logical_extent=0
            )
        except BaseException:
            self.close()
            raise

    def _handle(self, local_id: int) -> AssociatedActionID:
        return AssociatedActionID(self.owner, self._KIND, local_id)

    @staticmethod
    def _semantic_fingerprint(semantic: SaturatingAffineAction) -> tuple[int, ...]:
        semantic.__post_init__()
        coefficients = (
            semantic.scale.numerator,
            semantic.scale.denominator,
            semantic.offset.numerator,
            semantic.offset.denominator,
        )
        if semantic.cap is None:
            return (*coefficients, 0)
        return (
            *coefficients,
            1,
            semantic.cap.numerator,
            semantic.cap.denominator,
        )

    def _action_fingerprint(self, record: AssociatedActionRecord) -> tuple[int, ...]:
        if (
            type(record.semantic_id) is not int
            or type(record.logical_extent) is not int
        ):
            raise TypeError("associated action record has invalid numeric metadata")
        if type(record.zero_failure_absorbing) is not bool:
            raise TypeError("associated action record has invalid recovery metadata")
        children = record.children
        if children is None:
            child_ids = -1, -1
        else:
            if type(children) is not tuple or len(children) != 2:
                raise TypeError("associated action record has malformed children")
            before, after = children
            before.validate(self.owner, self._KIND, size=len(self._actions))
            after.validate(self.owner, self._KIND, size=len(self._actions))
            child_ids = before.local_id, after.local_id
        return (
            record.semantic_id,
            record.logical_extent,
            *child_ids,
            int(record.zero_failure_absorbing),
        )

    def record(self, action: AssociatedActionID) -> AssociatedActionRecord:
        if self._closed:
            raise ValueError("disposed associated action arena")
        if type(action) is not AssociatedActionID:
            raise TypeError("expected an associated action ID")
        action.validate(self.owner, self._KIND, size=len(self._actions))
        record = self._actions[action.local_id]
        if (
            type(record) is not AssociatedActionRecord
            or self._action_fingerprint(record)
            != self._action_fingerprints[action.local_id]
            or not 0 <= record.semantic_id < len(self._semantics)
            or self._semantic_fingerprint(self._semantics[record.semantic_id])
            != self._semantic_fingerprints[record.semantic_id]
        ):
            raise ValueError("associated action publication was altered")
        return record

    def close(self) -> None:
        """Release all action stores and invalidate previously issued IDs."""
        if self._closed:
            return
        action_keys = len(self._action_keys)
        actions = len(self._actions)
        action_fingerprints = len(self._action_fingerprints)
        semantic_keys = len(self._semantic_keys)
        semantics = len(self._semantics)
        semantic_fingerprints = len(self._semantic_fingerprints)
        self._action_keys.clear()
        self._actions._rollback_unpublished(0)
        self._action_fingerprints._rollback_unpublished(0)
        self._semantic_keys.clear()
        self._semantics._rollback_unpublished(0)
        self._semantic_fingerprints._rollback_unpublished(0)
        self.ledger.release(self._action_key_owner, entries=action_keys)
        self.ledger.release(self._action_owner, entries=actions, nodes=actions)
        self.ledger.release(self._action_fingerprint_owner, entries=action_fingerprints)
        self.ledger.release(self._semantic_key_owner, entries=semantic_keys)
        self.ledger.release(self._semantic_owner, entries=semantics, nodes=semantics)
        self.ledger.release(
            self._semantic_fingerprint_owner, entries=semantic_fingerprints
        )
        for owner in (
            self._action_key_owner,
            self._action_owner,
            self._action_fingerprint_owner,
            self._semantic_key_owner,
            self._semantic_owner,
            self._semantic_fingerprint_owner,
        ):
            self.ledger.mark_disposed(owner)
        self.owner = ArenaToken("associated-affine-actions-closed")
        self._closed = True
        self.ledger.bump("associated_action_arena_closures")

    def semantic(self, action: AssociatedActionID) -> SaturatingAffineAction:
        record = self.record(action)
        return self._semantics[record.semantic_id]

    def action_children(
        self, action: AssociatedActionID
    ) -> tuple[AssociatedActionID, AssociatedActionID] | None:
        return self.record(action).children

    def admit(
        self, semantic: SaturatingAffineAction, *, logical_extent: int = 1
    ) -> AssociatedActionID:
        return self._admit(semantic, logical_extent, None, None)

    def _admit(
        self,
        semantic: SaturatingAffineAction,
        logical_extent: int,
        children: tuple[AssociatedActionID, AssociatedActionID] | None,
        zero_failure_absorbing: bool | None,
    ) -> AssociatedActionID:
        if type(semantic) is not SaturatingAffineAction:
            raise TypeError("associated action admission requires an exact action")
        semantic.__post_init__()
        if type(logical_extent) is not int or logical_extent < 0:
            raise ValueError("associated action extent must be nonnegative")
        self.ledger.bump("associated_action_admission_requests")
        semantic_id = self._semantic_keys.get(semantic)
        new_semantic = semantic_id is None
        if semantic_id is None:
            semantic_id = len(self._semantics)
        key = semantic_id, logical_extent, children
        found = self._action_keys.get(key)
        if found is not None:
            self.ledger.bump("associated_action_admission_hits")
            return self._handle(found)
        reservations = [
            (self._action_owner, 1, 1),
            (self._action_key_owner, 1, 0),
            (self._action_fingerprint_owner, 1, 0),
        ]
        if new_semantic:
            reservations.extend(
                (
                    (self._semantic_owner, 1, 1),
                    (self._semantic_key_owner, 1, 0),
                    (self._semantic_fingerprint_owner, 1, 0),
                )
            )
        self.ledger.reserve_many(reservations)
        semantic_size = len(self._semantics)
        semantic_fingerprint_size = len(self._semantic_fingerprints)
        action_size = len(self._actions)
        action_fingerprint_size = len(self._action_fingerprints)
        try:
            if new_semantic:
                self._semantics.append(semantic)
                self._semantic_fingerprints.append(self._semantic_fingerprint(semantic))
                self._semantic_keys[semantic] = semantic_id
            local_id = len(self._actions)
            absorbs = semantic.apply(ZERO)
            record = AssociatedActionRecord(
                semantic_id,
                logical_extent,
                children,
                (
                    absorbs is not None and absorbs <= ZERO
                    if zero_failure_absorbing is None
                    else zero_failure_absorbing
                ),
            )
            self._actions.append(record)
            self._action_fingerprints.append(self._action_fingerprint(record))
            self._action_keys[key] = local_id
        except BaseException:
            self._action_keys.pop(key, None)
            self._actions._rollback_unpublished(action_size)
            self._action_fingerprints._rollback_unpublished(action_fingerprint_size)
            if new_semantic:
                self._semantic_keys.pop(semantic, None)
                self._semantics._rollback_unpublished(semantic_size)
                self._semantic_fingerprints._rollback_unpublished(
                    semantic_fingerprint_size
                )
            for owner, entries, nodes in reservations:
                self.ledger.release(owner, entries=entries, nodes=nodes)
            raise
        self.ledger.bump("associated_action_admissions")
        return self._handle(local_id)

    def compose(
        self, before: AssociatedActionID, after: AssociatedActionID
    ) -> AssociatedActionID:
        before_record, after_record = self.record(before), self.record(after)
        if before == self.identity:
            return after
        if after == self.identity:
            return before
        semantic = self.semantic(before).then(self.semantic(after))
        extent = before_record.logical_extent + after_record.logical_extent
        self.ledger.bump("associated_action_composition_requests")
        semantic_id = self._semantic_keys.get(semantic)
        children = before, after
        if semantic_id is not None:
            found = self._action_keys.get((semantic_id, extent, children))
            if found is not None:
                self.ledger.bump("associated_action_composition_hits")
                return self._handle(found)
        return self._admit(
            semantic,
            extent,
            children,
            before_record.zero_failure_absorbing
            and after_record.zero_failure_absorbing,
        )

    def power(self, base: AssociatedActionID, copies: int) -> AssociatedActionID:
        self.record(base)
        if type(copies) is not int or copies < 0:
            raise ValueError("associated action power must be nonnegative")
        result = self.identity
        while copies:
            if copies & 1:
                result = self.compose(result, base)
            copies >>= 1
            if copies:
                base = self.compose(base, base)
        return result


__all__ = [
    "AssociatedActionArena",
    "AssociatedActionID",
    "AssociatedActionRecord",
    "ExactRational",
    "MonotoneSurvivalClock",
    "SaturatingAffineAction",
    "SurvivalAggregation",
    "ThresholdDemand",
    "power_action",
]

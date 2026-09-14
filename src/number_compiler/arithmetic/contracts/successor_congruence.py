"""Fail-closed contracts for semantic action caches versus exact target caches.

A reusable local operator action is *not* automatically a state quotient.  An
``ActionID`` may safely cache compiled transition work for many exact payloads,
but an exact-target cache may use that ActionID as its sole key only after the
class is proved successor-congruent:

    pi(x) = pi(y)  =>  pi(T(x)) = pi(T(y))

and, when the cache returns an exact occurrence rather than only a semantic
class, the returned exact occurrence must also be independent of the chosen
representative (or be reconstructed by a separately carried transform/payload).

This module makes that distinction explicit.  It deliberately has no sequence-
specific arithmetic; domain engines feed it canonical semantic and occurrence
keys.  The registry is an audit/proof surface, not a heuristic promotion
mechanism: observing no conflict is never treated as a global proof.
"""

from __future__ import annotations

from collections.abc import Hashable
from dataclasses import dataclass


class SuccessorCongruenceViolation(ValueError):
    """Raised when one semantic class is observed with incompatible successors."""


@dataclass(frozen=True, slots=True)
class SuccessorObservation:
    semantic_key: Hashable
    source_occurrence_key: Hashable
    target_semantic_key: Hashable
    target_occurrence_key: Hashable


@dataclass(frozen=True, slots=True)
class SuccessorCongruenceMetrics:
    observations: int
    semantic_classes: int
    semantic_aliases: int
    successor_conflicts: int
    exact_target_conflicts: int


class SuccessorCongruenceAudit:
    """Record representative-independent successor behavior for action classes.

    The audit records both semantic target class and exact target occurrence.
    ``semantic_successor_closed`` means all *observed* representatives agree on
    the next semantic class.  ``exact_target_closed`` is stronger: all observed
    representatives also agree on the exact target occurrence.  Neither flag is
    a theorem; production code must not promote it to a global cache contract
    unless a domain proof establishes completeness of the audited carrier.
    """

    __slots__ = (
        "_exact_conflict_keys",
        "_exact_target",
        "_semantic_conflict_keys",
        "_semantic_target",
        "_sources",
        "exact_target_conflicts",
        "observations",
        "semantic_aliases",
        "successor_conflicts",
    )

    def __init__(self) -> None:
        self._semantic_target: dict[Hashable, Hashable] = {}
        self._exact_target: dict[Hashable, Hashable] = {}
        self._sources: dict[Hashable, set[Hashable]] = {}
        self.observations = 0
        self.semantic_aliases = 0
        self.successor_conflicts = 0
        self.exact_target_conflicts = 0
        self._semantic_conflict_keys: set[Hashable] = set()
        self._exact_conflict_keys: set[Hashable] = set()

    def observe(self, observation: SuccessorObservation) -> None:
        if not isinstance(observation, SuccessorObservation):
            raise TypeError(type(observation))
        self.observations += 1
        key = observation.semantic_key
        sources = self._sources.setdefault(key, set())
        if observation.source_occurrence_key not in sources and sources:
            self.semantic_aliases += 1
        sources.add(observation.source_occurrence_key)

        prior_semantic = self._semantic_target.get(key)
        if prior_semantic is None:
            self._semantic_target[key] = observation.target_semantic_key
        elif (
            prior_semantic != observation.target_semantic_key
            and key not in self._semantic_conflict_keys
        ):
            self.successor_conflicts += 1
            self._semantic_conflict_keys.add(key)

        prior_exact = self._exact_target.get(key)
        if prior_exact is None:
            self._exact_target[key] = observation.target_occurrence_key
        elif (
            prior_exact != observation.target_occurrence_key
            and key not in self._exact_conflict_keys
        ):
            self.exact_target_conflicts += 1
            self._exact_conflict_keys.add(key)

    def semantic_successor_closed(self, semantic_key: Hashable) -> bool:
        """Whether no semantic successor conflict has been observed for ``key``."""
        return (
            semantic_key in self._semantic_target
            and not self._has_semantic_conflict(semantic_key)
        )

    def exact_target_closed(self, semantic_key: Hashable) -> bool:
        """Whether no exact-target conflict has been observed for ``key``."""
        return semantic_key in self._exact_target and not self._has_exact_conflict(
            semantic_key
        )

    def _has_semantic_conflict(self, semantic_key: Hashable) -> bool:
        return semantic_key in self._semantic_conflict_keys

    def _has_exact_conflict(self, semantic_key: Hashable) -> bool:
        return semantic_key in self._exact_conflict_keys

    def require_global_proof(self, *, carrier_complete: bool) -> None:
        """Validate an externally proved complete carrier before promotion.

        Sampling cannot establish a quotient theorem.  A caller may set
        ``carrier_complete=True`` only when its domain construction enumerates
        or otherwise proves the complete admissible carrier.  Conflicts always
        fail, regardless of completeness.
        """
        if self.successor_conflicts:
            raise SuccessorCongruenceViolation(
                f"semantic successor conflicts: {self.successor_conflicts}"
            )
        if not carrier_complete:
            raise SuccessorCongruenceViolation(
                "observed aliases are not a complete successor-congruence proof"
            )

    def metrics(self) -> SuccessorCongruenceMetrics:
        return SuccessorCongruenceMetrics(
            self.observations,
            len(self._sources),
            self.semantic_aliases,
            self.successor_conflicts,
            self.exact_target_conflicts,
        )


@dataclass(frozen=True, slots=True)
class ExactTargetCacheIdentity:
    """Two-layer cache identity with an explicit successor-proof bit.

    ``operator_key`` is the aggressively shared ActionID.  ``occurrence_key``
    identifies the exact payload.  ``exact_cache_key`` drops the payload only
    when the caller supplies a *proved* successor-complete class.  This prevents
    accidental use of a merely extensional one-step operator as an exact-state
    quotient.
    """

    operator_key: Hashable
    occurrence_key: Hashable
    successor_complete: bool = False

    @property
    def operator_cache_key(self) -> tuple[str, Hashable]:
        return ("semantic-operator", self.operator_key)

    @property
    def exact_cache_key(self) -> tuple[str, Hashable]:
        if self.successor_complete:
            return ("proved-successor-class", self.operator_key)
        return ("exact-occurrence", self.occurrence_key)


__all__ = [
    "ExactTargetCacheIdentity",
    "SuccessorCongruenceAudit",
    "SuccessorCongruenceMetrics",
    "SuccessorCongruenceViolation",
    "SuccessorObservation",
]

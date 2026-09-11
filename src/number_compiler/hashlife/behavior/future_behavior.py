"""Certified successor-closed behavior for quiescent primitive regions.

The certificate in this module is deliberately narrow.  It proves that a
nonempty uniform blank interval stays blank under repeated applications of one
primitive kernel, provided its incoming left state belongs to the computed
safe set.  It also identifies genuinely absorbing left states whose output is
blank for every input symbol.  No source occurrence, spatial word, temporal
power, or callback is retained by the certificate.
"""

from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.hashlife.interfaces.primitive_behavior import (
    PrimitiveBehaviorQuotient,
    validate_primitive_behavior_quotient,
)

QUIESCENT_PROFILE_VERSION = 1
QUIESCENT_OBSERVATIONS = (
    "uniform-output-symbol",
    "activity",
    "termination",
    "normalization",
    "occurrence-cocycle",
    "left-boundary-transfer",
    "right-boundary-transfer",
)
QUIESCENT_GEOMETRY_SCHEMA = "nonempty-uniform-blank-dyadic-v1"
QUIESCENT_COCYCLE_SCHEMA = "primitive-zero-occurrence-cocycle-v1"
QUIESCENT_LAW = "successor-closed-uniform-blank-v1"


class UnsupportedFutureBehaviorProfile(ValueError):
    """The finite kernel has no proof for the requested behavior profile."""


@dataclass(slots=True)
class FutureBehaviorWork:
    """Measured transient work used to establish one finite certificate."""

    observation_checks: int = 0
    successor_checks: int = 0
    refinement_rounds: int = 0


@dataclass(frozen=True, slots=True)
class FutureBehaviorProfileID(ArenaHandle):
    """Scoped identity of one immutable continuation/observation profile."""


@dataclass(frozen=True, slots=True)
class FutureBehaviorClassID(ArenaHandle):
    """Scoped identity of one completed successor-closed behavior class."""


@dataclass(frozen=True, slots=True)
class QuiescentBlankCertificate:
    """Complete finite proof for one primitive kernel's blank behavior."""

    kernel: SemanticIdentity
    continuation: SemanticIdentity
    alphabet_size: int
    blank: int
    safe_blank_left_states: tuple[int, ...]
    absorbing_blank_left_states: tuple[int, ...]
    left_blank_transition: tuple[int, ...]
    right_blank_transition: tuple[int, ...]
    refinement_rounds: int
    semantic_digest: str

    def __post_init__(self) -> None:
        for identity in (self.kernel, self.continuation):
            if type(identity) is not SemanticIdentity:
                raise TypeError("quiescent behavior requires semantic identities")
            identity.__post_init__()
        if type(self.alphabet_size) is not int or self.alphabet_size < 1:
            raise ValueError("quiescent behavior requires a finite alphabet")
        if type(self.blank) is not int or not 0 <= self.blank < self.alphabet_size:
            raise ValueError("quiescent behavior has an invalid blank symbol")
        if type(self.refinement_rounds) is not int or self.refinement_rounds < 1:
            raise ValueError("quiescent refinement must reach a fixed point")
        if any(
            type(row) is not tuple
            for row in (
                self.safe_blank_left_states,
                self.absorbing_blank_left_states,
                self.left_blank_transition,
                self.right_blank_transition,
            )
        ):
            raise TypeError("quiescent proof tables must be immutable")
        if not self.safe_blank_left_states:
            raise ValueError("quiescent profile has no admissible left state")
        if (
            tuple(sorted(set(self.safe_blank_left_states)))
            != self.safe_blank_left_states
        ):
            raise ValueError("quiescent safe states are not canonical")
        if tuple(sorted(set(self.absorbing_blank_left_states))) != (
            self.absorbing_blank_left_states
        ):
            raise ValueError("quiescent sink states are not canonical")
        if any(
            type(value) is not int
            for row in (
                self.safe_blank_left_states,
                self.absorbing_blank_left_states,
                self.left_blank_transition,
                self.right_blank_transition,
            )
            for value in row
        ):
            raise TypeError("quiescent states require exact integer ordinals")
        left_count = len(self.left_blank_transition)
        right_count = len(self.right_blank_transition)
        if not left_count or not right_count:
            raise ValueError("quiescent behavior requires two finite state domains")
        if any(
            not 0 <= value < left_count
            for value in (
                *self.safe_blank_left_states,
                *self.absorbing_blank_left_states,
                *self.left_blank_transition,
            )
        ) or any(not 0 <= value < right_count for value in self.right_blank_transition):
            raise ValueError("quiescent proof state escaped its finite domain")
        if type(self.semantic_digest) is not str or len(self.semantic_digest) != 64:
            raise ValueError("quiescent behavior requires a deterministic digest")
        if self.semantic_digest != _certificate_digest(self):
            raise ValueError("quiescent behavior digest disagrees with its proof")


@dataclass(frozen=True, slots=True)
class FutureBehaviorProfile:
    """Immutable observation profile admitted by the quotient arena."""

    kernel: SemanticIdentity
    continuation: SemanticIdentity
    alphabet_size: int
    blank: int
    observations: tuple[str, ...]
    admissible_left_states: tuple[int, ...]
    geometry_schema: str
    cocycle_schema: str
    version: int
    certificate_digest: str

    def __post_init__(self) -> None:
        for identity in (self.kernel, self.continuation):
            if type(identity) is not SemanticIdentity:
                raise TypeError("future profiles require semantic identities")
            identity.__post_init__()
        if type(self.alphabet_size) is not int or self.alphabet_size < 1:
            raise ValueError("future profile requires a finite alphabet")
        if type(self.blank) is not int or not 0 <= self.blank < self.alphabet_size:
            raise ValueError("future profile has an invalid blank symbol")
        if self.observations != QUIESCENT_OBSERVATIONS:
            raise ValueError("future profile has an incomplete observation contract")
        if (
            type(self.admissible_left_states) is not tuple
            or not self.admissible_left_states
            or any(type(value) is not int for value in self.admissible_left_states)
            or tuple(sorted(set(self.admissible_left_states)))
            != self.admissible_left_states
        ):
            raise ValueError("future profile has invalid admissible states")
        if self.geometry_schema != QUIESCENT_GEOMETRY_SCHEMA:
            raise ValueError("future profile has another geometry contract")
        if self.cocycle_schema != QUIESCENT_COCYCLE_SCHEMA:
            raise ValueError("future profile has another cocycle contract")
        if type(self.version) is not int or self.version != QUIESCENT_PROFILE_VERSION:
            raise ValueError("future profile has another semantic version")
        if (
            type(self.certificate_digest) is not str
            or len(self.certificate_digest) != 64
        ):
            raise ValueError("future profile requires a certificate digest")


@dataclass(frozen=True, slots=True)
class FutureBehaviorClass:
    """One canonical all-blank self-loop under its admitted profile."""

    profile: FutureBehaviorProfileID
    law: str
    output_symbol: int
    active: bool
    termination: bool
    normalization_symbol: int

    def __post_init__(self) -> None:
        if type(self.profile) is not FutureBehaviorProfileID:
            raise TypeError("future behavior requires a scoped profile")
        if self.law != QUIESCENT_LAW:
            raise ValueError("future behavior has an uncertified law")
        if (
            type(self.output_symbol) is not int
            or type(self.normalization_symbol) is not int
        ):
            raise TypeError("future blank symbols require exact integers")
        if self.output_symbol != self.normalization_symbol:
            raise ValueError("quiescent normalization must preserve blank output")
        if type(self.active) is not bool or self.active:
            raise ValueError("quiescent blank behavior must be inactive")
        if type(self.termination) is not bool or not self.termination:
            raise ValueError("quiescent blank behavior must terminate")


def certify_quiescent_blank(
    quotient: PrimitiveBehaviorQuotient,
    *,
    work: FutureBehaviorWork | None = None,
) -> QuiescentBlankCertificate:
    """Compute the greatest primitive blank and absorbing-sink fixed points."""
    validate_primitive_behavior_quotient(quotient)
    measured = FutureBehaviorWork() if work is None else work
    if type(measured) is not FutureBehaviorWork:
        raise TypeError("quiescent refinement work requires a mutable work record")
    blank = quotient.blank
    safe: set[int] = set()
    sinks: set[int] = set()
    for left in range(quotient.left_count):
        safe_left = True
        sink_left = True
        for symbol in range(quotient.alphabet_size):
            for right in range(quotient.right_count):
                measured.observation_checks += 1
                blank_output = quotient.output(left, symbol, right) == blank
                blank_observation = quotient.observation(left, symbol, right) == (
                    0,
                    0,
                    0,
                )
                if symbol == blank and not (blank_output and blank_observation):
                    safe_left = False
                if not (blank_output and blank_observation):
                    sink_left = False
        if safe_left:
            safe.add(left)
        if sink_left:
            sinks.add(left)
    rounds = 0
    while True:
        rounds += 1
        measured.refinement_rounds = rounds
        next_safe = {
            left
            for left in safe
            if _successor_in(
                quotient.left_transitions[left][blank],
                safe,
                measured,
            )
        }
        next_sinks = {
            left
            for left in sinks
            if all(
                _successor_in(
                    quotient.left_transitions[left][symbol],
                    sinks,
                    measured,
                )
                for symbol in range(quotient.alphabet_size)
            )
        }
        if next_safe == safe and next_sinks == sinks:
            break
        safe, sinks = next_safe, next_sinks
    if not safe:
        raise UnsupportedFutureBehaviorProfile(
            "primitive kernel has no successor-closed blank behavior"
        )
    safe_states = tuple(sorted(safe))
    sink_states = tuple(sorted(sinks))
    left_transition = tuple(row[blank] for row in quotient.left_transitions)
    right_transition = tuple(row[blank] for row in quotient.right_transitions)
    key = (
        "quiescent-blank-certificate-v1",
        quotient.source_identity.behavior,
        quotient.semantic_identity.behavior,
        quotient.alphabet_size,
        blank,
        safe_states,
        sink_states,
        left_transition,
        right_transition,
        rounds,
    )
    return QuiescentBlankCertificate(
        quotient.source_identity,
        quotient.semantic_identity,
        quotient.alphabet_size,
        blank,
        safe_states,
        sink_states,
        left_transition,
        right_transition,
        rounds,
        sha256(repr(key).encode("utf-8")).hexdigest(),
    )


def _successor_in(
    successor: int,
    states: set[int],
    work: FutureBehaviorWork,
) -> bool:
    work.successor_checks += 1
    return successor in states


def _certificate_digest(certificate: QuiescentBlankCertificate) -> str:
    key = (
        "quiescent-blank-certificate-v1",
        certificate.kernel.behavior,
        certificate.continuation.behavior,
        certificate.alphabet_size,
        certificate.blank,
        certificate.safe_blank_left_states,
        certificate.absorbing_blank_left_states,
        certificate.left_blank_transition,
        certificate.right_blank_transition,
        certificate.refinement_rounds,
    )
    return sha256(repr(key).encode("utf-8")).hexdigest()


__all__ = [
    "FutureBehaviorClass",
    "FutureBehaviorClassID",
    "FutureBehaviorProfile",
    "FutureBehaviorProfileID",
    "FutureBehaviorWork",
    "QuiescentBlankCertificate",
    "UnsupportedFutureBehaviorProfile",
    "certify_quiescent_blank",
]

"""Proof-only finite audits for proposed active future-behavior profiles.

The carrier audited here is a declared finite local system.  Temporal
generators are tagged separately from spatial context actions, preventing a
carry-prefix monoid proof from being mistaken for temporal successor closure.
The minimizer refines against every declared generator and, when supplied,
both arguments of the spatial composition law.  These records are not runtime
``FutureBehaviorClassID`` values and cannot be published by the production
quotient arena.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from hashlib import sha256

from number_compiler.arithmetic.carry.carry_monoid import (
    apply_carry_fn,
    value_carry_fn,
)
from number_compiler.arithmetic.functions.finite_observer import canonical_partition
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.hashlife.behavior.future_behavior import (
    UnsupportedFutureBehaviorProfile,
)
from number_compiler.hashlife.interfaces.primitive_behavior import (
    PrimitiveBehaviorQuotient,
    validate_primitive_behavior_quotient,
)

ACTIVE_PROFILE_VERSION = 1
MAX_ACTIVE_PROFILE_TABLE_SLOTS = 1 << 20


class BehaviorGeneratorSort(Enum):
    """Semantic role of one certified transition generator."""

    TEMPORAL = "temporal"
    SPATIAL_PREFIX = "spatial-prefix"
    SPATIAL_SUFFIX = "spatial-suffix"


@dataclass(frozen=True, slots=True)
class BehaviorGenerator:
    """One immutable generator in a finite continuation profile."""

    sort: BehaviorGeneratorSort
    identity: SemanticIdentity

    def __post_init__(self) -> None:
        if type(self.sort) is not BehaviorGeneratorSort:
            raise TypeError("behavior generator requires an explicit semantic sort")
        if type(self.identity) is not SemanticIdentity:
            raise TypeError("behavior generator requires a semantic identity")
        self.identity.__post_init__()


@dataclass(frozen=True, slots=True)
class FiniteBehaviorProposal:
    """Frozen finite system presented for complete behavioral refinement."""

    kernel: SemanticIdentity
    continuation: SemanticIdentity
    observations: tuple[str, ...]
    observation_values: tuple[tuple[int, ...], ...]
    generators: tuple[BehaviorGenerator, ...]
    transitions: tuple[tuple[int, ...], ...]
    spatial_composition: tuple[tuple[int, ...], ...] | None
    geometry_schema: str
    identity_observing: bool
    version: int = ACTIVE_PROFILE_VERSION

    @property
    def state_count(self) -> int:
        return len(self.observation_values)

    def __post_init__(self) -> None:
        for identity in (self.kernel, self.continuation):
            if type(identity) is not SemanticIdentity:
                raise TypeError("active behavior systems require semantic identities")
            identity.__post_init__()
        if (
            type(self.observations) is not tuple
            or not self.observations
            or any(type(item) is not str or not item for item in self.observations)
            or len(set(self.observations)) != len(self.observations)
        ):
            raise ValueError("active behavior requires named finite observations")
        if type(self.observation_values) is not tuple or not self.observation_values:
            raise ValueError("active behavior requires a nonempty finite carrier")
        width = len(self.observations)
        if any(
            type(row) is not tuple
            or len(row) != width
            or any(type(value) is not int or value.bit_length() > 64 for value in row)
            for row in self.observation_values
        ):
            raise ValueError(
                "active behavior observations require bounded integer rows"
            )
        if (
            type(self.generators) is not tuple
            or not self.generators
            or any(type(item) is not BehaviorGenerator for item in self.generators)
            or len(set(self.generators)) != len(self.generators)
        ):
            raise ValueError("active behavior requires canonical finite generators")
        if not any(
            generator.sort is BehaviorGeneratorSort.TEMPORAL
            for generator in self.generators
        ):
            raise ValueError("active future behavior requires a temporal generator")
        if type(self.transitions) is not tuple or len(self.transitions) != len(
            self.generators
        ):
            raise ValueError("active behavior requires one table per generator")
        self._validate_table(
            self.transitions,
            "successor",
            outer_size=len(self.generators),
        )
        if self.spatial_composition is not None:
            self._validate_table(
                self.spatial_composition,
                "spatial",
                outer_size=self.state_count,
            )
        if type(self.geometry_schema) is not str or not self.geometry_schema:
            raise ValueError("active behavior requires a geometry schema")
        if type(self.identity_observing) is not bool:
            raise TypeError("identity-observation policy must be Boolean")
        if type(self.version) is not int or self.version != ACTIVE_PROFILE_VERSION:
            raise ValueError("active behavior system has another semantic version")
        slots = len(self.generators) * self.state_count
        if self.spatial_composition is not None:
            slots += self.state_count * self.state_count
        slots += width * self.state_count
        if slots > MAX_ACTIVE_PROFILE_TABLE_SLOTS:
            raise ValueError("active behavior system exceeds its fixed proof bound")

    def _validate_table(
        self,
        table: tuple[tuple[int, ...], ...],
        role: str,
        *,
        outer_size: int,
    ) -> None:
        if (
            type(table) is not tuple
            or len(table) != outer_size
            or any(
                type(row) is not tuple
                or len(row) != self.state_count
                or any(
                    type(target) is not int or not 0 <= target < self.state_count
                    for target in row
                )
                for row in table
            )
        ):
            raise ValueError(f"active {role} table escaped its finite carrier")


@dataclass(slots=True)
class BehaviorAuditWork:
    """Transient work counters for complete finite refinement."""

    observation_checks: int = 0
    successor_checks: int = 0
    spatial_checks: int = 0
    refinement_rounds: int = 0


@dataclass(frozen=True, slots=True)
class AuditedBehaviorProfile:
    """Immutable consumer profile backed by a complete certificate."""

    kernel: SemanticIdentity
    continuation: SemanticIdentity
    observations: tuple[str, ...]
    generators: tuple[BehaviorGenerator, ...]
    geometry_schema: str
    identity_observing: bool
    version: int
    certificate_digest: str

    def __post_init__(self) -> None:
        if (
            type(self.kernel) is not SemanticIdentity
            or type(self.continuation) is not SemanticIdentity
        ):
            raise TypeError("active profiles require semantic identities")
        self.kernel.__post_init__()
        self.continuation.__post_init__()
        if (
            type(self.observations) is not tuple
            or not self.observations
            or any(type(item) is not str or not item for item in self.observations)
            or len(set(self.observations)) != len(self.observations)
        ):
            raise ValueError("active profile requires declared observations")
        if (
            type(self.generators) is not tuple
            or not self.generators
            or any(type(item) is not BehaviorGenerator for item in self.generators)
            or len(set(self.generators)) != len(self.generators)
        ):
            raise ValueError("active profile requires continuation generators")
        for generator in self.generators:
            generator.__post_init__()
        if not any(
            generator.sort is BehaviorGeneratorSort.TEMPORAL
            for generator in self.generators
        ):
            raise ValueError("active profile requires temporal successor closure")
        if type(self.geometry_schema) is not str or not self.geometry_schema:
            raise ValueError("active profile requires geometry semantics")
        if type(self.identity_observing) is not bool:
            raise TypeError("active profile identity policy must be Boolean")
        if type(self.version) is not int or self.version != ACTIVE_PROFILE_VERSION:
            raise ValueError("active profile has another semantic version")
        if (
            type(self.certificate_digest) is not str
            or len(self.certificate_digest) != 64
        ):
            raise ValueError("active profile requires a certificate digest")


@dataclass(frozen=True, slots=True)
class BehaviorProfileAudit:
    """Coarsest completed bisimulation for one declared finite system."""

    profile: AuditedBehaviorProfile
    state_classes: tuple[int, ...]
    representatives: tuple[int, ...]
    observations: tuple[tuple[int, ...], ...]
    transitions: tuple[tuple[int, ...], ...]
    spatial_composition: tuple[tuple[int, ...], ...] | None
    refinement_rounds: int
    semantic_digest: str

    @property
    def class_count(self) -> int:
        return len(self.representatives)

    def __post_init__(self) -> None:
        if type(self.profile) is not AuditedBehaviorProfile:
            raise TypeError("active certificate requires its immutable profile")
        if (
            type(self.state_classes) is not tuple
            or not self.state_classes
            or any(type(value) is not int for value in self.state_classes)
            or any(value < 0 for value in self.state_classes)
        ):
            raise ValueError("active certificate requires a total state projection")
        if tuple(sorted(set(self.state_classes))) != tuple(range(self.class_count)):
            raise ValueError("active behavior class ordinals are not canonical")
        if (
            type(self.representatives) is not tuple
            or any(type(value) is not int for value in self.representatives)
            or len(set(self.representatives)) != len(self.representatives)
            or any(
                not 0 <= value < len(self.state_classes)
                for value in self.representatives
            )
            or any(
                self.state_classes[state] != class_id
                for class_id, state in enumerate(self.representatives)
            )
        ):
            raise ValueError("active behavior representatives are not canonical")
        if (
            type(self.observations) is not tuple
            or len(self.observations) != self.class_count
            or any(
                type(row) is not tuple
                or len(row) != len(self.profile.observations)
                or any(
                    type(value) is not int or value.bit_length() > 64 for value in row
                )
                for row in self.observations
            )
        ):
            raise ValueError("active behavior observations have another class domain")
        if (
            type(self.transitions) is not tuple
            or len(self.transitions) != len(self.profile.generators)
            or any(
                type(row) is not tuple
                or len(row) != self.class_count
                or any(
                    type(value) is not int or not 0 <= value < self.class_count
                    for value in row
                )
                for row in self.transitions
            )
        ):
            raise ValueError("active behavior transitions have another class domain")
        if self.spatial_composition is not None and (
            type(self.spatial_composition) is not tuple
            or len(self.spatial_composition) != self.class_count
            or any(
                type(row) is not tuple
                or len(row) != self.class_count
                or any(
                    type(value) is not int or not 0 <= value < self.class_count
                    for value in row
                )
                for row in self.spatial_composition
            )
        ):
            raise ValueError("active spatial quotient has another class domain")
        if type(self.refinement_rounds) is not int or self.refinement_rounds < 1:
            raise ValueError("active behavior refinement did not reach a fixed point")
        if self.profile.certificate_digest != self.semantic_digest:
            raise ValueError("active profile and certificate digest disagree")
        if self.semantic_digest != _certificate_digest(self):
            raise ValueError("active certificate digest disagrees with its proof")

    def project(self, state: int) -> int:
        _ordinal(state, len(self.state_classes), "active concrete state")
        return self.state_classes[state]

    def successor(self, generator: int, behavior: int) -> int:
        _ordinal(generator, len(self.transitions), "active behavior generator")
        _ordinal(behavior, self.class_count, "active behavior class")
        return self.transitions[generator][behavior]

    def compose_spatial(self, left: int, right: int) -> int:
        if self.spatial_composition is None:
            raise UnsupportedFutureBehaviorProfile(
                "this active profile has no certified spatial composition"
            )
        _ordinal(left, self.class_count, "left active behavior")
        _ordinal(right, self.class_count, "right active behavior")
        return self.spatial_composition[left][right]

    def require_macrocell_closure(self) -> None:
        """Reject leaf-only certificates at a macrocell publication boundary."""
        if self.spatial_composition is None:
            raise UnsupportedFutureBehaviorProfile(
                "active macrocell behavior requires certified spatial composition"
            )
        if not any(
            generator.sort is BehaviorGeneratorSort.TEMPORAL
            for generator in self.profile.generators
        ):
            raise UnsupportedFutureBehaviorProfile(
                "active macrocell behavior requires temporal successor closure"
            )


def audit_finite_behavior_profile(
    system: FiniteBehaviorProposal,
    *,
    work: BehaviorAuditWork | None = None,
) -> BehaviorProfileAudit:
    """Compute and verify the coarsest congruence of a complete finite system."""
    if type(system) is not FiniteBehaviorProposal:
        raise TypeError("active certification requires a frozen finite system")
    system.__post_init__()
    measured = BehaviorAuditWork() if work is None else work
    if type(measured) is not BehaviorAuditWork:
        raise TypeError("active refinement work requires its mutable record")
    measured.observation_checks += system.state_count * len(system.observations)
    partition = canonical_partition(system.observation_values)
    rounds = 0
    while True:
        rounds += 1
        signatures: list[tuple[object, ...]] = []
        for state in range(system.state_count):
            successor_signature = tuple(
                partition[row[state]] for row in system.transitions
            )
            measured.successor_checks += len(system.transitions)
            if system.spatial_composition is None:
                spatial_signature: tuple[tuple[int, ...], tuple[int, ...]] = ((), ())
            else:
                spatial_signature = (
                    tuple(
                        partition[system.spatial_composition[state][other]]
                        for other in range(system.state_count)
                    ),
                    tuple(
                        partition[system.spatial_composition[other][state]]
                        for other in range(system.state_count)
                    ),
                )
                measured.spatial_checks += 2 * system.state_count
            signatures.append(
                (
                    system.observation_values[state],
                    successor_signature,
                    spatial_signature,
                )
            )
        refined = canonical_partition(tuple(signatures))
        measured.refinement_rounds = rounds
        if _same_partition(partition, refined):
            partition = refined
            break
        partition = refined

    if system.identity_observing and len(set(partition)) != system.state_count:
        raise UnsupportedFutureBehaviorProfile(
            "identity-observing active profiles cannot merge concrete states"
        )

    representatives = _representatives(partition)
    observations = tuple(system.observation_values[state] for state in representatives)
    transitions = tuple(
        tuple(partition[row[state]] for state in representatives)
        for row in system.transitions
    )
    spatial = (
        None
        if system.spatial_composition is None
        else tuple(
            tuple(
                partition[system.spatial_composition[left][right]]
                for right in representatives
            )
            for left in representatives
        )
    )
    proof_key = (
        "active-future-behavior-certificate-v1",
        system.kernel.behavior,
        system.continuation.behavior,
        system.observations,
        tuple((item.sort.value, item.identity.behavior) for item in system.generators),
        system.geometry_schema,
        system.identity_observing,
        system.version,
        partition,
        representatives,
        observations,
        transitions,
        spatial,
        rounds,
    )
    digest = sha256(repr(proof_key).encode("utf-8")).hexdigest()
    profile = AuditedBehaviorProfile(
        system.kernel,
        system.continuation,
        system.observations,
        system.generators,
        system.geometry_schema,
        system.identity_observing,
        system.version,
        digest,
    )
    certificate = BehaviorProfileAudit(
        profile,
        partition,
        representatives,
        observations,
        transitions,
        spatial,
        rounds,
        digest,
    )
    certificate.__post_init__()
    return certificate


def reverse_leaf_carry_consumer_system(
    quotient: PrimitiveBehaviorQuotient,
    base: int,
) -> FiniteBehaviorProposal:
    """Build the exact leaf-level temporal audit for reverse carry consumers.

    LT/EQ/GT is the initial observation.  Every primitive left/right context
    is then admitted as a temporal generator.  The resulting certificate is
    intentionally leaf-local and has no spatial composition law.
    """
    validate_primitive_behavior_quotient(quotient)
    if type(base) is not int or base < 2:
        raise ValueError("reverse carry profile requires an exact radix")
    if quotient.alphabet_size != 2 * base or quotient.blank != 2 * base - 1:
        raise ValueError("primitive quotient is not a reverse pair alphabet")
    observations = tuple(
        (-1, -1, 0)
        if symbol == quotient.blank
        else (
            apply_carry_fn(value_carry_fn(symbol, base), 0),
            apply_carry_fn(value_carry_fn(symbol, base), 1),
            1,
        )
        for symbol in range(quotient.alphabet_size)
    )
    generators: list[BehaviorGenerator] = []
    transitions: list[tuple[int, ...]] = []
    for left in range(quotient.left_count):
        for right in range(quotient.right_count):
            identity = SemanticIdentity(
                "",
                (
                    "reverse-leaf-output-context-v1",
                    base,
                    left,
                    right,
                ),
            )
            generators.append(
                BehaviorGenerator(BehaviorGeneratorSort.TEMPORAL, identity)
            )
            transitions.append(
                tuple(
                    quotient.output(left, symbol, right)
                    for symbol in range(quotient.alphabet_size)
                )
            )
    return FiniteBehaviorProposal(
        quotient.source_identity,
        quotient.semantic_identity,
        (
            "carry-output-for-input-0",
            "carry-output-for-input-1",
            "active-nonblank",
        ),
        observations,
        tuple(generators),
        tuple(transitions),
        None,
        "single-reverse-pair-cell-v1",
        False,
    )


def certify_reverse_leaf_carry_consumer(
    quotient: PrimitiveBehaviorQuotient,
    base: int,
    *,
    work: BehaviorAuditWork | None = None,
) -> BehaviorProfileAudit:
    """Certify the complete reverse leaf profile, including negative aliases."""
    return audit_finite_behavior_profile(
        reverse_leaf_carry_consumer_system(quotient, base),
        work=work,
    )


def _same_partition(left: tuple[int, ...], right: tuple[int, ...]) -> bool:
    return all(
        (left[a] == left[b]) == (right[a] == right[b])
        for a in range(len(left))
        for b in range(len(left))
    )


def _representatives(partition: tuple[int, ...]) -> tuple[int, ...]:
    result: list[int] = []
    for class_id in range(max(partition) + 1):
        result.append(partition.index(class_id))
    return tuple(result)


def _certificate_digest(certificate: BehaviorProfileAudit) -> str:
    profile = certificate.profile
    key = (
        "active-future-behavior-certificate-v1",
        profile.kernel.behavior,
        profile.continuation.behavior,
        profile.observations,
        tuple((item.sort.value, item.identity.behavior) for item in profile.generators),
        profile.geometry_schema,
        profile.identity_observing,
        profile.version,
        certificate.state_classes,
        certificate.representatives,
        certificate.observations,
        certificate.transitions,
        certificate.spatial_composition,
        certificate.refinement_rounds,
    )
    return sha256(repr(key).encode("utf-8")).hexdigest()


def _ordinal(value: int, size: int, role: str) -> None:
    if type(value) is not int:
        raise TypeError(f"{role} requires an exact integer")
    if not 0 <= value < size:
        raise ValueError(f"{role} escaped its finite domain")


__all__ = [
    "ACTIVE_PROFILE_VERSION",
    "MAX_ACTIVE_PROFILE_TABLE_SLOTS",
    "AuditedBehaviorProfile",
    "BehaviorAuditWork",
    "BehaviorGenerator",
    "BehaviorGeneratorSort",
    "BehaviorProfileAudit",
    "FiniteBehaviorProposal",
    "audit_finite_behavior_profile",
    "certify_reverse_leaf_carry_consumer",
    "reverse_leaf_carry_consumer_system",
]

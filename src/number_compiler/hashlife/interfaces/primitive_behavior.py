"""Minimal output-complete residuals for one certified primitive kernel.

This module is the admission boundary between an immutable arithmetic kernel
and runtime local-interface compilation.  It enumerates only the kernel's
declared primitive state and symbol domains.  Temporal powers, spatial cells,
source fragments, and continuation programs cannot enter the certificate.

The quotient is Myhill--Nerode exact: initial classes are complete emission
residuals and refinement adds the corresponding directed successor class.
Consequently equal carry exits cannot merge states whose emitted symbols
differ.  The implementation is iterative and deterministic.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from hashlib import sha256
from typing import Protocol

from number_compiler.arithmetic.automata.symmetry_powering import ActionTransform
from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.functions.finite_observer import (
    canonical_partition,
    partition_equivalent,
)

PRIMITIVE_CHANNEL_SCHEMA = (
    "boundary_left",
    "boundary_right",
    "output",
    "activity",
    "first_active",
    "last_active",
    "extent",
    "halo_left",
    "halo_right",
    "growth",
    "termination",
    "normalization",
    "frame",
)

# These occurrence-local values are not reconstructible from the emitted
# symbol in every arithmetic family.  In particular, a physical Collatz leaf
# records the unique odd-event observation at the low boundary.  They must
# participate in residual refinement even though they stay outside TileID.
PRIMITIVE_OCCURRENCE_SCHEMA = (
    "event_weight",
    "valuation_delta",
    "frame_shift",
)

MAX_PRIMITIVE_BEHAVIOR_TABLE_ENTRIES = 1 << 20
PRIMITIVE_CHANNEL_CONTRACT = "fixed-padded-cell-leaf-v1"


def primitive_behavior_table_slots(left: int, right: int, alphabet: int) -> int:
    """Return exact retained scalar slots for a captured primitive table."""
    if any(type(value) is not int or value < 1 for value in (left, right, alphabet)):
        raise ValueError("primitive table dimensions require positive exact integers")
    triples = left * alphabet * right
    return (
        left * alphabet
        + right * alphabet
        + triples
        * (1 + len(PRIMITIVE_CHANNEL_SCHEMA) + len(PRIMITIVE_OCCURRENCE_SCHEMA))
    )


@dataclass(slots=True)
class PrimitiveBehaviorWork:
    """Transient minimization work, never retained by a quotient."""

    observation_checks: int = 0
    successor_checks: int = 0


class PrimitiveBehaviorKernel(Protocol):
    """Finite runtime surface required by primitive quotient admission."""

    @property
    def base(self) -> int: ...

    @property
    def blank(self) -> int: ...

    @property
    def left_count(self) -> int: ...

    @property
    def right_count(self) -> int: ...

    def advance(self, side: BoundarySide, state: int, symbol: int) -> int: ...

    def emit(self, left: int, symbol: int, right: int) -> int: ...

    def observe(self, left: int, symbol: int, right: int) -> tuple[int, ...]: ...


@dataclass(frozen=True, slots=True)
class PrimitiveBehaviorTable:
    """Frozen output-complete local system before residual minimization."""

    identity: SemanticIdentity
    alphabet_size: int
    blank: int
    left_transitions: tuple[tuple[int, ...], ...]
    right_transitions: tuple[tuple[int, ...], ...]
    outputs: tuple[int, ...]
    channels: tuple[tuple[int, ...], ...]
    observations: tuple[tuple[int, ...], ...]

    @property
    def left_count(self) -> int:
        return len(self.left_transitions)

    @property
    def right_count(self) -> int:
        return len(self.right_transitions)

    def output(self, left: int, symbol: int, right: int) -> int:
        _ordinal(left, self.left_count, "left state")
        _ordinal(symbol, self.alphabet_size, "symbol")
        _ordinal(right, self.right_count, "right state")
        return self.outputs[
            (left * self.alphabet_size + symbol) * self.right_count + right
        ]

    def observation(self, left: int, symbol: int, right: int) -> tuple[int, ...]:
        _ordinal(left, self.left_count, "left state")
        _ordinal(symbol, self.alphabet_size, "symbol")
        _ordinal(right, self.right_count, "right state")
        return self.observations[
            (left * self.alphabet_size + symbol) * self.right_count + right
        ]

    def channel_values(self, left: int, symbol: int, right: int) -> tuple[int, ...]:
        _ordinal(left, self.left_count, "left state")
        _ordinal(symbol, self.alphabet_size, "symbol")
        _ordinal(right, self.right_count, "right state")
        return self.channels[
            (left * self.alphabet_size + symbol) * self.right_count + right
        ]


@dataclass(frozen=True, slots=True)
class PrimitiveBehaviorQuotient:
    """Canonical minimal directed residual certificate.

    ``left_classes`` and ``right_classes`` project the admitted primitive
    domains.  The projected tables and outputs use deterministic class IDs,
    assigned by the lexicographically least complete residual signature.
    """

    source_identity: SemanticIdentity
    semantic_identity: SemanticIdentity
    alphabet_size: int
    blank: int
    left_classes: tuple[int, ...]
    right_classes: tuple[int, ...]
    left_representatives: tuple[int, ...]
    right_representatives: tuple[int, ...]
    left_transitions: tuple[tuple[int, ...], ...]
    right_transitions: tuple[tuple[int, ...], ...]
    outputs: tuple[int, ...]
    channels: tuple[tuple[int, ...], ...]
    observations: tuple[tuple[int, ...], ...]
    refinement_rounds: int

    @property
    def left_count(self) -> int:
        return len(self.left_transitions)

    @property
    def right_count(self) -> int:
        return len(self.right_transitions)

    def output(self, left: int, symbol: int, right: int) -> int:
        _ordinal(left, self.left_count, "left quotient state")
        _ordinal(symbol, self.alphabet_size, "symbol")
        _ordinal(right, self.right_count, "right quotient state")
        return self.outputs[
            (left * self.alphabet_size + symbol) * self.right_count + right
        ]

    def observation(self, left: int, symbol: int, right: int) -> tuple[int, ...]:
        _ordinal(left, self.left_count, "left quotient state")
        _ordinal(symbol, self.alphabet_size, "symbol")
        _ordinal(right, self.right_count, "right quotient state")
        return self.observations[
            (left * self.alphabet_size + symbol) * self.right_count + right
        ]

    def channel_values(self, left: int, symbol: int, right: int) -> tuple[int, ...]:
        _ordinal(left, self.left_count, "left quotient state")
        _ordinal(symbol, self.alphabet_size, "symbol")
        _ordinal(right, self.right_count, "right quotient state")
        return self.channels[
            (left * self.alphabet_size + symbol) * self.right_count + right
        ]


@dataclass(frozen=True, slots=True)
class LocalSymmetryWitness:
    """One immutable, exhaustively checked causal interface automorphism.

    Mirror swaps the directed left/right state sorts.  Conjugacy preserves the
    sorts.  Maps are explicit permutations, so a reset endomorphism can never
    be mislabeled as an automorphism.  Output maps cover the complete emitted
    symbol; metadata channels derived from that symbol transform with it.
    """

    transform: ActionTransform
    symbol_map: tuple[int, ...]
    left_map: tuple[int, ...]
    right_map: tuple[int, ...]
    output_map: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class CertifiedLocalSymmetry:
    """Verified causal subgroup for one primitive behavioral certificate."""

    behavior: SemanticIdentity
    witnesses: tuple[LocalSymmetryWitness, ...]
    semantic_digest: str

    @property
    def transforms(self) -> tuple[ActionTransform, ...]:
        return tuple(witness.transform for witness in self.witnesses)

    def require(self, transform: ActionTransform) -> LocalSymmetryWitness:
        if type(transform) is not ActionTransform or int(transform) & ~3:
            raise ValueError("unsupported D4 transform")
        for witness in self.witnesses:
            if witness.transform is transform:
                return witness
        raise ValueError("primitive interface has no certified wiring automorphism")


def capture_primitive_behavior(
    kernel: PrimitiveBehaviorKernel,
    identity: SemanticIdentity,
) -> PrimitiveBehaviorTable:
    """Freeze one kernel's complete local transition/output behavior."""
    if type(identity) is not SemanticIdentity:
        raise TypeError("primitive behavior requires a semantic kernel identity")
    identity.__post_init__()
    for value, name in (
        (kernel.left_count, "left count"),
        (kernel.right_count, "right count"),
        (kernel.blank, "blank"),
    ):
        if type(value) is not int or value < 0:
            raise ValueError(f"invalid primitive {name}")
    alphabet_size = kernel.blank + 1
    if not kernel.left_count or not kernel.right_count or not alphabet_size:
        raise ValueError("primitive behavior domains must be nonempty")
    table_entries = primitive_behavior_table_slots(
        kernel.left_count,
        kernel.right_count,
        alphabet_size,
    )
    if table_entries > MAX_PRIMITIVE_BEHAVIOR_TABLE_ENTRIES:
        raise ValueError("primitive behavioral table exceeds its fixed admission bound")
    left = tuple(
        tuple(
            kernel.advance(BoundarySide.LEFT, state, symbol)
            for symbol in range(alphabet_size)
        )
        for state in range(kernel.left_count)
    )
    right = tuple(
        tuple(
            kernel.advance(BoundarySide.RIGHT, state, symbol)
            for symbol in range(alphabet_size)
        )
        for state in range(kernel.right_count)
    )
    outputs = tuple(
        kernel.emit(left_state, symbol, right_state)
        for left_state in range(kernel.left_count)
        for symbol in range(alphabet_size)
        for right_state in range(kernel.right_count)
    )
    observations = tuple(
        kernel.observe(left_state, symbol, right_state)
        for left_state in range(kernel.left_count)
        for symbol in range(alphabet_size)
        for right_state in range(kernel.right_count)
    )
    channels = tuple(
        _fixed_padded_leaf_channels(
            left[left_state][symbol],
            right[right_state][symbol],
            outputs[
                (left_state * alphabet_size + symbol) * kernel.right_count + right_state
            ],
            symbol,
            kernel.blank,
        )
        for left_state in range(kernel.left_count)
        for symbol in range(alphabet_size)
        for right_state in range(kernel.right_count)
    )
    for row, size in (
        *((row, kernel.left_count) for row in left),
        *((row, kernel.right_count) for row in right),
    ):
        if any(type(target) is not int or not 0 <= target < size for target in row):
            raise ValueError("primitive transition escaped its finite domain")
    if any(
        type(value) is not int or not 0 <= value < alphabet_size for value in outputs
    ):
        raise ValueError("primitive output escaped its finite alphabet")
    _validate_observations(observations, len(outputs))
    key = (
        identity.behavior,
        alphabet_size,
        kernel.blank,
        left,
        right,
        outputs,
        PRIMITIVE_CHANNEL_CONTRACT,
        PRIMITIVE_CHANNEL_SCHEMA,
        channels,
        PRIMITIVE_OCCURRENCE_SCHEMA,
        observations,
    )
    return PrimitiveBehaviorTable(
        SemanticIdentity("primitive-behavior-table", key),
        alphabet_size,
        kernel.blank,
        left,
        right,
        outputs,
        channels,
        observations,
    )


def minimize_primitive_behavior(
    table: PrimitiveBehaviorTable,
    *,
    work: PrimitiveBehaviorWork | None = None,
) -> PrimitiveBehaviorQuotient:
    """Return the coarsest exact two-sided output congruence."""
    if type(table) is not PrimitiveBehaviorTable:
        raise TypeError("primitive minimization requires a frozen behavior table")
    _validate_table(table)
    if work is not None and type(work) is not PrimitiveBehaviorWork:
        raise TypeError("primitive refinement work requires a transient counter record")
    primitive_observations = table.left_count * table.alphabet_size * table.right_count
    # Emission residuals do not depend on the evolving successor partition.
    # Read each frozen primitive row once, then retain only two directional
    # tuple views while refinement updates the transition-class suffixes.
    emissions = tuple(
        (channels[2:], observation)
        for channels, observation in zip(
            table.channels, table.observations, strict=True
        )
    )
    left_emissions = tuple(
        tuple(
            emissions[(left * table.alphabet_size + symbol) * table.right_count + right]
            for symbol in range(table.alphabet_size)
            for right in range(table.right_count)
        )
        for left in range(table.left_count)
    )
    right_emissions = tuple(
        tuple(
            emissions[(left * table.alphabet_size + symbol) * table.right_count + right]
            for symbol in range(table.alphabet_size)
            for left in range(table.left_count)
        )
        for right in range(table.right_count)
    )
    left_part = canonical_partition(left_emissions)
    right_part = canonical_partition(right_emissions)
    if work is not None:
        # One channel-vector and one occurrence-vector read per primitive row.
        work.observation_checks += 2 * primitive_observations
    rounds = 0
    while True:
        rounds += 1
        left_signatures = tuple(
            (
                left_emissions[left],
                tuple(left_part[target] for target in table.left_transitions[left]),
            )
            for left in range(table.left_count)
        )
        right_signatures = tuple(
            (
                right_emissions[right],
                tuple(right_part[target] for target in table.right_transitions[right]),
            )
            for right in range(table.right_count)
        )
        if work is not None:
            work.successor_checks += (
                table.left_count + table.right_count
            ) * table.alphabet_size
        new_left = canonical_partition(left_signatures)
        new_right = canonical_partition(right_signatures)
        if partition_equivalent(left_part, new_left) and partition_equivalent(
            right_part, new_right
        ):
            left_part, right_part = new_left, new_right
            break
        left_part, right_part = new_left, new_right
    left_reps = _representatives(left_part)
    right_reps = _representatives(right_part)
    projected_left = tuple(
        tuple(left_part[target] for target in table.left_transitions[representative])
        for representative in left_reps
    )
    projected_right = tuple(
        tuple(right_part[target] for target in table.right_transitions[representative])
        for representative in right_reps
    )
    projected_outputs = tuple(
        table.output(left_reps[left], symbol, right_reps[right])
        for left in range(len(left_reps))
        for symbol in range(table.alphabet_size)
        for right in range(len(right_reps))
    )
    projected_observations = tuple(
        table.observation(left_reps[left], symbol, right_reps[right])
        for left in range(len(left_reps))
        for symbol in range(table.alphabet_size)
        for right in range(len(right_reps))
    )
    projected_channels = tuple(
        (
            projected_left[left][symbol],
            projected_right[right][symbol],
            *table.channel_values(left_reps[left], symbol, right_reps[right])[2:],
        )
        for left in range(len(left_reps))
        for symbol in range(table.alphabet_size)
        for right in range(len(right_reps))
    )
    if work is not None:
        work.observation_checks += (
            3 * len(left_reps) * table.alphabet_size * len(right_reps)
        )
    semantic_key = (
        "primitive-behavior-quotient-v2",
        PRIMITIVE_CHANNEL_CONTRACT,
        PRIMITIVE_CHANNEL_SCHEMA,
        PRIMITIVE_OCCURRENCE_SCHEMA,
        table.alphabet_size,
        table.blank,
        projected_left,
        projected_right,
        projected_outputs,
        projected_channels,
        projected_observations,
    )
    return PrimitiveBehaviorQuotient(
        table.identity,
        SemanticIdentity("primitive-behavior-quotient", semantic_key),
        table.alphabet_size,
        table.blank,
        left_part,
        right_part,
        left_reps,
        right_reps,
        projected_left,
        projected_right,
        projected_outputs,
        projected_channels,
        projected_observations,
        rounds,
    )


def certify_local_symmetry(
    quotient: PrimitiveBehaviorQuotient,
    witnesses: tuple[LocalSymmetryWitness, ...],
) -> CertifiedLocalSymmetry:
    """Validate a declared subgroup against all transitions and emissions."""
    if type(quotient) is not PrimitiveBehaviorQuotient:
        raise TypeError("symmetry certification requires a primitive quotient")
    if type(witnesses) is not tuple or not witnesses:
        raise TypeError("symmetry witnesses require an immutable nonempty tuple")
    by_transform: dict[ActionTransform, LocalSymmetryWitness] = {}
    for witness in witnesses:
        _validate_witness(quotient, witness)
        if witness.transform in by_transform:
            raise ValueError("duplicate symmetry transform")
        by_transform[witness.transform] = witness
    identity = by_transform.get(ActionTransform.IDENTITY)
    if identity is None or any(
        mapping != tuple(range(len(mapping)))
        for mapping in (
            identity.symbol_map,
            identity.left_map,
            identity.right_map,
            identity.output_map,
        )
    ):
        raise ValueError("causal symmetry certificate requires the exact identity")
    # The admitted set must be a group under the two commuting involutions.
    for first, first_effect in by_transform.items():
        for second, second_effect in by_transform.items():
            combined = ActionTransform(int(first) ^ int(second))
            if combined not in by_transform:
                raise ValueError(
                    "declared causal transforms are not composition-closed"
                )
            _validate_composition(
                first_effect,
                second_effect,
                by_transform[combined],
            )
    key = (
        quotient.semantic_identity.behavior,
        tuple(
            (
                int(item.transform),
                item.symbol_map,
                item.left_map,
                item.right_map,
                item.output_map,
            )
            for item in sorted(witnesses, key=lambda item: int(item.transform))
        ),
    )
    digest = sha256(repr(key).encode("utf-8")).hexdigest()
    return CertifiedLocalSymmetry(
        quotient.semantic_identity,
        tuple(sorted(witnesses, key=lambda item: int(item.transform))),
        digest,
    )


def identity_symmetry(quotient: PrimitiveBehaviorQuotient) -> CertifiedLocalSymmetry:
    """Return the always-valid identity-only causal certificate."""
    witness = LocalSymmetryWitness(
        ActionTransform.IDENTITY,
        tuple(range(quotient.alphabet_size)),
        tuple(range(quotient.left_count)),
        tuple(range(quotient.right_count)),
        tuple(range(quotient.alphabet_size)),
    )
    return certify_local_symmetry(quotient, (witness,))


def validate_certified_local_symmetry(
    quotient: PrimitiveBehaviorQuotient,
    certificate: CertifiedLocalSymmetry,
) -> None:
    """Revalidate a frozen automorphism certificate against its quotient."""
    if type(certificate) is not CertifiedLocalSymmetry:
        raise TypeError("expected a certified local symmetry")
    if certificate.behavior != quotient.semantic_identity:
        raise ValueError("local symmetry belongs to another behavioral quotient")
    if certify_local_symmetry(quotient, certificate.witnesses) != certificate:
        raise ValueError("local symmetry digest or maps are not canonical")


def validate_primitive_behavior_quotient(
    quotient: PrimitiveBehaviorQuotient,
    *,
    validate_identity: Callable[[SemanticIdentity], None] = SemanticIdentity.validate,
) -> None:
    """Revalidate a retained certificate without executing a kernel."""
    if type(quotient) is not PrimitiveBehaviorQuotient:
        raise TypeError("expected a primitive behavioral quotient")
    validate_identity(quotient.source_identity)
    validate_identity(quotient.semantic_identity)
    if type(quotient.refinement_rounds) is not int or quotient.refinement_rounds < 1:
        raise ValueError("invalid primitive refinement count")
    _ordinal(quotient.blank, quotient.alphabet_size, "blank")
    for classes, representatives, count, role in (
        (
            quotient.left_classes,
            quotient.left_representatives,
            quotient.left_count,
            "left",
        ),
        (
            quotient.right_classes,
            quotient.right_representatives,
            quotient.right_count,
            "right",
        ),
    ):
        if type(classes) is not tuple or not classes:
            raise ValueError(f"invalid {role} quotient projection")
        if any(type(value) is not int or not 0 <= value < count for value in classes):
            raise ValueError(f"invalid {role} quotient class")
        if representatives != _representatives(classes):
            raise ValueError(f"noncanonical {role} quotient representatives")
    for rows, count, role in (
        (quotient.left_transitions, quotient.left_count, "left"),
        (quotient.right_transitions, quotient.right_count, "right"),
    ):
        if type(rows) is not tuple or len(rows) != count:
            raise ValueError(f"invalid {role} quotient transitions")
        for row in rows:
            if type(row) is not tuple or len(row) != quotient.alphabet_size:
                raise ValueError(f"invalid {role} quotient transition row")
            for target in row:
                _ordinal(target, count, f"{role} quotient target")
    expected_outputs = (
        quotient.left_count * quotient.alphabet_size * quotient.right_count
    )
    if type(quotient.outputs) is not tuple or len(quotient.outputs) != expected_outputs:
        raise ValueError("invalid quotient output table")
    for value in quotient.outputs:
        _ordinal(value, quotient.alphabet_size, "quotient output")
    _validate_channels(
        quotient.channels,
        expected_outputs,
        quotient.left_transitions,
        quotient.right_transitions,
        quotient.outputs,
        quotient.alphabet_size,
        quotient.right_count,
        quotient.blank,
    )
    _validate_observations(quotient.observations, expected_outputs)
    semantic_key = (
        "primitive-behavior-quotient-v2",
        PRIMITIVE_CHANNEL_CONTRACT,
        PRIMITIVE_CHANNEL_SCHEMA,
        PRIMITIVE_OCCURRENCE_SCHEMA,
        quotient.alphabet_size,
        quotient.blank,
        quotient.left_transitions,
        quotient.right_transitions,
        quotient.outputs,
        quotient.channels,
        quotient.observations,
    )
    if quotient.semantic_identity.behavior != semantic_key:
        raise ValueError("primitive quotient identity does not match its behavior")


def _validate_witness(
    quotient: PrimitiveBehaviorQuotient,
    witness: LocalSymmetryWitness,
) -> None:
    if type(witness) is not LocalSymmetryWitness:
        raise TypeError("causal transforms require exact symmetry witnesses")
    transform = witness.transform
    if type(transform) is not ActionTransform or int(transform) & ~3:
        raise ValueError("unsupported D4 transform")
    mirror = bool(transform & ActionTransform.MIRROR)
    _permutation(witness.symbol_map, quotient.alphabet_size, "symbol")
    _permutation(witness.output_map, quotient.alphabet_size, "output")
    if (
        witness.symbol_map[quotient.blank] != quotient.blank
        or witness.output_map[quotient.blank] != quotient.blank
    ):
        raise ValueError("causal symmetry must preserve blank/activity semantics")
    if mirror:
        if quotient.left_count != quotient.right_count:
            raise ValueError("mirror cannot swap unequal directed state sorts")
        _permutation(witness.left_map, quotient.right_count, "left-to-right")
        _permutation(witness.right_map, quotient.left_count, "right-to-left")
    else:
        _permutation(witness.left_map, quotient.left_count, "left")
        _permutation(witness.right_map, quotient.right_count, "right")
    for left in range(quotient.left_count):
        for symbol in range(quotient.alphabet_size):
            moved_symbol = witness.symbol_map[symbol]
            target = quotient.left_transitions[left][symbol]
            if mirror:
                actual = quotient.right_transitions[witness.left_map[left]][
                    moved_symbol
                ]
            else:
                actual = quotient.left_transitions[witness.left_map[left]][moved_symbol]
            if actual != witness.left_map[target]:
                raise ValueError("left transition violates declared causal symmetry")
    for right in range(quotient.right_count):
        for symbol in range(quotient.alphabet_size):
            moved_symbol = witness.symbol_map[symbol]
            target = quotient.right_transitions[right][symbol]
            if mirror:
                actual = quotient.left_transitions[witness.right_map[right]][
                    moved_symbol
                ]
            else:
                actual = quotient.right_transitions[witness.right_map[right]][
                    moved_symbol
                ]
            if actual != witness.right_map[target]:
                raise ValueError("right transition violates declared causal symmetry")
    for left in range(quotient.left_count):
        for symbol in range(quotient.alphabet_size):
            for right in range(quotient.right_count):
                expected = witness.output_map[quotient.output(left, symbol, right)]
                if mirror:
                    actual = quotient.output(
                        witness.right_map[right],
                        witness.symbol_map[symbol],
                        witness.left_map[left],
                    )
                else:
                    actual = quotient.output(
                        witness.left_map[left],
                        witness.symbol_map[symbol],
                        witness.right_map[right],
                    )
                if actual != expected:
                    raise ValueError("emission violates declared causal symmetry")
                expected_observation = quotient.observation(left, symbol, right)
                if mirror:
                    actual_observation = quotient.observation(
                        witness.right_map[right],
                        witness.symbol_map[symbol],
                        witness.left_map[left],
                    )
                else:
                    actual_observation = quotient.observation(
                        witness.left_map[left],
                        witness.symbol_map[symbol],
                        witness.right_map[right],
                    )
                if actual_observation != expected_observation:
                    raise ValueError(
                        "occurrence observation violates declared causal symmetry"
                    )


def _validate_composition(
    first: LocalSymmetryWitness,
    second: LocalSymmetryWitness,
    expected: LocalSymmetryWitness,
) -> None:
    """Check map composition, including the sort swap caused by mirror."""
    symbol = tuple(
        second.symbol_map[first.symbol_map[value]]
        for value in range(len(first.symbol_map))
    )
    output = tuple(
        second.output_map[first.output_map[value]]
        for value in range(len(first.output_map))
    )
    if first.transform & ActionTransform.MIRROR:
        left = tuple(
            second.right_map[first.left_map[value]]
            for value in range(len(first.left_map))
        )
        right = tuple(
            second.left_map[first.right_map[value]]
            for value in range(len(first.right_map))
        )
    else:
        left = tuple(
            second.left_map[first.left_map[value]]
            for value in range(len(first.left_map))
        )
        right = tuple(
            second.right_map[first.right_map[value]]
            for value in range(len(first.right_map))
        )
    if (symbol, left, right, output) != (
        expected.symbol_map,
        expected.left_map,
        expected.right_map,
        expected.output_map,
    ):
        raise ValueError("declared causal transform maps violate the group law")


def _validate_table(
    table: PrimitiveBehaviorTable,
    *,
    validate_identity: Callable[[SemanticIdentity], None] = SemanticIdentity.validate,
) -> None:
    validate_identity(table.identity)
    if type(table.alphabet_size) is not int or not 1 <= table.alphabet_size <= 1 << 64:
        raise ValueError("invalid primitive alphabet")
    _ordinal(table.blank, table.alphabet_size, "blank")
    if not table.left_transitions or not table.right_transitions:
        raise ValueError("primitive state domains must be nonempty")
    for rows, size in (
        (table.left_transitions, table.left_count),
        (table.right_transitions, table.right_count),
    ):
        if type(rows) is not tuple:
            raise TypeError("primitive transition tables must be immutable")
        for row in rows:
            if type(row) is not tuple or len(row) != table.alphabet_size:
                raise ValueError("primitive transition row has another alphabet")
            for target in row:
                _ordinal(target, size, "transition target")
    expected = table.left_count * table.alphabet_size * table.right_count
    if type(table.outputs) is not tuple or len(table.outputs) != expected:
        raise ValueError("primitive output table has another domain")
    for output in table.outputs:
        _ordinal(output, table.alphabet_size, "output")
    _validate_channels(
        table.channels,
        expected,
        table.left_transitions,
        table.right_transitions,
        table.outputs,
        table.alphabet_size,
        table.right_count,
        table.blank,
    )
    _validate_observations(table.observations, expected)


def _fixed_padded_leaf_channels(
    boundary_left: int,
    boundary_right: int,
    output: int,
    symbol: int,
    blank: int,
) -> tuple[int, ...]:
    active = int(output != blank)
    absent = 1 - active
    return (
        boundary_left,
        boundary_right,
        output,
        active,
        absent,
        absent,
        active,
        output,
        output,
        active - int(symbol != blank) + 1,
        absent,
        output,
        0,
    )


def _validate_channels(
    channels: tuple[tuple[int, ...], ...],
    expected: int,
    left: tuple[tuple[int, ...], ...],
    right: tuple[tuple[int, ...], ...],
    outputs: tuple[int, ...],
    alphabet_size: int,
    right_count: int,
    blank: int,
) -> None:
    if type(channels) is not tuple or len(channels) != expected:
        raise ValueError("primitive semantic channels have another domain")
    for left_state in range(len(left)):
        for symbol in range(alphabet_size):
            for right_state in range(len(right)):
                index = (
                    left_state * alphabet_size + symbol
                ) * right_count + right_state
                value = channels[index]
                if type(value) is not tuple or len(value) != len(
                    PRIMITIVE_CHANNEL_SCHEMA
                ):
                    raise ValueError("primitive semantic channels have another schema")
                required = _fixed_padded_leaf_channels(
                    left[left_state][symbol],
                    right[right_state][symbol],
                    outputs[index],
                    symbol,
                    blank,
                )
                if value != required:
                    raise ValueError(
                        "primitive semantic channel behavior is inconsistent"
                    )


def _validate_observations(
    observations: tuple[tuple[int, ...], ...],
    expected: int,
) -> None:
    if type(observations) is not tuple or len(observations) != expected:
        raise ValueError("primitive occurrence observations have another domain")
    for observation in observations:
        if type(observation) is not tuple or len(observation) != len(
            PRIMITIVE_OCCURRENCE_SCHEMA
        ):
            raise ValueError("primitive occurrence observation has another schema")
        if any(type(value) is not int for value in observation):
            raise TypeError("primitive occurrence observations require exact integers")


def _representatives(partition: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(
        min(index for index, value in enumerate(partition) if value == cls)
        for cls in range(max(partition) + 1)
    )


def _permutation(values: tuple[int, ...], size: int, role: str) -> None:
    if type(values) is not tuple or len(values) != size:
        raise ValueError(f"{role} symmetry map has another domain")
    if any(type(value) is not int for value in values) or sorted(values) != list(
        range(size)
    ):
        raise ValueError(f"{role} symmetry map must be a bijection")
    if any(values[values[index]] != index for index in range(size)):
        raise ValueError(f"{role} symmetry map must be involutive")


def _ordinal(value: int, size: int, role: str) -> None:
    if type(value) is not int or not 0 <= value < size:
        raise ValueError(f"invalid {role}")


__all__ = [
    "MAX_PRIMITIVE_BEHAVIOR_TABLE_ENTRIES",
    "PRIMITIVE_CHANNEL_CONTRACT",
    "PRIMITIVE_CHANNEL_SCHEMA",
    "PRIMITIVE_OCCURRENCE_SCHEMA",
    "CertifiedLocalSymmetry",
    "LocalSymmetryWitness",
    "PrimitiveBehaviorKernel",
    "PrimitiveBehaviorQuotient",
    "PrimitiveBehaviorTable",
    "PrimitiveBehaviorWork",
    "capture_primitive_behavior",
    "certify_local_symmetry",
    "identity_symmetry",
    "minimize_primitive_behavior",
    "primitive_behavior_table_slots",
    "validate_certified_local_symmetry",
    "validate_primitive_behavior_quotient",
]

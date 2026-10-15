"""Immutable reverse/add field-action records and component-law contracts."""

from __future__ import annotations

from collections.abc import Callable, Hashable
from dataclasses import dataclass
from typing import TypeAlias

from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle
from number_compiler.arithmetic.fields.radial_innovation import (
    ReverseAddCyclotomicInnovationBlock,
)
from number_compiler.arithmetic.polynomials.cyclotomic_transport import (
    PowerTwoCyclotomicRadialQuotient,
)
from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID,
)

SemanticKey: TypeAlias = Hashable
BinarySemanticOp: TypeAlias = Callable[[SemanticKey, SemanticKey], SemanticKey]
UnarySemanticOp: TypeAlias = Callable[[SemanticKey], SemanticKey]
InnovationTransform: TypeAlias = Callable[
    [ReverseAddCyclotomicInnovationBlock], ReverseAddCyclotomicInnovationBlock
]

MAX_INNOVATION_ORDER = 16
MAX_RESIDUAL_CLASSES = 64
MAX_SEMANTIC_KEY_UNITS = 256


@dataclass(frozen=True, slots=True)
class ReverseDefectClassID(ArenaHandle):
    """Scoped residual behavior after deterministic algebraic factoring."""


@dataclass(frozen=True, slots=True)
class ProofMachineStateID(ArenaHandle):
    """Proof-only sort used to make the runtime boundary mechanically strict."""


@dataclass(frozen=True, slots=True)
class ReverseGeometry:
    """Symbolic geometry kept separate from bounded arithmetic payloads."""

    spatial_level: int
    orientation: int = 0
    phase: int = 0
    phase_count: int = 1
    halo_left: int = 0
    halo_right: int = 0

    def __post_init__(self) -> None:
        values = (
            self.spatial_level,
            self.orientation,
            self.phase,
            self.phase_count,
            self.halo_left,
            self.halo_right,
        )
        if any(type(value) is not int for value in values):
            raise TypeError("reverse geometry requires exact integer metadata")
        if self.spatial_level < 0 or self.orientation not in (0, 1):
            raise ValueError("invalid reverse geometry level or orientation")
        if self.phase_count <= 0 or not 0 <= self.phase < self.phase_count:
            raise ValueError("reverse phase is outside its bounded domain")
        if self.halo_left < 0 or self.halo_right < 0:
            raise ValueError("reverse halos must be nonnegative")

    def then(self, after: ReverseGeometry) -> ReverseGeometry:
        """Compose oriented geometry as a semidirect-product action."""
        if (
            self.spatial_level != after.spatial_level
            or self.phase_count != after.phase_count
        ):
            raise ValueError("reverse actions require matching spatial interfaces")
        pulled_left, pulled_right = after.halo_left, after.halo_right
        if self.orientation:
            pulled_left, pulled_right = pulled_right, pulled_left
        return ReverseGeometry(
            self.spatial_level,
            self.orientation ^ after.orientation,
            (self.phase + after.phase) % self.phase_count,
            self.phase_count,
            self.halo_left + pulled_left,
            self.halo_right + pulled_right,
        )

    def mirrored(self) -> ReverseGeometry:
        return ReverseGeometry(
            self.spatial_level,
            self.orientation ^ 1,
            self.phase,
            self.phase_count,
            self.halo_right,
            self.halo_left,
        )


@dataclass(frozen=True, slots=True)
class ReverseActionAutomorphisms:
    """Certified component automorphisms used by geometric aliases.

    Supplying :meth:`trivial` is an explicit declaration that both semantic
    component algebras and the innovation coordinate are invariant under the
    two transformations.  Nontrivial kernels should provide their proved maps.
    """

    mirror_residual: UnarySemanticOp
    conjugate_residual: UnarySemanticOp
    mirror_output: UnarySemanticOp
    conjugate_output: UnarySemanticOp
    mirror_innovation: InnovationTransform
    conjugate_innovation: InnovationTransform

    @classmethod
    def trivial(cls) -> ReverseActionAutomorphisms:
        def semantic_identity(value: SemanticKey) -> SemanticKey:
            return value

        def innovation_identity(
            value: ReverseAddCyclotomicInnovationBlock,
        ) -> ReverseAddCyclotomicInnovationBlock:
            return value

        return cls(
            semantic_identity,
            semantic_identity,
            semantic_identity,
            semantic_identity,
            innovation_identity,
            innovation_identity,
        )


@dataclass(frozen=True, slots=True)
class ReverseFieldAction:
    """Bounded factor action, not a complete source-cylinder occurrence.

    The innovation is a residue in the declared cyclotomic factor. Whole-source
    carry predicates, exact innovation geometry and successor admission cannot
    be recovered merely from equality of these records.
    """

    base: int
    radial: PowerTwoCyclotomicRadialQuotient
    innovation: tuple[int, ...]
    carry_forward: CarryFn
    carry_backward: CarryFn
    residual: ReverseDefectClassID
    output: CoordinateOutputMorphismID
    geometry: ReverseGeometry

    @property
    def source_annihilated(self) -> bool:
        return self.radial.annihilated


@dataclass(frozen=True, slots=True)
class ReverseFieldActionMetrics:
    action_count: int
    residual_count: int
    output_morphism_count: int
    compose_requests: int
    compose_early_hits: int
    compose_evaluations: int
    source_annihilation_derivations: int
    transform_hits: int

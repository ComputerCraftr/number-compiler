"""Algebraic reverse/add field actions without proof-machine state.

The arena in this module is deliberately smaller than the reverse/add proof
machine.  A node contains the radial/innovation affine action, a physical carry
endomorphism and reflected-domain summary, and scoped residual and output
semantics.  Exact slabs, rows, digits, and proof-machine states have no input
slot in this representation.

Physical carry runs only LSD to MSD. The historical ``carry_backward`` field
names the reflected-domain summary, not a second physical carry stream.

Composition uses ``before`` then ``after`` throughout.  Component algebras and
their mirror/conjugacy maps are supplied as certified operations; this module
validates and canonicalizes their results before publishing a field action.
"""

from __future__ import annotations

from collections.abc import Callable, Hashable, MutableMapping, MutableSequence
from dataclasses import dataclass
from typing import TYPE_CHECKING, TypeAlias, cast

from number_compiler.arithmetic.automata.symmetry_powering import ActionTransform
from number_compiler.arithmetic.carry.carry_monoid import CarryFn, compose_carry_fn
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.contracts.canonical_payload import (
    validate_bounded_semantic_key,
)
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.fields.radial_innovation import (
    ReverseAddCyclotomicInnovationBlock,
)
from number_compiler.arithmetic.fields.symbolic_innovation import RadialMultiplier
from number_compiler.arithmetic.polynomials.cyclotomic_transport import (
    PowerTwoCyclotomicRadialQuotient,
)
from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID,
    FieldCellActionID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict
from number_compiler.sequences.reverse_add.semantic_identity_cache import (
    SemanticIdentityMemoRecord,
    build_radial_identity,
    valid_radial_memo,
)

if TYPE_CHECKING:
    from number_compiler.sequences.reverse_add.coordinate_program import (
        ReverseCoordinateProgramArena,
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


_DEFAULT_REVERSE_GEOMETRY_1 = ReverseGeometry(0)


class ReverseFieldActionArena:
    """Index-owned canonical arena for algebraic reverse/add actions."""

    _ACTION_KIND = "field-cell-action"
    _RESIDUAL_KIND = "reverse-defect-class"
    _OUTPUT_KIND = "coordinate-output-morphism"

    @property
    def action_kind(self) -> str:
        """Scoped kind used when a shared image arena validates an action."""
        return self._ACTION_KIND

    @property
    def output_owner(self) -> ArenaToken:
        """Owner token used by shared coordinate-morphism validation."""
        return (
            self.owner
            if self._coordinate_programs is None
            else self._coordinate_programs.owner
        )

    @property
    def output_kind(self) -> str:
        return self._OUTPUT_KIND

    def __init__(
        self,
        *,
        base: int,
        order: int,
        residual_identity: SemanticKey,
        output_identity: SemanticKey,
        residual_compose: BinarySemanticOp,
        output_compose: BinarySemanticOp,
        automorphisms: ReverseActionAutomorphisms,
        geometry: ReverseGeometry = _DEFAULT_REVERSE_GEOMETRY_1,
        ledger: ResourceLedger | None = None,
        max_residual_classes: int = MAX_RESIDUAL_CLASSES,
        coordinate_programs: ReverseCoordinateProgramArena | None = None,
    ) -> None:
        if not callable(residual_compose) or not callable(output_compose):
            raise TypeError("reverse component composition must be executable")
        if type(automorphisms) is not ReverseActionAutomorphisms:
            raise TypeError("reverse actions require certified automorphism hooks")
        if type(base) is not int or base < 2 or type(order) is not int:
            raise ValueError(
                "reverse action arena requires a radix and cyclotomic order"
            )
        if order < 2 or order > MAX_INNOVATION_ORDER or order & (order - 1):
            raise ValueError("reverse cyclotomic order must be a bounded power of two")
        if type(geometry) is not ReverseGeometry:
            raise TypeError("reverse action identity requires symbolic geometry")
        if (
            type(max_residual_classes) is not int
            or not 1 <= max_residual_classes <= MAX_RESIDUAL_CLASSES
        ):
            raise ValueError("reverse residual certificate exceeds its bounded domain")
        self.ledger = ResourceLedger() if ledger is None else ledger
        if type(self.ledger) is not ResourceLedger:
            raise TypeError("reverse actions require an index resource ledger")
        self.ledger.register_execution_root(self)
        self.owner = ArenaToken("reverse-field-actions")
        self._base = base
        self._order = order
        self._residual_compose = residual_compose
        self._output_compose = output_compose
        self._automorphisms = automorphisms
        self._max_residual_classes = max_residual_classes
        if coordinate_programs is not None and (
            coordinate_programs.ledger is not self.ledger
            or coordinate_programs.base != base
        ):
            raise ValueError(
                "reverse coordinate programs require the action arena's index and radix"
            )
        self._coordinate_programs = coordinate_programs
        prefix = f"reverse-field-{len(self.ledger.inventory())}"
        self._residual_owner = self.ledger.register(
            prefix + "-residuals", "reverse_residual_node"
        )
        self._residual_key_owner = self.ledger.register(
            prefix + "-residual-keys", "reverse_residual_interner"
        )
        self._output_owner = self.ledger.register(
            prefix + "-outputs", "reverse_output_morphism"
        )
        self._output_key_owner = self.ledger.register(
            prefix + "-output-keys", "reverse_output_interner"
        )
        self._action_owner = self.ledger.register(
            prefix + "-actions", "reverse_field_action"
        )
        self._action_key_owner = self.ledger.register(
            prefix + "-action-keys", "reverse_action_interner"
        )
        self._compose_owner = self.ledger.register(
            prefix + "-compose", "reverse_action_composition"
        )
        self._transform_owner = self.ledger.register(
            prefix + "-transforms", "reverse_action_transform"
        )
        self._witness_owner = self.ledger.register(
            prefix + "-construction-witnesses",
            "reverse_action_construction_witness",
        )
        self._semantic_identity_owner = self.ledger.register(
            prefix + "-semantic-identities",
            "reverse_action_semantic_identity",
        )
        self._semantic_identity_issued_owner = self.ledger.register(
            prefix + "-semantic-identity-issued",
            "reverse_action_semantic_identity_authority",
        )
        self._residual_keys: MutableMapping[SemanticKey, ReverseDefectClassID] = (
            self.ledger.make_dict(self._residual_key_owner)
        )
        self._residuals: MutableSequence[SemanticKey] = self.ledger.make_list(
            self._residual_owner
        )
        self._output_keys: MutableMapping[SemanticKey, CoordinateOutputMorphismID] = (
            self.ledger.make_dict(self._output_key_owner)
        )
        self._outputs: MutableSequence[SemanticKey] = self.ledger.make_list(
            self._output_owner
        )
        self._action_keys: MutableMapping[tuple[object, ...], FieldCellActionID] = (
            self.ledger.make_dict(self._action_key_owner)
        )
        self._actions: MutableSequence[ReverseFieldAction] = self.ledger.make_list(
            self._action_owner
        )
        self._compose: MutableMapping[
            tuple[FieldCellActionID, FieldCellActionID], FieldCellActionID
        ] = self.ledger.make_dict(self._compose_owner)
        self._transforms: MutableMapping[
            tuple[FieldCellActionID, ActionTransform], FieldCellActionID
        ] = self.ledger.make_dict(self._transform_owner)
        self._witnesses: MutableMapping[
            FieldCellActionID, tuple[FieldCellActionID, FieldCellActionID]
        ] = self.ledger.make_dict(self._witness_owner)
        self._semantic_identities: LedgerDict[
            FieldCellActionID, SemanticIdentityMemoRecord
        ] = self.ledger.make_dict(
            self._semantic_identity_owner,
            nodes_per_entry=1,
            write_once=True,
        )
        self._semantic_identity_issued: LedgerDict[
            FieldCellActionID, SemanticIdentityMemoRecord
        ] = self.ledger.make_dict(
            self._semantic_identity_issued_owner,
            write_once=True,
        )
        self.ledger.register_container(
            self._compose_owner,
            self._compose,
            payloads=self._compose.items,
            composition_count=lambda: len(self._compose),
        )
        self.ledger.register_container(
            self._semantic_identity_owner,
            self._semantic_identities,
            node_count=lambda: len(self._semantic_identities),
            payloads=self._semantic_identities.items,
        )
        self.ledger.register_container(
            self._semantic_identity_issued_owner,
            self._semantic_identity_issued,
            payloads=self._semantic_identity_issued.items,
        )
        self.compose_requests = 0
        self.compose_early_hits = 0
        self.compose_evaluations = 0
        self.source_annihilation_derivations = 0
        self.transform_hits = 0
        residual = self.intern_residual(residual_identity)
        output = (
            self.intern_output(output_identity)
            if coordinate_programs is None
            else coordinate_programs.identity
        )
        self.identity = self.intern(
            base=base,
            innovation=ReverseAddCyclotomicInnovationBlock.identity(
                order=order, bits=5
            ),
            carry_forward=CarryFn.ID,
            carry_backward=CarryFn.ID,
            residual=residual,
            output=output,
            geometry=geometry,
        )

    @staticmethod
    def _validate_semantic_key(key: SemanticKey) -> None:
        validate_bounded_semantic_key(key, max_units=MAX_SEMANTIC_KEY_UNITS)

    def intern_residual(self, key: SemanticKey) -> ReverseDefectClassID:
        self._validate_semantic_key(key)
        found = self._residual_keys.get(key)
        if found is not None:
            return found
        if len(self._residuals) >= self._max_residual_classes:
            raise ValueError("reverse residual certificate failed to remain bounded")
        result = ReverseDefectClassID(
            self.owner, self._RESIDUAL_KIND, len(self._residuals)
        )
        self.ledger.reserve_many(
            ((self._residual_owner, 1, 1), (self._residual_key_owner, 1, 0))
        )
        self._residuals.append(key)
        self._residual_keys[key] = result
        return result

    def intern_output(self, key: SemanticKey) -> CoordinateOutputMorphismID:
        self._validate_semantic_key(key)
        if self._coordinate_programs is not None:
            return self._coordinate_programs.atom(key)
        found = self._output_keys.get(key)
        if found is not None:
            return found
        result = CoordinateOutputMorphismID(
            self.owner, self._OUTPUT_KIND, len(self._outputs)
        )
        self.ledger.reserve_many(
            ((self._output_owner, 1, 1), (self._output_key_owner, 1, 0))
        )
        self._outputs.append(key)
        self._output_keys[key] = result
        return result

    def _residual_key(self, reference: ReverseDefectClassID) -> SemanticKey:
        if type(reference) is not ReverseDefectClassID:
            raise TypeError("field actions require a residual defect-class ID")
        reference.validate(self.owner, self._RESIDUAL_KIND, size=len(self._residuals))
        return self._residuals[reference.local_id]

    def _output_key(self, reference: CoordinateOutputMorphismID) -> SemanticKey:
        if self._coordinate_programs is not None:
            program = self._coordinate_programs.resolve(reference)
            return SemanticIdentity(
                "reverse-coordinate-program-v1",
                (program.base, program.pair_steps, program.normalized, program.atom),
            )
        if type(reference) is not CoordinateOutputMorphismID:
            raise TypeError("field actions require a coordinate-output morphism ID")
        reference.validate(self.owner, self._OUTPUT_KIND, size=len(self._outputs))
        return self._outputs[reference.local_id]

    def validate_action(self, reference: FieldCellActionID) -> None:
        """Validate the shared runtime sort and this arena's scoped identity."""
        self.resolve(reference)

    def validate_output(self, reference: CoordinateOutputMorphismID) -> None:
        """Reject foreign or wrong-sort morphisms before an image lookup."""
        self._output_key(reference)

    def output_semantics(self, reference: CoordinateOutputMorphismID) -> SemanticKey:
        """Return the bounded canonical program key, never an emitted tape."""
        return self._output_key(reference)

    def temporal_action(self, reference: FieldCellActionID) -> RadialMultiplier:
        """Return the exact centered temporal action ``(q, r)``.

        Reverse/add occurrence selection may carry innovation, carry, output,
        admission and geometric data, but after rebasing an authenticated
        source occurrence to its target origin the linear action is exactly
        ``U -> 2**q * (1+z)**r * U``.  Therefore only the no-growth and growth
        counts belong to temporal ActionID.
        """
        action = self.resolve(reference)
        return RadialMultiplier(action.radial.no_growth, action.radial.growth)

    def semantic_identity(self, reference: FieldCellActionID) -> SemanticIdentity:
        """Return the centered temporal semantic identity, never occurrence data.

        The complete field-action record is an occurrence/interface carrier.
        Its innovation, carry summaries, residual/output bindings and geometry
        deliberately do not split this identity.
        """
        action = self.resolve(reference)
        if type(action.radial) is not PowerTwoCyclotomicRadialQuotient:
            raise ValueError("reverse action radial coordinates changed")
        try:
            action.radial.__post_init__()
        except (TypeError, ValueError) as error:
            raise ValueError("reverse action radial coordinates changed") from error
        self.ledger.bump("reverse_field_action_semantic_identity_requests")
        if reference in self._semantic_identities:
            cached = self._semantic_identities[reference]
            self.ledger.bump(
                "reverse_field_action_identity_validation_radial_bit_work",
                max(1, action.radial.no_growth.bit_length())
                + max(1, action.radial.growth.bit_length()),
            )
            issued = self._semantic_identity_issued.get(reference)
            if not valid_radial_memo(
                reference,
                id(action),
                action.radial,
                cached,
                issued,
                self.owner,
                self._ACTION_KIND,
                len(self._actions),
            ):
                raise ValueError("cached reverse semantic identity lost its seal")
            self.ledger.bump("reverse_field_action_semantic_identity_cache_hits")
            return cached[3]
        if reference in self._semantic_identity_issued:
            raise ValueError("reverse semantic identity lost its issued cache record")

        self.ledger.bump("reverse_field_action_semantic_identity_cache_misses")
        radial = action.radial
        self.ledger.bump(
            "reverse_field_action_identity_radial_bit_work",
            max(1, radial.no_growth.bit_length()) + max(1, radial.growth.bit_length()),
        )
        try:
            self.ledger.reserve_many(
                (
                    (self._semantic_identity_owner, 1, 1),
                    (self._semantic_identity_issued_owner, 1, 0),
                )
            )
        except BlockContextBudgetExceeded:
            # Identity construction remains exact when the optional memo has
            # no room under a stricter request budget.
            self.ledger.bump("reverse_field_action_semantic_identity_cache_bypasses")
            return self._compute_semantic_identity(radial)

        record: SemanticIdentityMemoRecord | None = None
        try:
            identity = self._compute_semantic_identity(radial)
            record = (
                reference,
                id(action),
                (radial.no_growth, radial.growth),
                identity,
                identity.digest,
                identity.behavior,
            )
            self._semantic_identities[reference] = record
            self._semantic_identity_issued[reference] = record
        except BaseException:
            issued_removed = (
                self._semantic_identity_issued._rollback_unpublished(reference, record)
                if record is not None
                else False
            )
            if not issued_removed:
                self.ledger.release(self._semantic_identity_issued_owner, entries=1)
            identity_removed = (
                self._semantic_identities._rollback_unpublished(reference, record)
                if record is not None
                else False
            )
            if not identity_removed:
                self.ledger.release(self._semantic_identity_owner, entries=1, nodes=1)
            raise
        self.ledger.bump(
            "reverse_field_action_identity_retained_payload_bytes",
            len(cast(str, identity.behavior[1]))
            + len(cast(str, identity.behavior[2]))
            + len(identity.digest),
        )
        self.ledger.bump("reverse_field_action_semantic_identity_publications")
        return identity

    def _compute_semantic_identity(
        self,
        radial: PowerTwoCyclotomicRadialQuotient,
    ) -> SemanticIdentity:
        try:
            identity = build_radial_identity(radial)
        except BaseException:
            self.ledger.bump("reverse_field_action_semantic_identity_failed_work")
            raise
        radial_chars = len(cast(str, identity.behavior[1])) + len(
            cast(str, identity.behavior[2])
        )
        self.ledger.bump(
            "reverse_field_action_identity_radial_decimal_digit_work",
            radial_chars,
        )
        self.ledger.bump(
            "reverse_field_action_identity_transient_payload_bytes",
            radial_chars + len(identity.digest),
        )
        return identity

    def occurrence_identity(self, reference: FieldCellActionID) -> SemanticIdentity:
        """Return the complete source-free occurrence/interface identity.

        This is the old pre-rebase semantic payload under an explicit name.
        Consumers that must authenticate a particular published interface may
        use it; temporal equality and powering must use :meth:`temporal_action`
        or :meth:`semantic_identity` instead.
        """
        action = self.resolve(reference)

        def component(role: str, value: object) -> SemanticIdentity:
            return SemanticIdentity(role, (role, value))

        behavior = (
            "reverse-field-occurrence-v1",
            component("base", action.base),
            component("radial-derived", action.radial.canonical_key),
            component("innovation", action.innovation),
            f"carry-forward:{action.carry_forward.value}",
            f"carry-backward:{action.carry_backward.value}",
            component("residual", self._residual_key(action.residual)),
            component("output", self._output_key(action.output)),
            component(
                "geometry",
                (
                    action.geometry.spatial_level,
                    action.geometry.orientation,
                    action.geometry.phase,
                    action.geometry.phase_count,
                    action.geometry.halo_left,
                    action.geometry.halo_right,
                ),
            ),
        )
        return SemanticIdentity("reverse-field-occurrence", behavior)

    def _canonical_block(
        self,
        block: ReverseAddCyclotomicInnovationBlock,
    ) -> ReverseAddCyclotomicInnovationBlock:
        if type(block) is not ReverseAddCyclotomicInnovationBlock:
            raise TypeError("reverse actions require a bounded innovation block")
        if block.bits != 5 or block.order != self._order:
            raise ValueError("production reverse innovation is bounded modulo 32")
        return ReverseAddCyclotomicInnovationBlock(
            block.order,
            block.bits,
            block.steps,
            block.growth,
            block.innovation,
            0,
        )

    @staticmethod
    def _block(action: ReverseFieldAction) -> ReverseAddCyclotomicInnovationBlock:
        radial = action.radial
        return ReverseAddCyclotomicInnovationBlock(
            radial.classes * 2,
            radial.bits,
            radial.steps,
            radial.growth,
            action.innovation,
            0,
        )

    def _action_key(
        self,
        base: int,
        block: ReverseAddCyclotomicInnovationBlock,
        carry_forward: CarryFn,
        carry_backward: CarryFn,
        residual: ReverseDefectClassID,
        output: CoordinateOutputMorphismID,
        geometry: ReverseGeometry,
    ) -> tuple[object, ...]:
        return (
            base,
            block.radial.canonical_key,
            block.innovation,
            carry_forward,
            carry_backward,
            residual,
            output,
            geometry,
        )

    def intern(
        self,
        *,
        base: int,
        innovation: ReverseAddCyclotomicInnovationBlock,
        carry_forward: CarryFn,
        carry_backward: CarryFn,
        residual: ReverseDefectClassID,
        output: CoordinateOutputMorphismID,
        geometry: ReverseGeometry,
        _construction: tuple[FieldCellActionID, FieldCellActionID] | None = None,
    ) -> FieldCellActionID:
        if type(base) is not int or base != self._base:
            raise ValueError("reverse field action belongs to another radix arena")
        if type(carry_forward) is not CarryFn or type(carry_backward) is not CarryFn:
            raise TypeError("reverse field action requires canonical carry functions")
        if type(geometry) is not ReverseGeometry:
            raise TypeError("reverse field action requires symbolic geometry")
        self._residual_key(residual)
        self._output_key(output)
        block = self._canonical_block(innovation)
        key = self._action_key(
            base,
            block,
            carry_forward,
            carry_backward,
            residual,
            output,
            geometry,
        )
        if _construction is not None:
            if type(_construction) is not tuple or len(_construction) != 2:
                raise TypeError("reverse construction witness requires two action IDs")
            self.resolve(_construction[0])
            self.resolve(_construction[1])
        found = self._action_keys.get(key)
        if found is not None:
            return found
        result = FieldCellActionID(self.owner, self._ACTION_KIND, len(self._actions))
        reservations = [
            (self._action_owner, 1, 1),
            (self._action_key_owner, 1, 0),
        ]
        if _construction is not None:
            reservations.append((self._witness_owner, 1, 0))
        self.ledger.reserve_many(tuple(reservations))
        self._actions.append(
            ReverseFieldAction(
                base,
                block.radial,
                block.innovation,
                carry_forward,
                carry_backward,
                residual,
                output,
                geometry,
            )
        )
        self._action_keys[key] = result
        if _construction is not None:
            self._witnesses[result] = _construction
        self.ledger.bump("field_action_publications")
        return result

    def resolve(self, reference: FieldCellActionID) -> ReverseFieldAction:
        if type(reference) is not FieldCellActionID:
            raise TypeError("expected a reverse field-action ID")
        reference.validate(self.owner, self._ACTION_KIND, size=len(self._actions))
        return self._actions[reference.local_id]

    def action_children(
        self,
        reference: FieldCellActionID,
    ) -> tuple[FieldCellActionID, FieldCellActionID] | None:
        """Return the first construction witness for a canonical action."""
        self.resolve(reference)
        return self._witnesses.get(reference)

    def compose(
        self,
        before: FieldCellActionID,
        after: FieldCellActionID,
    ) -> FieldCellActionID:
        """Apply ``before`` and then ``after`` without visiting field digits."""
        first, second = self.resolve(before), self.resolve(after)
        self.compose_requests += 1
        self.ledger.bump("temporal_parent_requests")
        self.ledger.bump("diamond_temporal_composition_requests")
        cache_key = (before, after)
        found = self._compose.get(cache_key)
        if found is not None:
            self.compose_early_hits += 1
            self.ledger.bump("temporal_parent_early_hits")
            self.ledger.bump("diamond_temporal_composition_hits")
            return found
        if first.base != second.base:
            raise ValueError("cannot compose reverse actions for different radices")
        block = self._block(first).then(self._block(second))
        residual_key = self._residual_compose(
            self._residual_key(first.residual),
            self._residual_key(second.residual),
        )
        output_key = (
            None
            if self._coordinate_programs is not None
            else self._output_compose(
                self._output_key(first.output),
                self._output_key(second.output),
            )
        )
        # Validate the full semantic result before any component interner is
        # mutated. Resource publication then sees canonical bounded keys only.
        self._validate_semantic_key(residual_key)
        if output_key is not None:
            self._validate_semantic_key(output_key)
        residual = self.intern_residual(residual_key)
        output = (
            self._coordinate_programs.compose(first.output, second.output)
            if self._coordinate_programs is not None
            else self.intern_output(output_key)
        )
        result = self.intern(
            base=first.base,
            innovation=block,
            carry_forward=compose_carry_fn(second.carry_forward, first.carry_forward),
            carry_backward=compose_carry_fn(
                second.carry_backward, first.carry_backward
            ),
            residual=residual,
            output=output,
            geometry=first.geometry.then(second.geometry),
            _construction=(before, after),
        )
        if self.resolve(result).source_annihilated and not first.source_annihilated:
            self.source_annihilation_derivations += 1
            self.ledger.bump("reverse_field_action_source_annihilation_derivations")
        self.ledger.reserve(self._compose_owner, 1, 0)
        self._compose[cache_key] = result
        self.compose_evaluations += 1
        self.ledger.bump("temporal_parent_compositions")
        self.ledger.bump("diamond_temporal_composition_evaluations")
        self.ledger.bump("radial_action_operations")
        self.ledger.bump("carry_action_operations", 2)
        self.ledger.bump("innovation_action_operations")
        self.ledger.bump("residual_refinement_operations")
        self.ledger.bump("output_morphism_operations")
        return result

    def power(self, action: FieldCellActionID, exponent: int) -> FieldCellActionID:
        """Build a temporal power with at most two compositions per exponent bit."""
        self.resolve(action)
        if type(exponent) is not int:
            raise TypeError("reverse temporal exponent must be an exact integer")
        if exponent < 0:
            raise ValueError("reverse temporal exponent must be nonnegative")
        if exponent == 0:
            return self.identity
        # Do not compose the first selected bit with the identity.  Apart from
        # needless component work, that used to discover the already-published
        # primitive only after reducing every algebraic component.  Canonical
        # parent identity must be known before a cache probe is counted as a
        # composition evaluation.
        result: FieldCellActionID | None = None
        square = action
        remaining = exponent
        while remaining:
            if remaining & 1:
                result = square if result is None else self.compose(result, square)
            remaining >>= 1
            if remaining:
                square = self.compose(square, square)
        if result is None:
            raise AssertionError("positive reverse exponent produced no action")
        return result

    @staticmethod
    def _conjugate_carry(value: CarryFn) -> CarryFn:
        if value is CarryFn.CONST0:
            return CarryFn.CONST1
        if value is CarryFn.CONST1:
            return CarryFn.CONST0
        if value is CarryFn.ID:
            return CarryFn.ID
        raise AssertionError(value)

    def _transformed_components(
        self, action: ReverseFieldAction, transform: ActionTransform
    ) -> tuple[
        ReverseAddCyclotomicInnovationBlock,
        SemanticKey,
        SemanticKey,
        CarryFn,
        CarryFn,
        ReverseGeometry,
    ]:
        """Compute transform semantics without interning or changing arena state."""
        block = self._block(action)
        residual_key = self._residual_key(action.residual)
        output_key = self._output_key(action.output)
        forward, backward = action.carry_forward, action.carry_backward
        geometry = action.geometry
        hooks = self._automorphisms
        if transform & ActionTransform.CONJUGATE:
            block = self._canonical_block(hooks.conjugate_innovation(block))
            residual_key = hooks.conjugate_residual(residual_key)
            output_key = hooks.conjugate_output(output_key)
            forward = self._conjugate_carry(forward)
            backward = self._conjugate_carry(backward)
        if transform & ActionTransform.MIRROR:
            block = self._canonical_block(hooks.mirror_innovation(block))
            residual_key = hooks.mirror_residual(residual_key)
            output_key = hooks.mirror_output(output_key)
            forward, backward = backward, forward
            geometry = geometry.mirrored()
        return block, residual_key, output_key, forward, backward, geometry

    def transformed(
        self,
        reference: FieldCellActionID,
        transform: ActionTransform,
    ) -> FieldCellActionID:
        action = self.resolve(reference)
        if type(transform) is not ActionTransform or int(transform) & ~3:
            raise TypeError("invalid reverse action transform")
        if transform is ActionTransform.IDENTITY:
            return reference
        if self._coordinate_programs is not None:
            raise ValueError(
                "reverse coordinate programs have no certified mirror/conjugacy transform"
            )
        cache_key = (reference, transform)
        found = self._transforms.get(cache_key)
        if found is not None:
            self.transform_hits += 1
            return found
        block, residual_key, output_key, forward, backward, geometry = (
            self._transformed_components(action, transform)
        )
        self._validate_semantic_key(residual_key)
        self._validate_semantic_key(output_key)
        result = self.intern(
            base=action.base,
            innovation=block,
            carry_forward=forward,
            carry_backward=backward,
            residual=self.intern_residual(residual_key),
            output=self.intern_output(output_key),
            geometry=geometry,
        )
        self.ledger.reserve(self._transform_owner, 1, 0)
        self._transforms[cache_key] = result
        return result

    def metrics(self) -> ReverseFieldActionMetrics:
        outputs = (
            len(self._outputs)
            if self._coordinate_programs is None
            else self._coordinate_programs.metrics().programs
        )
        return ReverseFieldActionMetrics(
            len(self._actions),
            len(self._residuals),
            outputs,
            self.compose_requests,
            self.compose_early_hits,
            self.compose_evaluations,
            self.source_annihilation_derivations,
            self.transform_hits,
        )


__all__ = [
    "MAX_INNOVATION_ORDER",
    "MAX_RESIDUAL_CLASSES",
    "MAX_SEMANTIC_KEY_UNITS",
    "CoordinateOutputMorphismID",
    "FieldCellActionID",
    "ProofMachineStateID",
    "ReverseActionAutomorphisms",
    "ReverseDefectClassID",
    "ReverseFieldAction",
    "ReverseFieldActionArena",
    "ReverseFieldActionMetrics",
    "ReverseGeometry",
]

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

from collections.abc import MutableMapping, MutableSequence
from typing import TYPE_CHECKING, cast

from number_compiler.arithmetic.automata.symmetry_powering import ActionTransform
from number_compiler.arithmetic.carry.carry_monoid import CarryFn, compose_carry_fn
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.contracts.canonical_payload import (
    validate_bounded_semantic_key,
)
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.contracts.semantic_identity import (
    SemanticIdentity,
    SemanticIdentityDomain,
)
from number_compiler.arithmetic.fields.radial_innovation import (
    RadialMultiplier,
    ReverseAddCyclotomicInnovationBlock,
)
from number_compiler.arithmetic.polynomials.cyclotomic_transport import (
    PowerTwoCyclotomicRadialQuotient,
)
from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID,
    FieldCellActionID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys
from number_compiler.resources.metric_keys import shared as _shared_keys
from number_compiler.resources.stores import LedgerDict
from number_compiler.sequences.reverse_add.field_action_audit import (
    ReverseFieldActionAudit,
)
from number_compiler.sequences.reverse_add.semantic_identity_cache import (
    SemanticIdentityMemoRecord,
    build_radial_identity,
    valid_radial_memo,
)
from number_compiler.sequences.reverse_add.semantic_tags import (
    REVERSE_FIELD_OCCURRENCE_TAG,
)

if TYPE_CHECKING:
    from number_compiler.sequences.reverse_add.coordinate_program import (
        ReverseCoordinateProgramArena,
    )


from number_compiler.sequences.reverse_add.field_action_types import (
    MAX_INNOVATION_ORDER,
    MAX_RESIDUAL_CLASSES,
    MAX_SEMANTIC_KEY_UNITS,
    BinarySemanticOp,
    ProofMachineStateID,
    ReverseActionAutomorphisms,
    ReverseDefectClassID,
    ReverseFieldAction,
    ReverseFieldActionMetrics,
    ReverseGeometry,
    SemanticKey,
)

_DEFAULT_REVERSE_GEOMETRY_1 = ReverseGeometry(0)


class ReverseFieldActionArena(ReverseFieldActionAudit):
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
        from number_compiler.sequences.reverse_add.field_action_payload_audit import (
            register_reverse_field_action_contract,
        )

        register_reverse_field_action_contract(self)

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
                SemanticIdentityDomain.REVERSE_COORDINATE_PROGRAM,
                (program.base, program.pair_steps, program.normalized, program.atom),
            )
        if type(reference) is not CoordinateOutputMorphismID:
            raise TypeError("field actions require a coordinate-output morphism ID")
        reference.validate(self.owner, self._OUTPUT_KIND, size=len(self._outputs))
        return self._outputs[reference.local_id]

    def validate_action(self, reference: FieldCellActionID) -> None:
        """Validate the shared runtime sort and this arena's scoped identity."""
        self.resolve(reference)

    def validate_residual(self, reference: ReverseDefectClassID) -> None:
        """Validate a residual handle against this exact arena and store."""
        self._residual_key(reference)

    def validate_output(self, reference: CoordinateOutputMorphismID) -> None:
        """Reject foreign or wrong-sort morphisms before an image lookup."""
        self._output_key(reference)

    def output_semantics(self, reference: CoordinateOutputMorphismID) -> SemanticKey:
        """Return the bounded canonical program key, never an emitted tape."""
        return self._output_key(reference)

    def audit_expected_action_key(
        self, action: ReverseFieldAction
    ) -> tuple[object, ...]:
        """Return the canonical key recomputed from a typed action record."""
        if type(action) is not ReverseFieldAction:
            raise TypeError("reverse action audit requires an exact action record")
        return self._action_key(
            action.base,
            self._block(action),
            action.carry_forward,
            action.carry_backward,
            action.residual,
            action.output,
            action.geometry,
        )

    def temporal_action(self, reference: FieldCellActionID) -> RadialMultiplier:
        """Return the radial exponents recorded on this algebraic action.

        The action ID does not itself carry source authority. Its ``growth``
        exponent is the physical width-growth count only when the producer
        authenticated and composed source-specific successor clauses. The
        recursive cutover's current generic primitive has growth zero for all
        sources, so this projection must not be used to infer that occurrence's
        active width.
        """
        action = self.resolve(reference)
        return RadialMultiplier(action.radial.no_growth, action.radial.growth)

    def semantic_identity(
        self, reference: FieldCellActionID, *, audit: bool = False
    ) -> SemanticIdentity:
        """Return the centered temporal semantic identity, never occurrence data.

        The complete field-action record is an occurrence/interface carrier.
        Its innovation, carry summaries, residual/output bindings and geometry
        deliberately do not split this identity.
        """
        if type(audit) is not bool:
            raise TypeError("identity audit selection must be Boolean")
        action = self.resolve(reference)
        if type(action.radial) is not PowerTwoCyclotomicRadialQuotient:
            raise ValueError("reverse action radial coordinates changed")
        try:
            action.radial.__post_init__()
        except (TypeError, ValueError) as error:
            raise ValueError("reverse action radial coordinates changed") from error
        if audit:
            self.ledger.bump(
                _reverse_add_keys.REVERSE_PAYLOAD_AUDIT_IDENTITY_OPERAND_BITS,
                max(1, action.radial.no_growth.bit_length())
                + max(1, action.radial.growth.bit_length()),
            )
        else:
            self.ledger.bump(
                _reverse_add_keys.REVERSE_FIELD_ACTION_SEMANTIC_IDENTITY_REQUESTS
            )
        if reference in self._semantic_identities:
            cached = self._semantic_identities[reference]
            if not audit:
                self.ledger.bump(
                    _reverse_add_keys.REVERSE_FIELD_ACTION_IDENTITY_VALIDATION_RADIAL_BIT_WORK,
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
            if not audit:
                self.ledger.bump(
                    _reverse_add_keys.REVERSE_FIELD_ACTION_SEMANTIC_IDENTITY_CACHE_HITS
                )
            return cached[3]
        if reference in self._semantic_identity_issued:
            raise ValueError("reverse semantic identity lost its issued cache record")
        if audit:
            # Explicit audits may check a capacity-bypassed identity, but must
            # never publish a memo or inflate execution cache counters.
            return build_radial_identity(action.radial)

        self.ledger.bump(
            _reverse_add_keys.REVERSE_FIELD_ACTION_SEMANTIC_IDENTITY_CACHE_MISSES
        )
        radial = action.radial
        self.ledger.bump(
            _reverse_add_keys.REVERSE_FIELD_ACTION_IDENTITY_RADIAL_BIT_WORK,
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
            self.ledger.bump(
                _reverse_add_keys.REVERSE_FIELD_ACTION_SEMANTIC_IDENTITY_CACHE_BYPASSES
            )
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
                self._semantic_identity_issued.rollback_unpublished(reference, record)
                if record is not None
                else False
            )
            if not issued_removed:
                self.ledger.release(self._semantic_identity_issued_owner, entries=1)
            identity_removed = (
                self._semantic_identities.rollback_unpublished(reference, record)
                if record is not None
                else False
            )
            if not identity_removed:
                self.ledger.release(self._semantic_identity_owner, entries=1, nodes=1)
            raise
        self.ledger.bump(
            _reverse_add_keys.REVERSE_FIELD_ACTION_IDENTITY_RETAINED_PAYLOAD_BYTES,
            len(cast(str, identity.behavior[1]))
            + len(cast(str, identity.behavior[2]))
            + len(identity.digest),
        )
        self.ledger.bump(
            _reverse_add_keys.REVERSE_FIELD_ACTION_SEMANTIC_IDENTITY_PUBLICATIONS
        )
        return identity

    def _compute_semantic_identity(
        self,
        radial: PowerTwoCyclotomicRadialQuotient,
    ) -> SemanticIdentity:
        try:
            identity = build_radial_identity(radial)
        except BaseException:
            self.ledger.bump(
                _reverse_add_keys.REVERSE_FIELD_ACTION_SEMANTIC_IDENTITY_FAILED_WORK
            )
            raise
        radial_chars = len(cast(str, identity.behavior[1])) + len(
            cast(str, identity.behavior[2])
        )
        self.ledger.bump(
            _reverse_add_keys.REVERSE_FIELD_ACTION_IDENTITY_RADIAL_DECIMAL_DIGIT_WORK,
            radial_chars,
        )
        self.ledger.bump(
            _reverse_add_keys.REVERSE_FIELD_ACTION_IDENTITY_TRANSIENT_PAYLOAD_BYTES,
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
            return SemanticIdentity(SemanticIdentityDomain.ANONYMOUS, (role, value))

        behavior = (
            REVERSE_FIELD_OCCURRENCE_TAG,
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
        return SemanticIdentity(
            SemanticIdentityDomain.REVERSE_FIELD_OCCURRENCE, behavior
        )

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
        self.ledger.bump(_shared_keys.FIELD_ACTION_PUBLICATIONS)
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
        self.ledger.bump(_shared_keys.TEMPORAL_PARENT_REQUESTS)
        self.ledger.bump(_shared_keys.DIAMOND_TEMPORAL_COMPOSITION_REQUESTS)
        cache_key = (before, after)
        found = self._compose.get(cache_key)
        if found is not None:
            self.compose_early_hits += 1
            self.ledger.bump(_shared_keys.TEMPORAL_PARENT_EARLY_HITS)
            self.ledger.bump(_shared_keys.DIAMOND_TEMPORAL_COMPOSITION_HITS)
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
            self.ledger.bump(
                _reverse_add_keys.REVERSE_FIELD_ACTION_SOURCE_ANNIHILATION_DERIVATIONS
            )
        self.ledger.reserve(self._compose_owner, 1, 0)
        self._compose[cache_key] = result
        self.compose_evaluations += 1
        self.ledger.bump(_shared_keys.TEMPORAL_PARENT_COMPOSITIONS)
        self.ledger.bump(_shared_keys.DIAMOND_TEMPORAL_COMPOSITION_EVALUATIONS)
        self.ledger.bump(_reverse_add_keys.RADIAL_ACTION_OPERATIONS)
        self.ledger.bump(_reverse_add_keys.CARRY_ACTION_OPERATIONS, 2)
        self.ledger.bump(_reverse_add_keys.INNOVATION_ACTION_OPERATIONS)
        self.ledger.bump(_reverse_add_keys.RESIDUAL_REFINEMENT_OPERATIONS)
        self.ledger.bump(_reverse_add_keys.OUTPUT_MORPHISM_OPERATIONS)
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

"""Canonical algebraic carrier for powered Collatz field cells.

The carrier retains only finite characters, a bounded 3-adic innovation and
scoped references to symbolic root, affine and output programs.  Exact tails,
future suffixes and affine constants belong to the program provider or explicit
lowering boundary; they can never enter a field-action record.
"""

from __future__ import annotations

from collections.abc import Mapping, MutableMapping, MutableSequence
from dataclasses import dataclass
from types import MappingProxyType
from typing import Final, Literal, Protocol, TypeAlias

from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
)
from number_compiler.arithmetic.contracts.semantic_identity import (
    SemanticIdentity,
    SemanticIdentityDomain,
)
from number_compiler.arithmetic.fields.adic_morphism import (
    PadicAffineMorphism,
    PadicRadialQuotient,
)
from number_compiler.arithmetic.fields.morphism_core import semigroup_power
from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID,
    FieldCellActionID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.resources.metric_keys import shared as _shared_keys
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditEntry,
    PayloadAuditStoreBinding,
    register_payload_audit_contract,
)
from number_compiler.sequences.collatz.character import CollatzRadialCharacter
from number_compiler.sequences.collatz.defect_arena import (
    CollatzDefectArena as _CollatzDefectArena,
)
from number_compiler.sequences.collatz.defect_arena import (
    CollatzDefectClassID as _CollatzDefectClassID,
)

ProgramRole = Literal[
    "root",
    "affine",
    "output",
    "physical-tick",
    "valuation",
    "frame",
]
_PROGRAM_ROLES: tuple[ProgramRole, ...] = (
    "root",
    "affine",
    "output",
    "physical-tick",
    "valuation",
    "frame",
)
_ACTION_KIND = "field-cell-action"
_OUTPUT_KIND = "coordinate-output-morphism"
COLLATZ_CHARACTER_ACTION_TAG: Final[str] = "collatz-character-action-v1"
COLLATZ_RESIDUAL_DEFECT_TAG: Final[str] = "collatz-residual-defect-v1"
COLLATZ_ACTION_GEOMETRY_TAG: Final[str] = "collatz-action-geometry-v1"
COLLATZ_FIELD_ACTION_TAG: Final[str] = "collatz-field-action-v2"
GEOMETRY_LEVEL_FIELD: Final = "level"
GEOMETRY_PHASE_FIELD: Final = "phase"
GEOMETRY_LEFT_HALO_FIELD: Final = "halo-left"
GEOMETRY_RIGHT_HALO_FIELD: Final = "halo-right"


class CollatzSymbolicProgramAlgebra(Protocol):
    """Canonical symbolic program operations supplied by the shared runtime."""

    def identity(self, role: ProgramRole) -> ActionProgramID: ...

    def validate(self, role: ProgramRole, reference: ActionProgramID) -> int: ...

    def semantic_identity(
        self,
        role: ProgramRole,
        reference: ActionProgramID,
    ) -> SemanticIdentity: ...

    def audit_semantic_identity(
        self,
        role: ProgramRole,
        reference: ActionProgramID,
    ) -> SemanticIdentity: ...

    def composed_semantic_identity(
        self,
        role: ProgramRole,
        before: ActionProgramID,
        after: ActionProgramID,
    ) -> SemanticIdentity: ...

    def compose(
        self,
        role: ProgramRole,
        before: ActionProgramID,
        after: ActionProgramID,
    ) -> ActionProgramID: ...


# Compatibility spelling for callers of the family module.  Production image
# arenas must see the shared runtime action sort, never a family-local alias.
CollatzFieldActionID: TypeAlias = FieldCellActionID


@dataclass(frozen=True, slots=True)
class CollatzCharacterAction:
    """Finite growth and radial-character phases."""

    growth_phase: int
    radial: tuple[CollatzRadialCharacter, ...]

    def __post_init__(self) -> None:
        if type(self.growth_phase) is not int or self.growth_phase not in (0, 1):
            raise ValueError("growth character phase must be binary")
        if type(self.radial) is not tuple or any(
            type(character) is not CollatzRadialCharacter for character in self.radial
        ):
            raise TypeError("radial characters must be an immutable typed tuple")
        orders = tuple(character.order for character in self.radial)
        if tuple(sorted(set(orders))) != orders:
            raise ValueError("radial character orders must be sorted and unique")

    def then(self, other: CollatzCharacterAction) -> CollatzCharacterAction:
        if tuple(item.order for item in self.radial) != tuple(
            item.order for item in other.radial
        ):
            raise ValueError("character actions use different radial signatures")
        return CollatzCharacterAction(
            self.growth_phase ^ other.growth_phase,
            tuple(
                first.then(second)
                for first, second in zip(self.radial, other.radial, strict=True)
            ),
        )


@dataclass(frozen=True, slots=True)
class CollatzCocyclePrograms:
    """Source-parametric tick, valuation, and frame cocycles.

    These are executable functions of the bounded interface and source image.
    Storing their observed integer values here would specialize a temporal
    action to one trajectory and make otherwise different branch schedules
    alias in the action interner.
    """

    physical_tick: ActionProgramID
    valuation: ActionProgramID
    frame: ActionProgramID


@dataclass(frozen=True, slots=True)
class CollatzActionGeometry:
    """Normalized spatial wiring kept separate from semantic arithmetic."""

    level: int = 0
    orientation: int = 0
    phase: int = 0
    halo_left: int = 0
    halo_right: int = 0

    def __post_init__(self) -> None:
        values = (
            self.level,
            self.orientation,
            self.phase,
            self.halo_left,
            self.halo_right,
        )
        if any(type(value) is not int for value in values):
            raise TypeError("Collatz geometry requires exact integer fields")
        if (
            self.level < 0
            or self.orientation not in (0, 1)
            or min(
                self.phase,
                self.halo_left,
                self.halo_right,
            )
            < 0
        ):
            raise ValueError("invalid Collatz action geometry")


@dataclass(frozen=True, slots=True)
class CollatzFieldAction:
    """Complete factored action; every potentially large object is a handle."""

    character: CollatzCharacterAction
    root_action: ActionProgramID
    affine_action: ActionProgramID
    innovation: PadicRadialQuotient
    defect: _CollatzDefectClassID
    cocycles: CollatzCocyclePrograms
    output_morphism: ActionProgramID
    geometry: CollatzActionGeometry


@dataclass(frozen=True, slots=True)
class CollatzFieldActionMetrics:
    action_nodes: int
    interner_entries: int
    composition_evaluations: int
    early_hits: int
    source_annihilation_derivations: int
    composition_requests: int
    composition_early_hits: int
    composition_cache_entries: int


class CollatzFieldActionArena:
    """Hash-cons and power complete algebraic Collatz cell actions."""

    def __init__(
        self,
        programs: CollatzSymbolicProgramAlgebra,
        defects: _CollatzDefectArena,
        *,
        radial_orders: tuple[int, ...] = (),
        padic_precision: int = 32,
        ledger: ResourceLedger | None = None,
    ) -> None:
        if type(radial_orders) is not tuple or any(
            type(order) is not int for order in radial_orders
        ):
            raise TypeError("radial orders must be an immutable integer tuple")
        if tuple(sorted(set(radial_orders))) != radial_orders or any(
            order <= 0 for order in radial_orders
        ):
            raise ValueError("radial orders must be positive, sorted, and unique")
        if type(padic_precision) is not int:
            raise TypeError("3-adic precision must be an exact integer")
        if padic_precision <= 0:
            raise ValueError("3-adic precision must be positive")
        # 3**41 exceeds one 64-bit limb.  Check the exponent first so an
        # adversarial precision cannot allocate an enormous temporary integer
        # merely to be rejected by this bounded production carrier.
        if padic_precision > 40:
            raise ValueError("3-adic innovation payload must fit one 64-bit limb")
        self.programs = programs
        self.defects = defects
        self.ledger = ledger if ledger is not None else defects.ledger
        if defects.ledger is not self.ledger:
            raise ValueError(
                "field actions and residual defects must belong to one index ledger"
            )
        self.owner = ArenaToken("collatz-field-actions")
        self.radial_orders = radial_orders
        self.padic_precision = padic_precision
        for role in _PROGRAM_ROLES:
            self._validate_program(role, programs.identity(role))
        self.ledger.register_execution_root(self)
        prefix = f"collatz-field-action-{len(self.ledger.inventory())}"
        self._node_owner = self.ledger.register(
            prefix + "-nodes", "collatz_field_action"
        )
        self._key_owner = self.ledger.register(
            prefix + "-keys", "collatz_field_action_interner"
        )
        self._nodes: MutableSequence[CollatzFieldAction] = self.ledger.make_list(
            self._node_owner
        )
        self._keys: MutableMapping[SemanticIdentity, CollatzFieldActionID] = (
            self.ledger.make_dict(
                self._key_owner,
            )
        )
        # A runtime image stores a coordinate-output handle, while this
        # family record continues to reference the executable symbolic
        # program.  This table is a scoped view, not a digit cache.
        self.output_owner = ArenaToken("collatz-coordinate-outputs")
        output_prefix = f"collatz-field-output-{len(self.ledger.inventory())}"
        self._output_node_owner = self.ledger.register(
            output_prefix + "-nodes",
            "coordinate_output_morphism",
        )
        self._output_key_owner = self.ledger.register(
            output_prefix + "-keys",
            "coordinate_output_interner",
        )
        self._output_programs: MutableSequence[ActionProgramID] = self.ledger.make_list(
            self._output_node_owner,
        )
        self._output_ids: MutableMapping[ActionProgramID, int] = self.ledger.make_dict(
            self._output_key_owner,
        )
        self.ledger.register_container(
            self._output_node_owner,
            self._output_programs,
            node_count=lambda: len(self._output_programs),
            payloads=lambda: self._output_programs,
        )
        self.ledger.register_container(
            self._output_key_owner,
            self._output_ids,
            payloads=lambda: self._output_ids.items(),
        )
        witness_owner = self.ledger.register(
            output_prefix + "-construction-witnesses",
            "action_construction_metadata",
        )
        self._witness_owner = witness_owner
        self._witnesses: MutableMapping[
            CollatzFieldActionID,
            tuple[CollatzFieldActionID, CollatzFieldActionID],
        ] = self.ledger.make_dict(witness_owner)
        self.ledger.register_container(
            witness_owner,
            self._witnesses,
            payloads=lambda: self._witnesses.items(),
        )
        composition_owner = self.ledger.register(
            output_prefix + "-temporal-compositions",
            "action_construction_metadata",
        )
        self._composition_owner = composition_owner
        self._compositions: MutableMapping[
            tuple[CollatzFieldActionID, CollatzFieldActionID], CollatzFieldActionID
        ] = self.ledger.make_dict(composition_owner)
        self.ledger.register_container(
            composition_owner,
            self._compositions,
            payloads=lambda: self._compositions.items(),
            composition_count=lambda: len(self._compositions),
        )
        self._composition_evaluations = 0
        self._composition_requests = 0
        self._composition_early_hits = 0
        self._early_hits = 0
        self._source_annihilation_derivations = 0

        self.register_payload_audit()

    @property
    def nodes(self) -> tuple[CollatzFieldAction, ...]:
        return tuple(self._nodes)

    @property
    def action_kind(self) -> str:
        """Kind token required when constructing the shared image arena."""
        return _ACTION_KIND

    @property
    def output_kind(self) -> str:
        """Kind token for coordinate-parametric output handles."""
        return _OUTPUT_KIND

    @property
    def interned(self) -> Mapping[SemanticIdentity, CollatzFieldActionID]:
        return MappingProxyType(self._keys)

    def _validate_program(self, role: ProgramRole, reference: ActionProgramID) -> int:
        if type(reference) is not ActionProgramID:
            raise TypeError(f"{role} component requires an exact scoped program ID")
        result = self.programs.validate(role, reference)
        if type(result) is not int or result != reference.local_id:
            raise ValueError(
                "symbolic program resolver returned another local identity"
            )
        return result

    def coordinate_output(
        self, action: CollatzFieldActionID
    ) -> CoordinateOutputMorphismID:
        """Expose an action's symbolic output through the shared runtime sort."""
        record = self.resolve(action)
        program = record.output_morphism
        found = self._output_ids.get(program)
        if found is None:
            self.ledger.reserve_many(
                ((self._output_node_owner, 1, 1), (self._output_key_owner, 1, 0)),
            )
            found = len(self._output_programs)
            self._output_programs.append(program)
            self._output_ids[program] = found
        return CoordinateOutputMorphismID(self.output_owner, _OUTPUT_KIND, found)

    def output_program(self, reference: CoordinateOutputMorphismID) -> ActionProgramID:
        """Resolve a runtime output view back to its symbolic program."""
        if type(reference) is not CoordinateOutputMorphismID:
            raise TypeError("expected a scoped coordinate output morphism")
        reference.validate(
            self.output_owner,
            _OUTPUT_KIND,
            size=len(self._output_programs),
        )
        return self._output_programs[reference.local_id]

    def _validate_character(self, character: CollatzCharacterAction) -> None:
        if type(character) is not CollatzCharacterAction:
            raise TypeError("field action requires a canonical Collatz character")
        character.__post_init__()
        if tuple(item.order for item in character.radial) != self.radial_orders:
            raise ValueError("field action has another radial port signature")

    def _validate_action(self, action: CollatzFieldAction) -> None:
        if type(action) is not CollatzFieldAction:
            raise TypeError("expected a complete Collatz field action")
        self._validate_character(action.character)
        self._validate_program("root", action.root_action)
        self._validate_program("affine", action.affine_action)
        self._validate_program("output", action.output_morphism)
        if type(action.innovation) is not PadicRadialQuotient:
            raise TypeError("field action requires a bounded 3-adic radial quotient")
        action.innovation.__post_init__()
        if (
            action.innovation.prime != 3
            or action.innovation.precision != self.padic_precision
            or action.innovation.modulus > 1 << 64
        ):
            raise ValueError("field action has another bounded 3-adic signature")
        self.defects.validate(action.defect)
        if type(action.cocycles) is not CollatzCocyclePrograms:
            raise TypeError("field action requires symbolic Collatz cocycles")
        self._validate_program("physical-tick", action.cocycles.physical_tick)
        self._validate_program("valuation", action.cocycles.valuation)
        self._validate_program("frame", action.cocycles.frame)
        if type(action.geometry) is not CollatzActionGeometry:
            raise TypeError("field action requires normalized Collatz geometry")
        action.geometry.__post_init__()

    def _intern(
        self,
        action: CollatzFieldAction,
        reservations: tuple[tuple[int, int, int], ...] = (),
    ) -> CollatzFieldActionID:
        self._validate_action(action)
        identity = self._action_identity(action)
        found = self._keys.get(identity)
        if found is not None:
            if reservations:
                self.ledger.reserve_many(reservations)
            self._early_hits += 1
            self.ledger.bump(_collatz_keys.COLLATZ_FIELD_ACTION_EARLY_HITS)
            return found
        self.ledger.reserve_many(
            (
                (self._node_owner, 1, 1),
                (self._key_owner, 1, 0),
                *reservations,
            )
        )
        result = CollatzFieldActionID(self.owner, _ACTION_KIND, len(self._nodes))
        self._nodes.append(action)
        self._keys[identity] = result
        self.ledger.bump(_collatz_keys.COLLATZ_FIELD_ACTION_PUBLICATIONS)
        self.ledger.bump(_shared_keys.FIELD_ACTION_PUBLICATIONS)
        return result

    def intern(self, action: CollatzFieldAction) -> CollatzFieldActionID:
        return self._intern(action)

    def resolve(self, reference: CollatzFieldActionID) -> CollatzFieldAction:
        if type(reference) is not CollatzFieldActionID:
            raise TypeError("expected a scoped Collatz field action ID")
        reference.validate(self.owner, _ACTION_KIND, size=len(self._nodes))
        return self._nodes[reference.local_id]

    def validate_action(self, reference: CollatzFieldActionID) -> None:
        """Validate the shared runtime action sort before any image lookup."""
        self.resolve(reference)

    def _action_identity(
        self,
        action: CollatzFieldAction,
        program_identities: tuple[SemanticIdentity, ...] | None = None,
    ) -> SemanticIdentity:
        """Build the complete semantic key for a validated action record."""
        self._validate_action(action)
        if program_identities is None:
            program_identity = self.programs.semantic_identity
            if not callable(program_identity):
                raise TypeError("Collatz symbolic programs require semantic identities")
            program_identities = (
                program_identity("root", action.root_action),
                program_identity("affine", action.affine_action),
                program_identity("physical-tick", action.cocycles.physical_tick),
                program_identity("valuation", action.cocycles.valuation),
                program_identity("frame", action.cocycles.frame),
                program_identity("output", action.output_morphism),
            )
        if (
            type(program_identities) is not tuple
            or len(program_identities) != 6
            or any(type(item) is not SemanticIdentity for item in program_identities)
        ):
            raise TypeError("Collatz action requires six canonical program identities")
        root, affine, physical_tick, valuation, frame, output = program_identities
        character = (
            COLLATZ_CHARACTER_ACTION_TAG,
            action.character.growth_phase,
            tuple(item.canonical_key for item in action.character.radial),
        )
        innovation = action.innovation.canonical_key
        defect = (
            COLLATZ_RESIDUAL_DEFECT_TAG,
            self.defects.certificate_digest,
            self.defects.validate(action.defect),
        )
        geometry = (
            COLLATZ_ACTION_GEOMETRY_TAG,
            (GEOMETRY_LEVEL_FIELD, str(action.geometry.level)),
            action.geometry.orientation,
            (GEOMETRY_PHASE_FIELD, str(action.geometry.phase)),
            (GEOMETRY_LEFT_HALO_FIELD, str(action.geometry.halo_left)),
            (GEOMETRY_RIGHT_HALO_FIELD, str(action.geometry.halo_right)),
        )
        behavior = (
            COLLATZ_FIELD_ACTION_TAG,
            character,
            root,
            affine,
            innovation,
            defect,
            physical_tick,
            valuation,
            frame,
            output,
            geometry,
        )
        return SemanticIdentity(SemanticIdentityDomain.ANONYMOUS, behavior)

    def semantic_identity(self, reference: CollatzFieldActionID) -> SemanticIdentity:
        """Return complete source-free action behavior without its arena ordinal."""
        return self._action_identity(self.resolve(reference))

    def action_children(
        self,
        reference: CollatzFieldActionID,
    ) -> tuple[CollatzFieldActionID, CollatzFieldActionID] | None:
        """Return construction-only temporal operands for the shared scheduler."""
        self.resolve(reference)
        result = self._witnesses.get(reference)
        if result is None:
            return None
        for child in result:
            self.resolve(child)
        return result

    @property
    def identity(self) -> CollatzFieldActionID:
        return self.identity_for(CollatzActionGeometry())

    def identity_for(self, geometry: CollatzActionGeometry) -> CollatzFieldActionID:
        if type(geometry) is not CollatzActionGeometry:
            raise TypeError("identity geometry must be normalized")
        character = CollatzCharacterAction(
            0,
            tuple(CollatzRadialCharacter(order, 0) for order in self.radial_orders),
        )
        innovation = PadicRadialQuotient(3, self.padic_precision, 0, 1, 0)
        return self.intern(
            CollatzFieldAction(
                character,
                self.programs.identity("root"),
                self.programs.identity("affine"),
                innovation,
                self.defects.identity,
                CollatzCocyclePrograms(
                    self.programs.identity("physical-tick"),
                    self.programs.identity("valuation"),
                    self.programs.identity("frame"),
                ),
                self.programs.identity("output"),
                geometry,
            )
        )

    def compose(
        self,
        before: CollatzFieldActionID,
        after: CollatzFieldActionID,
    ) -> CollatzFieldActionID:
        first, second = self.resolve(before), self.resolve(after)
        if first.geometry != second.geometry:
            raise ValueError("temporal actions require identical normalized geometry")
        self._composition_requests += 1
        self.ledger.bump(_collatz_keys.COLLATZ_FIELD_ACTION_COMPOSITION_REQUESTS)
        self.ledger.bump(_shared_keys.TEMPORAL_PARENT_REQUESTS)
        self.ledger.bump(_shared_keys.DIAMOND_TEMPORAL_COMPOSITION_REQUESTS)
        cache_key = (before, after)
        found = self._compositions.get(cache_key)
        if found is not None:
            # Resolve the retained result too: a malformed or stale cache entry
            # must fail before being reported as a warm semantic hit.
            self.resolve(found)
            self._composition_early_hits += 1
            self.ledger.bump(_collatz_keys.COLLATZ_FIELD_ACTION_COMPOSITION_CACHE_HITS)
            self.ledger.bump(_shared_keys.TEMPORAL_PARENT_EARLY_HITS)
            self.ledger.bump(_shared_keys.DIAMOND_TEMPORAL_COMPOSITION_HITS)
            return found
        first_affine = first.innovation.as_affine()
        second_affine = second.innovation.as_affine()
        innovation = first_affine.then(second_affine).radial_quotient
        character = first.character.then(second.character)
        defect = self.defects.compose(first.defect, second.defect)
        compose_identity = self.programs.composed_semantic_identity
        if not callable(compose_identity):
            raise TypeError(
                "Collatz symbolic programs require composition semantic identities"
            )
        program_identities = (
            compose_identity("root", first.root_action, second.root_action),
            compose_identity("affine", first.affine_action, second.affine_action),
            compose_identity(
                "physical-tick",
                first.cocycles.physical_tick,
                second.cocycles.physical_tick,
            ),
            compose_identity(
                "valuation",
                first.cocycles.valuation,
                second.cocycles.valuation,
            ),
            compose_identity("frame", first.cocycles.frame, second.cocycles.frame),
            compose_identity(
                "output",
                first.output_morphism,
                second.output_morphism,
            ),
        )
        prospective = CollatzFieldAction(
            character,
            first.root_action,
            first.affine_action,
            innovation,
            defect,
            first.cocycles,
            first.output_morphism,
            first.geometry,
        )
        semantic_key = self._action_identity(prospective, program_identities)
        semantic_found = self._keys.get(semantic_key)
        if semantic_found is not None:
            self.resolve(semantic_found)
            self.ledger.reserve(self._composition_owner, entries=1)
            self._compositions[cache_key] = semantic_found
            self._composition_early_hits += 1
            self.ledger.bump(_collatz_keys.COLLATZ_FIELD_ACTION_SEMANTIC_PRE_HITS)
            self.ledger.bump(_shared_keys.TEMPORAL_PARENT_EARLY_HITS)
            self.ledger.bump(_shared_keys.DIAMOND_TEMPORAL_COMPOSITION_HITS)
            return semantic_found
        result = CollatzFieldAction(
            character,
            self.programs.compose("root", first.root_action, second.root_action),
            self.programs.compose("affine", first.affine_action, second.affine_action),
            innovation,
            defect,
            CollatzCocyclePrograms(
                self.programs.compose(
                    "physical-tick",
                    first.cocycles.physical_tick,
                    second.cocycles.physical_tick,
                ),
                self.programs.compose(
                    "valuation",
                    first.cocycles.valuation,
                    second.cocycles.valuation,
                ),
                self.programs.compose(
                    "frame",
                    first.cocycles.frame,
                    second.cocycles.frame,
                ),
            ),
            self.programs.compose(
                "output", first.output_morphism, second.output_morphism
            ),
            first.geometry,
        )
        existing = self._keys.get(semantic_key)
        reserve_witness = existing is None or (
            existing not in (before, after) and existing not in self._witnesses
        )
        reservations = [(self._composition_owner, 1, 0)]
        if reserve_witness:
            reservations.append((self._witness_owner, 1, 0))
        canonical = self._intern(result, tuple(reservations))
        if existing is not None:
            self.ledger.bump(
                _collatz_keys.COLLATZ_FIELD_ACTION_LATE_DUPLICATE_REDUCTIONS
            )
            self.ledger.bump(_collatz_keys.TEMPORAL_PARENT_LATE_DUPLICATE_REDUCTIONS)
        if canonical not in (before, after) and canonical not in self._witnesses:
            self._witnesses[canonical] = (before, after)
        elif reserve_witness:
            self.ledger.release(self._witness_owner, entries=1)
        self._compositions[cache_key] = canonical
        self._composition_evaluations += 1
        self.ledger.bump(_collatz_keys.COLLATZ_FIELD_ACTION_COMPOSITIONS)
        self.ledger.bump(_shared_keys.TEMPORAL_PARENT_COMPOSITIONS)
        self.ledger.bump(_shared_keys.DIAMOND_TEMPORAL_COMPOSITION_EVALUATIONS)
        if innovation.source_annihilated:
            self._source_annihilation_derivations += 1
            self.ledger.bump(
                _collatz_keys.COLLATZ_FIELD_ACTION_SOURCE_ANNIHILATION_DERIVATIONS
            )
        return canonical

    def power(
        self, action: CollatzFieldActionID, exponent: int
    ) -> CollatzFieldActionID:
        self.resolve(action)
        if type(exponent) is not int:
            raise TypeError("Collatz action exponent must be an exact integer")
        if exponent < 0:
            raise ValueError("Collatz action exponent must be nonnegative")
        if exponent == 0:
            return self.identity_for(self.resolve(action).geometry)
        # An optional accumulator avoids composing the semantic identity with
        # the first selected bit.  That old pattern performed a complete
        # reduction only to discover the already-interned primitive as a late
        # duplicate, making every cold power start with avoidable publication
        # work.  The loop visits exponent bits, never physical generations.
        return semigroup_power(action, exponent, compose=self.compose)

    @property
    def action_count(self) -> int:
        return len(self._nodes)

    @property
    def production_residual_state_classes(self) -> int:
        return self.defects.class_count

    @property
    def retained_entries(self) -> int:
        return len(self._nodes) + len(self._keys)

    @property
    def metrics(self) -> CollatzFieldActionMetrics:
        return CollatzFieldActionMetrics(
            len(self._nodes),
            len(self._keys),
            self._composition_evaluations,
            self._early_hits,
            self._source_annihilation_derivations,
            self._composition_requests,
            self._composition_early_hits,
            len(self._compositions),
        )

    def register_payload_audit(self) -> None:
        root = self

        if type(root) is not CollatzFieldActionArena:
            raise TypeError("Collatz field-action audit requires its exact arena")
        stores = (
            PayloadAuditStoreBinding(
                root._node_owner, "_nodes", "collatz_field_action"
            ),
            PayloadAuditStoreBinding(
                root._key_owner, "_keys", "collatz_field_action_interner"
            ),
            PayloadAuditStoreBinding(
                root._output_node_owner,
                "_output_programs",
                "coordinate_output_morphism",
            ),
            PayloadAuditStoreBinding(
                root._output_key_owner,
                "_output_ids",
                "coordinate_output_interner",
            ),
            PayloadAuditStoreBinding(
                root._witness_owner,
                "_witnesses",
                "action_construction_metadata",
            ),
            PayloadAuditStoreBinding(
                root._composition_owner,
                "_compositions",
                "action_construction_metadata",
            ),
        )
        register_payload_audit_contract(
            root.ledger, root, "collatz", stores, audit_collatz_field_action
        )

    def audit_payload(self, ledger: object, root: object) -> PayloadAuditContribution:
        """Validate action/key/output/witness rows without ledger mutation."""
        if root is not self:
            raise TypeError("payload audit callback received another owner")
        from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
        from number_compiler.arithmetic.contracts.semantic_identity import (
            SemanticIdentity,
        )
        from number_compiler.resources.ledger import ResourceLedger

        if (
            type(ledger) is not ResourceLedger
            or type(root) is not CollatzFieldActionArena
        ):
            raise TypeError("Collatz field-action audit received a foreign owner")
        arena = root
        approved: list[PayloadAuditEntry] = []
        invalid: list[PayloadAuditEntry] = []

        def accept(owner: int, value: object) -> None:
            approved.append(PayloadAuditEntry(owner, value))

        def reject(owner: int, value: object) -> None:
            invalid.append(PayloadAuditEntry(owner, value))

        if arena.ledger is not ledger:
            reject(arena._node_owner, arena)
            return PayloadAuditContribution((), tuple(invalid))

        for index, action in enumerate(arena._nodes):
            try:
                valid = type(action) is CollatzFieldAction
                arena._validate_action(action)
                reference = CollatzFieldActionID(arena.owner, arena.action_kind, index)
                valid &= arena.resolve(reference) is action
            except (TypeError, ValueError, IndexError, AttributeError):
                valid = False
            (accept if valid else reject)(arena._node_owner, action)

        program_identity_cache: dict[
            tuple[ProgramRole, ActionProgramID], SemanticIdentity
        ] = {}

        def audit_program_identity(
            role: ProgramRole, program: ActionProgramID
        ) -> SemanticIdentity:
            cache_key = role, program
            found = program_identity_cache.get(cache_key)
            if found is not None:
                return found
            identity = arena.programs.audit_semantic_identity(role, program)
            if type(identity) is not SemanticIdentity:
                raise TypeError("Collatz program audit returned an unchecked identity")
            program_identity_cache[cache_key] = identity
            return identity

        for key, reference in arena._keys.items():
            try:
                valid = type(key) is SemanticIdentity
                valid &= type(reference) is CollatzFieldActionID
                action = arena.resolve(reference)
                if type(action) is not CollatzFieldAction:
                    raise TypeError("Collatz field-action store contains another node")
                arena._validate_action(action)
                program_identities = (
                    audit_program_identity("root", action.root_action),
                    audit_program_identity("affine", action.affine_action),
                    audit_program_identity(
                        "physical-tick", action.cocycles.physical_tick
                    ),
                    audit_program_identity("valuation", action.cocycles.valuation),
                    audit_program_identity("frame", action.cocycles.frame),
                    audit_program_identity("output", action.output_morphism),
                )
                valid &= arena._action_identity(action, program_identities) == key
            except (TypeError, ValueError, IndexError, AttributeError):
                valid = False
            (accept if valid else reject)(arena._key_owner, key)
            (accept if valid else reject)(arena._key_owner, reference)

        for index, program in enumerate(arena._output_programs):
            try:
                valid = type(program) is ActionProgramID
                arena._validate_program("output", program)
                valid &= arena._output_ids.get(program) == index
            except (TypeError, ValueError, IndexError, AttributeError):
                valid = False
            (accept if valid else reject)(arena._output_node_owner, program)

        for program, index in arena._output_ids.items():
            valid = type(program) is ActionProgramID and type(index) is int
            valid &= 0 <= index < len(arena._output_programs)
            if valid:
                valid &= arena._output_programs[index] == program
            (accept if valid else reject)(arena._output_key_owner, program)
            (accept if valid else reject)(arena._output_key_owner, index)

        for parent, children in arena._witnesses.items():
            try:
                valid = type(parent) is CollatzFieldActionID
                arena.resolve(parent)
                valid &= type(children) is tuple and len(children) == 2
                if valid:
                    for child in children:
                        arena.resolve(child)
            except (TypeError, ValueError, IndexError, AttributeError):
                valid = False
            (accept if valid else reject)(arena._witness_owner, parent)
            (accept if valid else reject)(arena._witness_owner, children)

        for operands, result in arena._compositions.items():
            try:
                valid = type(operands) is tuple and len(operands) == 2
                if valid:
                    first, second = operands
                    arena.resolve(first)
                    arena.resolve(second)
                arena.resolve(result)
            except (TypeError, ValueError, IndexError, AttributeError):
                valid = False
            (accept if valid else reject)(arena._composition_owner, operands)
            (accept if valid else reject)(arena._composition_owner, result)

        return PayloadAuditContribution(tuple(approved), tuple(invalid))


def bounded_3adic_innovation(
    precision: int,
    multiplier: int,
    innovation: int,
    *,
    steps: int = 0,
) -> PadicRadialQuotient:
    """Create the bounded source/innovation factor at a compiler boundary."""
    values = (precision, multiplier, innovation, steps)
    if any(type(value) is not int for value in values):
        raise TypeError("3-adic compiler inputs require exact integers")
    if precision <= 0 or precision > 40:
        raise ValueError("3-adic compiler precision must fit one 64-bit limb")
    return PadicAffineMorphism(
        3, precision, multiplier, innovation, steps
    ).radial_quotient


__all__ = [
    "CollatzActionGeometry",
    "CollatzCharacterAction",
    "CollatzCocyclePrograms",
    "CollatzFieldAction",
    "CollatzFieldActionArena",
    "CollatzFieldActionID",
    "CollatzFieldActionMetrics",
    "CollatzSymbolicProgramAlgebra",
    "ProgramRole",
    "bounded_3adic_innovation",
]


def audit_collatz_field_action(
    ledger: object, root: object
) -> PayloadAuditContribution:
    """Closure-free ledger entry point for its exact family owner."""
    if type(root) is not CollatzFieldActionArena:
        raise TypeError("Collatz payload audit received another owner")
    return root.audit_payload(ledger, root)

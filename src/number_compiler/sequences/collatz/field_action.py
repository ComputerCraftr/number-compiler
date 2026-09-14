"""Canonical algebraic carrier for powered Collatz field cells.

The carrier retains only finite characters, a bounded 3-adic innovation and
scoped references to symbolic root, affine and output programs.  Exact tails,
future suffixes and affine constants belong to the program provider or explicit
lowering boundary; they can never enter a field-action record.
"""

from __future__ import annotations

from collections.abc import Mapping, MutableMapping, MutableSequence
from dataclasses import dataclass
from hashlib import sha256
from types import MappingProxyType
from typing import Literal, Protocol, TypeAlias

from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaHandle,
    ArenaToken,
)
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.fields.adic_morphism import (
    PadicAffineMorphism,
    PadicRadialQuotient,
)
from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID,
    FieldCellActionID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.character import CollatzRadialCharacter

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
_DEFECT_KIND = "collatz-residual-defect"
_OUTPUT_KIND = "coordinate-output-morphism"


class CollatzSymbolicProgramAlgebra(Protocol):
    """Canonical symbolic program operations supplied by the shared runtime."""

    def identity(self, role: ProgramRole) -> ActionProgramID: ...

    def validate(self, role: ProgramRole, reference: ActionProgramID) -> int: ...

    def semantic_identity(
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


@dataclass(frozen=True, slots=True)
class CollatzDefectClassID(ArenaHandle):
    """A scoped class in one frozen residual-behavior certificate."""


# Compatibility spelling for callers of the family module.  Production image
# arenas must see the shared runtime action sort, never a family-local alias.
CollatzFieldActionID: TypeAlias = FieldCellActionID


class CollatzDefectArena:
    """Frozen finite monoid for the residual behavior left after factoring."""

    def __init__(
        self,
        table: tuple[tuple[int, ...], ...],
        *,
        identity: int,
        ledger: ResourceLedger | None = None,
    ) -> None:
        if (
            type(table) is not tuple
            or not table
            or any(type(row) is not tuple for row in table)
        ):
            raise TypeError(
                "residual composition table must be a nonempty immutable matrix"
            )
        size = len(table)
        if type(identity) is not int:
            raise TypeError("residual identity must be an exact class index")
        if not 0 <= identity < size:
            raise ValueError("residual identity must be an exact class index")
        if any(len(row) != size for row in table):
            raise ValueError("residual composition table must be square")
        for row in table:
            for result in row:
                if type(result) is not int or not 0 <= result < size:
                    raise ValueError("residual composition table is not closed")
        for index in range(size):
            if table[identity][index] != index or table[index][identity] != index:
                raise ValueError("declared residual identity is invalid")
        for first in range(size):
            for second in range(size):
                for third in range(size):
                    if (
                        table[table[first][second]][third]
                        != table[first][table[second][third]]
                    ):
                        raise ValueError(
                            "residual composition table is not associative"
                        )
        self.owner = ArenaToken("collatz-residual-defects")
        self.ledger = ledger if ledger is not None else ResourceLedger()
        self.table = table
        self.identity_index = identity
        encoded = repr((size, identity, table)).encode("ascii")
        self.certificate_digest = sha256(encoded).hexdigest()

    @property
    def class_count(self) -> int:
        return len(self.table)

    @property
    def identity(self) -> CollatzDefectClassID:
        return self.class_id(self.identity_index)

    def class_id(self, index: int) -> CollatzDefectClassID:
        if type(index) is not int or not 0 <= index < self.class_count:
            raise ValueError("invalid residual class index")
        return CollatzDefectClassID(self.owner, _DEFECT_KIND, index)

    def validate(self, reference: CollatzDefectClassID) -> int:
        if type(reference) is not CollatzDefectClassID:
            raise TypeError("expected a scoped Collatz residual class")
        return reference.validate(
            self.owner,
            _DEFECT_KIND,
            size=self.class_count,
        ).local_id

    def compose(
        self,
        before: CollatzDefectClassID,
        after: CollatzDefectClassID,
    ) -> CollatzDefectClassID:
        before_id, after_id = self.validate(before), self.validate(after)
        return self.class_id(self.table[before_id][after_id])


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
    defect: CollatzDefectClassID
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
        defects: CollatzDefectArena,
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
            self.ledger.bump("collatz_field_action_early_hits")
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
        self.ledger.bump("collatz_field_action_publications")
        self.ledger.bump("field_action_publications")
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
            "collatz-character-action-v1",
            action.character.growth_phase,
            tuple(item.canonical_key for item in action.character.radial),
        )
        innovation = action.innovation.canonical_key
        defect = (
            "collatz-residual-defect-v1",
            self.defects.certificate_digest,
            self.defects.validate(action.defect),
        )
        geometry = (
            "collatz-action-geometry-v1",
            ("level", str(action.geometry.level)),
            action.geometry.orientation,
            ("phase", str(action.geometry.phase)),
            ("halo-left", str(action.geometry.halo_left)),
            ("halo-right", str(action.geometry.halo_right)),
        )
        behavior = (
            "collatz-field-action-v2",
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
        return SemanticIdentity("", behavior)

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
        self.ledger.bump("collatz_field_action_composition_requests")
        self.ledger.bump("temporal_parent_requests")
        self.ledger.bump("diamond_temporal_composition_requests")
        cache_key = (before, after)
        found = self._compositions.get(cache_key)
        if found is not None:
            # Resolve the retained result too: a malformed or stale cache entry
            # must fail before being reported as a warm semantic hit.
            self.resolve(found)
            self._composition_early_hits += 1
            self.ledger.bump("collatz_field_action_composition_cache_hits")
            self.ledger.bump("temporal_parent_early_hits")
            self.ledger.bump("diamond_temporal_composition_hits")
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
            self.ledger.bump("collatz_field_action_semantic_pre_hits")
            self.ledger.bump("temporal_parent_early_hits")
            self.ledger.bump("diamond_temporal_composition_hits")
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
            self.ledger.bump("collatz_field_action_late_duplicate_reductions")
            self.ledger.bump("temporal_parent_late_duplicate_reductions")
        if canonical not in (before, after) and canonical not in self._witnesses:
            self._witnesses[canonical] = (before, after)
        elif reserve_witness:
            self.ledger.release(self._witness_owner, entries=1)
        self._compositions[cache_key] = canonical
        self._composition_evaluations += 1
        self.ledger.bump("collatz_field_action_compositions")
        self.ledger.bump("temporal_parent_compositions")
        self.ledger.bump("diamond_temporal_composition_evaluations")
        if innovation.source_annihilated:
            self._source_annihilation_derivations += 1
            self.ledger.bump("collatz_field_action_source_annihilation_derivations")
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
        result: CollatzFieldActionID | None = None
        current = action
        remaining = exponent
        while remaining:
            if remaining & 1:
                result = current if result is None else self.compose(result, current)
            remaining >>= 1
            if remaining:
                current = self.compose(current, current)
        if result is None:
            raise AssertionError("positive Collatz power lost its accumulator")
        return result

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
    "CollatzDefectArena",
    "CollatzDefectClassID",
    "CollatzFieldAction",
    "CollatzFieldActionArena",
    "CollatzFieldActionID",
    "CollatzFieldActionMetrics",
    "CollatzSymbolicProgramAlgebra",
    "ProgramRole",
    "bounded_3adic_innovation",
]

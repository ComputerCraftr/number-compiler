"""Complete extensional macro effects, distinct from construction programs.

Only normalized semantic functions enter this arena. Source/geometry bindings
belong to the parent memo, never to the semantic effect interner. This module
does not turn an arbitrary expression recipe into an extensional function;
the compiler must supply all components in the finite semantic algebra first.
"""

from __future__ import annotations

from collections.abc import Mapping, MutableMapping, MutableSequence
from dataclasses import dataclass, field, fields
from types import MappingProxyType
from typing import TypeAlias

from number_compiler.arithmetic.carry.reverse_port_functions import ReversePortFunction
from number_compiler.arithmetic.carry.reverse_sector_transfer import (
    ReverseCarrySectorTransfer,
)
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FinitePort,
    FunctionSignature,
    SemanticFunctionID,
    SemanticSort,
    SemanticTerminal,
)
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.arithmetic.radix_port_functions import RadixPortFunction
from number_compiler.hashlife.actions.diamond_actions import (
    CellID,
    ImageCellArena,
    PortSignatureID,
)
from number_compiler.hashlife.behavior.future_behavior import (
    FutureBehaviorClass,
    FutureBehaviorClassID,
    FutureBehaviorProfile,
    FutureBehaviorProfileID,
    QuiescentBlankCertificate,
)
from number_compiler.hashlife.interfaces.closed_interface_admission import (
    has_closed_components,
    validate_closed_components,
)
from number_compiler.hashlife.interfaces.primitive_behavior import (
    PrimitiveBehaviorQuotient,
)
from number_compiler.hashlife.interfaces.quotient_publication import (
    retained_record_nodes,
)
from number_compiler.hashlife.interfaces.semantic_bits import BitFunctionArena
from number_compiler.hashlife.interfaces.semantic_structure_conversion import (
    StructureConversion,
)
from number_compiler.hashlife.interfaces.semantic_structure_publication import (
    PreparedStructures,
    prepare_structures,
)
from number_compiler.hashlife.interfaces.semantic_structure_validation import (
    require_total_components,
)
from number_compiler.hashlife.interfaces.semantic_structures import (
    StructureArena,
    StructureID,
    _Builder,
    _Rewrite,
)
from number_compiler.resources.closed_interface_workspace import (
    ClosedInterfaceWorkspace,
)
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class LocalInterfaceID(ArenaHandle):
    """Complete bounded port behavior, separate from a recursive image."""


DiamondQuotientID: TypeAlias = LocalInterfaceID


COMPONENT_ROLES = (
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


@dataclass(frozen=True, slots=True)
class MacroInterface:
    """Normalized semantic channel contract; no source or occurrence identity."""

    kernel: SemanticIdentity
    inputs: tuple[FinitePort, ...]
    outputs: tuple[SemanticSort, ...]
    admissible: SemanticFunctionID
    phase_count: int = 1
    orientations: tuple[int, ...] = (0, 1)


SemanticComponent: TypeAlias = (
    SemanticFunctionID | StructureID | RadixPortFunction | ReversePortFunction
)


@dataclass(frozen=True, slots=True)
class MacroComponents:
    boundary_left: SemanticComponent
    boundary_right: SemanticComponent
    output: SemanticComponent
    activity: SemanticComponent
    first_active: SemanticComponent
    last_active: SemanticComponent
    extent: SemanticComponent
    halo_left: SemanticComponent
    halo_right: SemanticComponent
    growth: SemanticComponent
    termination: SemanticComponent
    normalization: SemanticComponent
    frame: SemanticComponent
    reverse_sectors: ReverseCarrySectorTransfer | None = field(
        default=None, kw_only=True
    )

    def functions(self) -> tuple[SemanticComponent, ...]:
        return tuple(getattr(self, role) for role in COMPONENT_ROLES)


@dataclass(frozen=True, slots=True)
class QuotientRecord:
    signature: PortSignatureID
    components: MacroComponents


@dataclass(frozen=True, slots=True)
class DiamondKey:
    """An occurrence binding to an already canonical complete action."""

    before: DiamondQuotientID
    after: DiamondQuotientID
    cell: CellID
    level: int
    orientation: int
    phase: int
    signature: PortSignatureID


class DiamondQuotientArena:
    """Intern complete effects and atomically bind them to parent requests.

    The semantic function arena is index-owned. A parent hit consults only
    allocated handle metadata and signatures; it does not admit, minimize, or
    evaluate its functions. Canonical records survive binding eviction.
    """

    @property
    def signature_kind(self) -> str:
        """Handle kind used by this arena's canonical port signatures."""
        return "diamond-semantic-signature"

    @property
    def interface_kind(self) -> str:
        """Handle kind used by this arena's canonical local interfaces."""
        return "diamond-quotient"

    def __init__(
        self,
        functions: SemanticFunctionArena,
        cells: ImageCellArena | None = None,
        *,
        structures: StructureArena | None = None,
    ) -> None:
        self.functions = functions
        self.ledger: ResourceLedger = functions.ledger
        if cells is not None and cells.ledger is not self.ledger:
            raise ValueError("quotient cells belong to another index")
        if structures is not None and structures.functions is not functions:
            raise ValueError("quotient structures belong to another semantic arena")
        self.structures = (
            structures
            if structures is not None
            else StructureArena(BitFunctionArena(self.ledger, functions))
        )
        self.cells = cells
        self.owner = ArenaToken("diamond-quotients")
        self.ledger.register_execution_root(self)
        prefix = f"diamond-quotient-{len(self.ledger.inventory())}"
        self._signature_owner = self.ledger.register(
            prefix + "-signatures", "semantic_port_signature"
        )
        self._signature_key_owner = self.ledger.register(
            prefix + "-signature-keys", "semantic_port_interner"
        )
        self._node_owner = self.ledger.register(prefix + "-nodes", "diamond_quotient")
        self._key_owner = self.ledger.register(
            prefix + "-keys", "diamond_quotient_interner"
        )
        self._normalization_owner = self.ledger.register(
            prefix + "-normalizations",
            "query_memo",
        )
        self._binding_owner = self.ledger.register(prefix + "-parents", "diamond_memo")
        self._future_profile_owner = self.ledger.register(
            prefix + "-future-profiles",
            "future_behavior_profile",
        )
        self._future_profile_key_owner = self.ledger.register(
            prefix + "-future-profile-keys",
            "future_behavior_profile_interner",
        )
        self._future_class_owner = self.ledger.register(
            prefix + "-future-classes",
            "future_behavior_class",
        )
        self._future_class_key_owner = self.ledger.register(
            prefix + "-future-class-keys",
            "future_behavior_class_interner",
        )
        self._future_certificate_owner = self.ledger.register(
            prefix + "-future-certificates",
            "future_behavior_certificate",
        )
        self._future_admission_owner = self.ledger.register(
            prefix + "-future-admissions",
            "future_behavior_admission",
        )
        self._future_work_owner = self.ledger.register(
            prefix + "-future-workspace",
            "future_behavior_workspace",
        )
        self._closed_workspace = ClosedInterfaceWorkspace(self.ledger, prefix)
        self._future_snapshot_owner = self.ledger.register(
            prefix + "-behavior-snapshots",
            "future_behavior_publication_snapshot",
        )
        self._signatures: MutableSequence[MacroInterface] = self.ledger.make_list(
            self._signature_owner
        )
        self._signature_keys: MutableMapping[MacroInterface, PortSignatureID] = (
            self.ledger.make_dict(self._signature_key_owner)
        )
        self._nodes: MutableMapping[int, QuotientRecord] = self.ledger.make_dict(
            self._node_owner
        )
        self._next_node = 0
        self.ledger.register_container(
            self._node_owner,
            self._nodes,
            node_count=lambda: sum(
                retained_record_nodes(record) for record in self._nodes.values()
            ),
            payloads=self._nodes.items,
        )
        self._keys: MutableMapping[QuotientRecord, DiamondQuotientID] = (
            self.ledger.make_dict(self._key_owner)
        )
        self._normalizations: MutableMapping[QuotientRecord, DiamondQuotientID] = (
            self.ledger.make_dict(self._normalization_owner)
        )
        self._parents: MutableMapping[DiamondKey, DiamondQuotientID] = (
            self.ledger.make_dict(self._binding_owner)
        )
        self._future_profiles: MutableMapping[int, FutureBehaviorProfile] = (
            self.ledger.make_dict(self._future_profile_owner)
        )
        self._future_profile_keys: MutableMapping[
            FutureBehaviorProfile, FutureBehaviorProfileID
        ] = self.ledger.make_dict(self._future_profile_key_owner)
        self._future_classes: MutableMapping[int, FutureBehaviorClass] = (
            self.ledger.make_dict(self._future_class_owner)
        )
        self._future_class_keys: MutableMapping[
            FutureBehaviorClass, FutureBehaviorClassID
        ] = self.ledger.make_dict(self._future_class_key_owner)
        self._future_certificates: MutableMapping[
            FutureBehaviorProfileID, QuiescentBlankCertificate
        ] = self.ledger.make_dict(self._future_certificate_owner)
        self._future_admissions: MutableMapping[
            str,
            tuple[tuple[object, ...], FutureBehaviorProfileID, FutureBehaviorClassID],
        ] = self.ledger.make_dict(self._future_admission_owner)
        self._future_snapshots: MutableMapping[tuple[str, int], tuple[object, ...]] = (
            self.ledger.make_dict(self._future_snapshot_owner)
        )
        self._next_future_profile = 0
        self._next_future_class = 0
        self.ledger.register_container(
            self._normalization_owner,
            self._normalizations,
            node_count=lambda: 0,
            payloads=self._normalizations.items,
            evict=self.clear_normalizations,
        )
        self.ledger.register_container(
            self._binding_owner,
            self._parents,
            node_count=lambda: 0,
            payloads=self._parents.items,
            evict=self.clear_bindings,
        )
        self.ledger.register_container(
            self._future_profile_owner,
            self._future_profiles,
            node_count=lambda: len(self._future_profiles),
            payloads=self._future_profiles.items,
        )
        self.ledger.register_container(
            self._future_profile_key_owner,
            self._future_profile_keys,
            node_count=lambda: 0,
            payloads=self._future_profile_keys.items,
        )
        self.ledger.register_container(
            self._future_class_owner,
            self._future_classes,
            node_count=lambda: len(self._future_classes),
            payloads=self._future_classes.items,
        )
        self.ledger.register_container(
            self._future_class_key_owner,
            self._future_class_keys,
            node_count=lambda: 0,
            payloads=self._future_class_keys.items,
        )
        self.ledger.register_container(
            self._future_certificate_owner,
            self._future_certificates,
            node_count=lambda: 0,
            payloads=self._future_certificates.items,
        )
        self.ledger.register_container(
            self._future_admission_owner,
            self._future_admissions,
            node_count=lambda: 0,
            payloads=self._future_admissions.items,
        )
        self.ledger.register_container(
            self._future_snapshot_owner,
            self._future_snapshots,
            node_count=lambda: 0,
            payloads=self._future_snapshots.items,
        )
        self.ledger.register_container(
            self._future_work_owner,
            self.ledger.make_list(self._future_work_owner, nodes_per_entry=0),
            node_count=lambda: 0,
            payloads=lambda: (),
        )

    @property
    def parents(self) -> Mapping[DiamondKey, DiamondQuotientID]:
        """Parent bindings are published only through the checked boundary."""
        return MappingProxyType(self._parents)

    @property
    def closed_workspace(self) -> ClosedInterfaceWorkspace:
        """Ledger owner for bounded closed-function construction scratch."""
        return self._closed_workspace

    def _component_signature(self, reference: SemanticComponent) -> FunctionSignature:
        if (
            type(reference) is RadixPortFunction
            or type(reference) is ReversePortFunction
        ):
            reference.__post_init__()
            return reference.signature
        if type(reference) is SemanticFunctionID:
            return self.functions.signature(reference)
        if type(reference) is StructureID:
            return self.structures.resolve(reference).signature
        raise ValueError("complete component requires a canonical semantic handle")

    def _validate_interface(self, interface: MacroInterface) -> None:
        if (
            type(interface) is not MacroInterface
            or type(interface.kernel) is not SemanticIdentity
        ):
            raise TypeError(
                "macro interface requires a frozen semantic kernel identity"
            )
        interface.kernel.__post_init__()
        if type(interface.outputs) is not tuple or len(interface.outputs) != len(
            COMPONENT_ROLES
        ):
            raise ValueError("complete macro interface requires every semantic channel")
        if type(interface.inputs) is not tuple:
            raise TypeError("macro input ports must be immutable")
        if (
            type(interface.phase_count) is not int
            or not 1 <= interface.phase_count <= 1 << 64
        ):
            raise ValueError("macro phases require a bounded finite domain")
        if (
            type(interface.orientations) is not tuple
            or not interface.orientations
            or any(
                type(value) is not int or value not in (0, 1)
                for value in interface.orientations
            )
            or interface.orientations != tuple(sorted(set(interface.orientations)))
        ):
            raise ValueError("macro orientations require a canonical finite domain")
        admissibility = self.functions.signature(interface.admissible)
        if admissibility.inputs != interface.inputs or admissibility.output != BOOL:
            raise ValueError(
                "admissibility must be a Boolean function on the full port bundle"
            )
        # FunctionSignature performs deep sort and finite-port validation.
        for output in interface.outputs:
            FunctionSignature(interface.inputs, output).__post_init__()

    def intern_interface(self, interface: MacroInterface) -> PortSignatureID:
        self._validate_interface(interface)
        found = self._signature_keys.get(interface)
        if found is not None:
            self.ledger.bump("quotient_signature_hits")
            return found
        self.ledger.reserve_many(
            ((self._signature_owner, 1, 1), (self._signature_key_owner, 1, 0))
        )
        result = PortSignatureID(
            self.owner, "diamond-semantic-signature", len(self._signatures)
        )
        self._signatures.append(interface)
        self._signature_keys[interface] = result
        self.ledger.bump("quotient_signature_evaluations")
        return result

    def interface(self, reference: PortSignatureID) -> MacroInterface:
        if type(reference) is not PortSignatureID:
            raise TypeError("expected a semantic port signature ID")
        ArenaHandle.validate(
            reference,
            self.owner,
            "diamond-semantic-signature",
            size=len(self._signatures),
        )
        return self._signatures[reference.local_id]

    def resolve(self, reference: DiamondQuotientID) -> QuotientRecord:
        if type(reference) is not DiamondQuotientID:
            raise TypeError("parent execution requires a complete diamond quotient ID")
        ArenaHandle.validate(
            reference, self.owner, "diamond-quotient", size=self._next_node
        )
        try:
            return self._nodes[reference.local_id]
        except KeyError:
            raise ValueError("stale or unpublished local interface") from None

    def resolve_future_profile(
        self,
        reference: FutureBehaviorProfileID,
    ) -> FutureBehaviorProfile:
        """Resolve a live profile without evaluating its semantic functions."""
        if type(reference) is not FutureBehaviorProfileID:
            raise TypeError("expected a future behavior profile ID")
        ArenaHandle.validate(
            reference,
            self.owner,
            "future-behavior-profile",
            size=self._next_future_profile,
        )
        found = self._future_profiles.get(reference.local_id)
        if found is None:
            raise ValueError("stale or unpublished future behavior profile")
        snapshot = self._future_snapshots.get(("profile", reference.local_id))
        if snapshot is None or not self._profile_matches(found, snapshot):
            raise ValueError("future behavior profile changed after publication")
        return found

    def resolve_future_behavior(
        self,
        reference: FutureBehaviorClassID,
    ) -> FutureBehaviorClass:
        """Resolve a completed successor-closed behavior class."""
        if type(reference) is not FutureBehaviorClassID:
            raise TypeError("expected a future behavior class ID")
        ArenaHandle.validate(
            reference,
            self.owner,
            "future-behavior-class",
            size=self._next_future_class,
        )
        found = self._future_classes.get(reference.local_id)
        if found is None:
            raise ValueError("stale or unpublished future behavior class")
        snapshot = self._future_snapshots.get(("class", reference.local_id))
        if snapshot is None or not self._class_matches(found, snapshot):
            raise ValueError("future behavior class changed after publication")
        profile = self.resolve_future_profile(found.profile)
        if found.output_symbol != profile.blank:
            raise ValueError("future blank class disagrees with its profile")
        return found

    def future_certificate(
        self,
        reference: FutureBehaviorProfileID,
    ) -> QuiescentBlankCertificate:
        """Return the frozen proof attached to a live admitted profile."""
        self.resolve_future_profile(reference)
        found = self._future_certificates.get(reference)
        if found is None:
            raise ValueError("future behavior profile has no published certificate")
        snapshot = self._future_snapshots.get(("certificate", reference.local_id))
        if snapshot is None or not self._certificate_matches(found, snapshot):
            raise ValueError("future behavior certificate changed after publication")
        return found

    @staticmethod
    def _profile_snapshot(profile: FutureBehaviorProfile) -> tuple[object, ...]:
        return (
            id(profile.kernel),
            profile.kernel.digest,
            id(profile.kernel.behavior),
            id(profile.continuation),
            profile.continuation.digest,
            id(profile.continuation.behavior),
            "int",
            profile.alphabet_size,
            "int",
            profile.blank,
            profile.observations,
            profile.admissible_left_states,
            profile.geometry_schema,
            profile.cocycle_schema,
            "int",
            profile.version,
            profile.certificate_digest,
        )

    @staticmethod
    def _profile_matches(
        profile: FutureBehaviorProfile,
        snapshot: tuple[object, ...],
    ) -> bool:
        return (
            len(snapshot) == 17
            and type(profile.kernel) is SemanticIdentity
            and type(profile.kernel.digest) is str
            and type(profile.kernel.behavior) is tuple
            and type(profile.continuation) is SemanticIdentity
            and type(profile.continuation.digest) is str
            and type(profile.continuation.behavior) is tuple
            and id(profile.kernel) == snapshot[0]
            and profile.kernel.digest == snapshot[1]
            and id(profile.kernel.behavior) == snapshot[2]
            and id(profile.continuation) == snapshot[3]
            and profile.continuation.digest == snapshot[4]
            and id(profile.continuation.behavior) == snapshot[5]
            and type(profile.alphabet_size) is int
            and snapshot[6] == "int"
            and profile.alphabet_size == snapshot[7]
            and type(profile.blank) is int
            and snapshot[8] == "int"
            and profile.blank == snapshot[9]
            and profile.observations is snapshot[10]
            and profile.admissible_left_states is snapshot[11]
            and profile.geometry_schema == snapshot[12]
            and profile.cocycle_schema == snapshot[13]
            and type(profile.version) is int
            and snapshot[14] == "int"
            and profile.version == snapshot[15]
            and profile.certificate_digest == snapshot[16]
        )

    @staticmethod
    def _class_snapshot(behavior: FutureBehaviorClass) -> tuple[object, ...]:
        return (
            behavior.profile.owner,
            behavior.profile.kind,
            behavior.profile.local_id,
            behavior.law,
            "int",
            behavior.output_symbol,
            "bool",
            behavior.active,
            "bool",
            behavior.termination,
            "int",
            behavior.normalization_symbol,
        )

    @staticmethod
    def _class_matches(
        behavior: FutureBehaviorClass,
        snapshot: tuple[object, ...],
    ) -> bool:
        return (
            type(behavior.profile) is FutureBehaviorProfileID
            and type(behavior.output_symbol) is int
            and type(behavior.active) is bool
            and type(behavior.termination) is bool
            and type(behavior.normalization_symbol) is int
            and DiamondQuotientArena._class_snapshot(behavior) == snapshot
        )

    @staticmethod
    def _certificate_snapshot(
        certificate: QuiescentBlankCertificate,
    ) -> tuple[object, ...]:
        return (
            id(certificate.kernel),
            certificate.kernel.digest,
            id(certificate.kernel.behavior),
            id(certificate.continuation),
            certificate.continuation.digest,
            id(certificate.continuation.behavior),
            "int",
            certificate.alphabet_size,
            "int",
            certificate.blank,
            certificate.safe_blank_left_states,
            certificate.absorbing_blank_left_states,
            certificate.left_blank_transition,
            certificate.right_blank_transition,
            "int",
            certificate.refinement_rounds,
            certificate.semantic_digest,
        )

    @staticmethod
    def _certificate_matches(
        certificate: QuiescentBlankCertificate,
        snapshot: tuple[object, ...],
    ) -> bool:
        return (
            len(snapshot) == 17
            and type(certificate.kernel) is SemanticIdentity
            and type(certificate.kernel.digest) is str
            and type(certificate.kernel.behavior) is tuple
            and type(certificate.continuation) is SemanticIdentity
            and type(certificate.continuation.digest) is str
            and type(certificate.continuation.behavior) is tuple
            and id(certificate.kernel) == snapshot[0]
            and certificate.kernel.digest == snapshot[1]
            and id(certificate.kernel.behavior) == snapshot[2]
            and id(certificate.continuation) == snapshot[3]
            and certificate.continuation.digest == snapshot[4]
            and id(certificate.continuation.behavior) == snapshot[5]
            and type(certificate.alphabet_size) is int
            and snapshot[6] == "int"
            and certificate.alphabet_size == snapshot[7]
            and type(certificate.blank) is int
            and snapshot[8] == "int"
            and certificate.blank == snapshot[9]
            and certificate.safe_blank_left_states is snapshot[10]
            and certificate.absorbing_blank_left_states is snapshot[11]
            and certificate.left_blank_transition is snapshot[12]
            and certificate.right_blank_transition is snapshot[13]
            and type(certificate.refinement_rounds) is int
            and snapshot[14] == "int"
            and certificate.refinement_rounds == snapshot[15]
            and certificate.semantic_digest == snapshot[16]
        )

    @staticmethod
    def _quotient_snapshot(quotient: PrimitiveBehaviorQuotient) -> tuple[object, ...]:
        return (
            id(quotient.source_identity),
            quotient.source_identity.digest,
            id(quotient.source_identity.behavior),
            id(quotient.semantic_identity),
            quotient.semantic_identity.digest,
            id(quotient.semantic_identity.behavior),
            "int",
            quotient.alphabet_size,
            "int",
            quotient.blank,
            quotient.left_classes,
            quotient.right_classes,
            quotient.left_representatives,
            quotient.right_representatives,
            quotient.left_transitions,
            quotient.right_transitions,
            quotient.outputs,
            quotient.channels,
            quotient.observations,
            "int",
            quotient.refinement_rounds,
        )

    @staticmethod
    def _quotient_matches(
        quotient: PrimitiveBehaviorQuotient,
        snapshot: tuple[object, ...],
    ) -> bool:
        if (
            type(quotient.source_identity) is not SemanticIdentity
            or type(quotient.source_identity.digest) is not str
            or type(quotient.source_identity.behavior) is not tuple
            or type(quotient.semantic_identity) is not SemanticIdentity
            or type(quotient.semantic_identity.digest) is not str
            or type(quotient.semantic_identity.behavior) is not tuple
            or type(quotient.alphabet_size) is not int
            or type(quotient.blank) is not int
            or type(quotient.refinement_rounds) is not int
        ):
            return False
        current = DiamondQuotientArena._quotient_snapshot(quotient)
        if len(current) != len(snapshot):
            return False
        reference_slots = frozenset((10, 11, 12, 13, 14, 15, 16, 17, 18))
        return all(
            left is right if index in reference_slots else left == right
            for index, (left, right) in enumerate(zip(current, snapshot, strict=True))
        )

    def admit_quiescent_blank(
        self,
        quotient: PrimitiveBehaviorQuotient,
    ) -> tuple[FutureBehaviorProfileID, FutureBehaviorClassID]:
        from number_compiler.hashlife.behavior.quiescent_admission import (
            admit_quiescent_blank,
        )

        return admit_quiescent_blank(self, quotient)

    def lookup_quiescent_blank(
        self,
        quotient: PrimitiveBehaviorQuotient,
    ) -> tuple[FutureBehaviorProfileID, FutureBehaviorClassID] | None:
        from number_compiler.hashlife.behavior.quiescent_admission import (
            lookup_quiescent_blank,
        )

        return lookup_quiescent_blank(self, quotient)

    def rollback_quiescent_blank_admission(
        self,
        quotient: PrimitiveBehaviorQuotient,
        profile: FutureBehaviorProfileID,
        behavior: FutureBehaviorClassID,
    ) -> None:
        from number_compiler.hashlife.behavior.quiescent_admission import (
            rollback_quiescent_blank_admission,
        )

        return rollback_quiescent_blank_admission(self, quotient, profile, behavior)

    def _validate_components(
        self, signature: PortSignatureID, components: MacroComponents
    ) -> MacroInterface:
        interface = self.interface(signature)
        if type(components) is not MacroComponents:
            raise TypeError("parent publication requires all semantic components")
        from number_compiler.hashlife.interfaces.tile_reverse_sector_functions import (
            validate_reverse_sectors,
        )

        validate_reverse_sectors(interface, components.reverse_sectors)
        for role, function, output in zip(
            COMPONENT_ROLES, components.functions(), interface.outputs, strict=True
        ):
            actual = self._component_signature(function)
            if actual != FunctionSignature(interface.inputs, output):
                raise ValueError(f"macro {role} has another semantic interface")
        if has_closed_components(components):
            validate_closed_components(self, interface, components)
        return interface

    def normalize(
        self, signature: PortSignatureID, components: MacroComponents
    ) -> MacroComponents:
        """Erase inadmissible assignments before semantic record interning.

        Every supplied component is already a canonical semantic function.
        This operation does not accept expression or closure recipes.
        """
        interface = self._validate_components(signature, components)
        from number_compiler.hashlife.interfaces.atomic_quotient_normalization import (
            atomic_product_is_masked,
        )

        if atomic_product_is_masked(self, interface, components):
            self.ledger.bump("quotient_atomic_mask_elisions")
            return components
        if has_closed_components(components):
            return components
        prepared = self._prepare_normalization(signature, components)
        try:
            prepared.reserve_with()
            prepared.publish_reserved()
            self.ledger.bump("quotient_complete_normalizations")
            return MacroComponents(
                *prepared.roots,
                reverse_sectors=components.reverse_sectors,
            )
        finally:
            prepared.cancel()

    def _prepare_normalization(
        self, signature: PortSignatureID, components: MacroComponents
    ) -> PreparedStructures:
        interface = self._validate_components(signature, components)
        if has_closed_components(components):
            raise ValueError("closed arithmetic cannot enter Boolean normalization")
        require_total_components(
            self.structures,
            tuple(
                function
                for function in components.functions()
                if type(function) is SemanticFunctionID or type(function) is StructureID
            ),
            interface.admissible,
        )
        builder = _Builder(self.structures)
        conversion = StructureConversion(builder)
        boolean_signature = FunctionSignature(interface.inputs, BOOL)
        predicate = builder.tx.map_terminals(
            interface.admissible.local_id,
            boolean_signature,
            lambda leaf: builder.tx.terminal(
                boolean_signature,
                SemanticTerminal("atom", int(leaf.kind == "atom" and leaf.value == 1)),
            ),
        )
        roots = tuple(
            conversion.convert(function)
            if type(function) is SemanticFunctionID
            else function.local_id
            if type(function) is StructureID
            else -1
            for function in components.functions()
        )
        normalized = tuple(
            builder.rewrite(_Rewrite(root, mask=predicate)) for root in roots
        )
        return prepare_structures(builder, normalized)

    def intern(
        self, signature: PortSignatureID, components: MacroComponents
    ) -> DiamondQuotientID:
        interface = self._validate_components(signature, components)
        request = QuotientRecord(signature, components)
        # Exact canonical records and previously normalized aliases are the
        # only legal pre-reduction hits.  The semantic interner itself is
        # probed only with the normalized record produced below.
        found = self._keys.get(request)
        if found is not None:
            self.ledger.bump("quotient_normal_form_early_hits")
            return found
        from number_compiler.hashlife.interfaces.atomic_quotient_normalization import (
            atomic_product_is_masked,
        )

        if atomic_product_is_masked(self, interface, components):
            self.ledger.bump("quotient_atomic_mask_elisions")
            return self._publish(request, None)
        if has_closed_components(components):
            arithmetic = self.normalize(signature, components)
            self.ledger.bump("quotient_arithmetic_normalizations")
            return self._publish(QuotientRecord(signature, arithmetic), None)
        found = self._normalizations.get(request)
        if found is not None:
            self.resolve(found)
            self.ledger.bump("quotient_normalization_memo_hits")
            return found
        prepared = self._prepare_normalization(signature, components)
        normalized = QuotientRecord(
            signature,
            MacroComponents(
                *prepared.roots,
                reverse_sectors=components.reverse_sectors,
            ),
        )
        result = self._publish(normalized, None, prepared, alias=request)
        self.ledger.bump("quotient_complete_normalizations")
        return result

    def _validate_key(self, key: DiamondKey) -> MacroInterface:
        if type(key) is not DiamondKey:
            raise TypeError("expected a canonical diamond request")
        before, after = self.resolve(key.before), self.resolve(key.after)
        interface = self.interface(key.signature)
        if before.signature != key.signature or after.signature != key.signature:
            raise ValueError("diamond operands have incompatible semantic signatures")
        if self.cells is None:
            raise ValueError("parent binding requires the owning source/image arena")
        cell = self.cells.resolve(key.cell)
        if (
            type(key.level) is not int
            or key.level != cell.level
            or type(key.orientation) is not int
            or key.orientation not in interface.orientations
            or type(key.phase) is not int
            or not 0 <= key.phase < interface.phase_count
        ):
            raise ValueError("diamond geometry or bounded phase is invalid")
        return interface

    def probe(self, key: DiamondKey) -> DiamondQuotientID | None:
        self._validate_key(key)
        self.ledger.bump("quotient_parent_requests")
        found = self._parents.get(key)
        if found is not None:
            self.resolve(found)
            self.ledger.bump("quotient_parent_early_hits")
        return found

    def publish(self, key: DiamondKey, result: DiamondQuotientID) -> DiamondQuotientID:
        """Bind only an allocated, minimized complete result, never a recipe."""
        self._validate_key(key)
        record = self.resolve(result)
        if record.signature != key.signature:
            raise ValueError("diamond result belongs to another semantic interface")
        return self._publish(record, key)

    def normalize_and_publish(
        self, key: DiamondKey, components: MacroComponents
    ) -> DiamondQuotientID:
        self._validate_key(key)
        # Check every component before a hit, including forged numeric IDs.
        self._validate_components(key.signature, components)
        found = self._parents.get(key)
        if found is not None:
            raise ValueError("compile only after probing an unresolved diamond")
        request = QuotientRecord(key.signature, components)
        if request in self._keys:
            self.ledger.bump("quotient_normal_form_early_hits")
            return self._publish(request, key)
        found = self._normalizations.get(request)
        if found is not None:
            self.resolve(found)
            self.ledger.bump("quotient_normalization_memo_hits")
            return self._publish(self.resolve(found), key)
        if has_closed_components(components):
            return self._publish(request, key)
        prepared = self._prepare_normalization(key.signature, components)
        normalized = QuotientRecord(
            key.signature,
            MacroComponents(
                *prepared.roots,
                reverse_sectors=components.reverse_sectors,
            ),
        )
        result = self._publish(normalized, key, prepared, alias=request)
        self.ledger.bump("quotient_complete_normalizations")
        return result

    def _publish(
        self,
        record: QuotientRecord,
        key: DiamondKey | None,
        prepared: PreparedStructures | None = None,
        *,
        alias: QuotientRecord | None = None,
    ) -> DiamondQuotientID:
        from number_compiler.hashlife.interfaces.quotient_publication import (
            publish_quotient,
        )

        return publish_quotient(self, record, key, prepared, alias=alias)

    def clear_bindings(self) -> None:
        count = len(self._parents)
        self._parents.clear()
        self.ledger.release(self._binding_owner, entries=count)

    def clear_normalizations(self) -> None:
        count = len(self._normalizations)
        self._normalizations.clear()
        self.ledger.release(self._normalization_owner, entries=count)


assert tuple(field.name for field in fields(MacroComponents)) == (
    *COMPONENT_ROLES,
    "reverse_sectors",
)

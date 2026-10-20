"""Complete extensional macro effects, distinct from construction programs.

Only normalized semantic functions enter this arena. Source/geometry bindings
belong to the parent memo, never to the semantic effect interner. This module
does not turn an arbitrary expression recipe into an extensional function;
the compiler must supply all components in the finite semantic algebra first.
"""

from __future__ import annotations

from collections.abc import Mapping, MutableMapping, MutableSequence
from dataclasses import fields
from types import MappingProxyType

from number_compiler.arithmetic.carry.reverse_port_functions import ReversePortFunction
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FunctionSignature,
    SemanticFunctionID,
    SemanticTerminal,
)
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.arithmetic.radix_port_functions import RadixPortFunction
from number_compiler.hashlife.actions.diamond_actions import (
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
from number_compiler.hashlife.behavior.quiescent_admission import (
    FutureBehaviorAdmission,
)
from number_compiler.hashlife.interfaces.closed_interface_admission import (
    has_closed_components,
    validate_closed_components,
)
from number_compiler.hashlife.interfaces.quotient_publication import (
    QuotientPublication,
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
    COMPONENT_ROLES,
    DiamondKey,
    DiamondQuotientID,
    MacroComponents,
    MacroInterface,
    QuotientRecord,
    SemanticComponent,
    StructureArena,
    StructureBuilder,
    StructureID,
    StructureRewrite,
)
from number_compiler.resources.closed_interface_workspace import (
    ClosedInterfaceWorkspace,
)
from number_compiler.resources.field_image_audit_contracts import (
    DiamondQuotientAuditSnapshot,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    hashlife_interfaces as _interfaces_keys,
)
from number_compiler.resources.metric_keys import shared as _shared_keys
from number_compiler.resources.stores import LedgerList


class DiamondQuotientArena(FutureBehaviorAdmission, QuotientPublication):
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
        future_work: LedgerList[int] = self.ledger.make_list(
            self._future_work_owner, nodes_per_entry=0
        )
        self.ledger.register_container(
            self._future_work_owner,
            future_work,
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
            self.ledger.bump(_interfaces_keys.QUOTIENT_SIGNATURE_HITS)
            return found
        self.ledger.reserve_many(
            ((self._signature_owner, 1, 1), (self._signature_key_owner, 1, 0))
        )
        result = PortSignatureID(
            self.owner, "diamond-semantic-signature", len(self._signatures)
        )
        self._signatures.append(interface)
        self._signature_keys[interface] = result
        self.ledger.bump(_interfaces_keys.QUOTIENT_SIGNATURE_EVALUATIONS)
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

    def audit_snapshot(self) -> DiamondQuotientAuditSnapshot:
        """Expose exact backing stores through a read-only audit view."""
        return DiamondQuotientAuditSnapshot(
            self.ledger,
            self.owner,
            self._next_node,
            self._signature_owner,
            self._signatures,
            self._signature_key_owner,
            self._signature_keys,
            self._node_owner,
            self._nodes,
            self._key_owner,
            self._keys,
            self._normalization_owner,
            self._normalizations,
            self._binding_owner,
            self._parents,
        )

    def future_behavior_store_counts(self) -> tuple[int, int, int, int]:
        """Count retained behavior profiles, classes, and their canonical keys."""
        return (
            len(self._future_profiles),
            len(self._future_profile_keys),
            len(self._future_classes),
            len(self._future_class_keys),
        )

    def validate_interface_record(self, interface: MacroInterface) -> None:
        """Validate an interface payload through the issuing quotient arena."""
        self._validate_interface(interface)

    def validate_quotient_record(self, record: QuotientRecord) -> None:
        """Validate a complete quotient payload through its semantic owner."""
        if type(record) is not QuotientRecord:
            raise TypeError("expected a canonical quotient record")
        self.validate_components(record.signature, record.components)

    def validate_parent_key(self, key: DiamondKey) -> None:
        """Validate a source-bound parent request through its issuing arena."""
        self._validate_key(key)

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

    def validate_components(
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
        interface = self.validate_components(signature, components)
        from number_compiler.hashlife.interfaces.atomic_quotient_normalization import (
            atomic_product_is_masked,
        )

        if atomic_product_is_masked(self, interface, components):
            self.ledger.bump(_interfaces_keys.QUOTIENT_ATOMIC_MASK_ELISIONS)
            return components
        if has_closed_components(components):
            return components
        prepared = self._prepare_normalization(signature, components)
        try:
            prepared.reserve_with()
            prepared.publish_reserved()
            self.ledger.bump(_interfaces_keys.QUOTIENT_COMPLETE_NORMALIZATIONS)
            return MacroComponents(
                *prepared.roots,
                reverse_sectors=components.reverse_sectors,
            )
        finally:
            prepared.cancel()

    def _prepare_normalization(
        self, signature: PortSignatureID, components: MacroComponents
    ) -> PreparedStructures:
        interface = self.validate_components(signature, components)
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
        builder = StructureBuilder(self.structures)
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
            builder.rewrite(StructureRewrite(root, mask=predicate)) for root in roots
        )
        return prepare_structures(builder, normalized)

    def intern(
        self, signature: PortSignatureID, components: MacroComponents
    ) -> DiamondQuotientID:
        interface = self.validate_components(signature, components)
        request = QuotientRecord(signature, components)
        # Exact canonical records and previously normalized aliases are the
        # only legal pre-reduction hits.  The semantic interner itself is
        # probed only with the normalized record produced below.
        found = self._keys.get(request)
        if found is not None:
            self.ledger.bump(_interfaces_keys.QUOTIENT_NORMAL_FORM_EARLY_HITS)
            return found
        from number_compiler.hashlife.interfaces.atomic_quotient_normalization import (
            atomic_product_is_masked,
        )

        if atomic_product_is_masked(self, interface, components):
            self.ledger.bump(_interfaces_keys.QUOTIENT_ATOMIC_MASK_ELISIONS)
            return self._publish(request, None)
        if has_closed_components(components):
            arithmetic = self.normalize(signature, components)
            self.ledger.bump(_shared_keys.QUOTIENT_ARITHMETIC_NORMALIZATIONS)
            return self._publish(QuotientRecord(signature, arithmetic), None)
        found = self._normalizations.get(request)
        if found is not None:
            self.resolve(found)
            self.ledger.bump(_interfaces_keys.QUOTIENT_NORMALIZATION_MEMO_HITS)
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
        self.ledger.bump(_interfaces_keys.QUOTIENT_COMPLETE_NORMALIZATIONS)
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
        self.ledger.bump(_interfaces_keys.QUOTIENT_PARENT_REQUESTS)
        found = self._parents.get(key)
        if found is not None:
            self.resolve(found)
            self.ledger.bump(_interfaces_keys.QUOTIENT_PARENT_EARLY_HITS)
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
        self.validate_components(key.signature, components)
        found = self._parents.get(key)
        if found is not None:
            raise ValueError("compile only after probing an unresolved diamond")
        request = QuotientRecord(key.signature, components)
        if request in self._keys:
            self.ledger.bump(_interfaces_keys.QUOTIENT_NORMAL_FORM_EARLY_HITS)
            return self._publish(request, key)
        found = self._normalizations.get(request)
        if found is not None:
            self.resolve(found)
            self.ledger.bump(_interfaces_keys.QUOTIENT_NORMALIZATION_MEMO_HITS)
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
        self.ledger.bump(_interfaces_keys.QUOTIENT_COMPLETE_NORMALIZATIONS)
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

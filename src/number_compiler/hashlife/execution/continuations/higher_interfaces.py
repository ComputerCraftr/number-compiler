"""Complete thirteen-channel interfaces over recursive higher state ports.

This is the typed publication boundary used when a macro action's boundary is
itself a product containing a continuation function.  It deliberately does
not coerce higher programs to integer terminals or enumerate their domains.
The component arena has already alpha-normalized and hash-consed every
expression/function before this arena publishes a complete interface.
"""

from __future__ import annotations

from collections.abc import Callable, MutableMapping, MutableSequence
from dataclasses import dataclass, fields
from typing import TypeAlias, cast

from number_compiler.arithmetic.contracts.canonical_payload import (
    validate_bounded_semantic_key,
)
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import CoordinateOutputMorphismID
from number_compiler.hashlife.execution.continuations.higher_semantic import (
    HigherSemanticArena,
)
from number_compiler.hashlife.execution.continuations.higher_types import (
    HigherExpressionID,
    HigherFunctionID,
    HigherSort,
)
from number_compiler.hashlife.interfaces.diamond_quotient import (
    COMPONENT_ROLES,
    LocalInterfaceID,
)
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class HigherMorphismSort:
    """Scoped terminal sort for a recursive coordinate output morphism."""

    owner: ArenaToken
    kind: str


HigherComponentID: TypeAlias = (
    HigherExpressionID | HigherFunctionID | CoordinateOutputMorphismID
)
HigherOutputSort: TypeAlias = HigherSort | HigherMorphismSort


@dataclass(frozen=True, slots=True)
class HigherPort:
    """One explicitly named structured input to a higher macro behavior."""

    variable: HigherExpressionID
    role: str

    def __post_init__(self) -> None:
        if type(self.variable) is not HigherExpressionID:
            raise TypeError("higher ports require scoped expression variables")
        if type(self.role) is not str or not self.role or len(self.role) > 128:
            raise ValueError("higher ports require a stable semantic role")


@dataclass(frozen=True, slots=True)
class HigherMacroInterface:
    kernel: SemanticIdentity
    inputs: tuple[HigherPort, ...]
    outputs: tuple[HigherOutputSort, ...]
    phase_count: int = 1

    def __post_init__(self) -> None:
        if type(self.kernel) is not SemanticIdentity:
            raise TypeError("higher interface requires immutable semantic identity")
        self.kernel.__post_init__()
        validate_bounded_semantic_key(self.kernel.behavior, max_units=256)
        if type(self.inputs) is not tuple or type(self.outputs) is not tuple:
            raise TypeError("higher interface declarations must be immutable")
        if any(type(port) is not HigherPort for port in self.inputs):
            raise TypeError("higher interface inputs require typed port declarations")
        for port in self.inputs:
            port.__post_init__()
        if len(self.outputs) != len(COMPONENT_ROLES):
            raise ValueError("higher interface requires all thirteen semantic channels")
        if len({port.role for port in self.inputs}) != len(self.inputs):
            raise ValueError("higher interface input roles must be unique")
        if len({port.variable for port in self.inputs}) != len(self.inputs):
            raise ValueError("higher interface input variables must be unique")
        if type(self.phase_count) is not int or not 1 <= self.phase_count <= 1 << 64:
            raise ValueError(
                "higher interface phase count is outside its bounded domain"
            )


@dataclass(frozen=True, slots=True)
class HigherMacroComponents:
    boundary_left: HigherComponentID
    boundary_right: HigherComponentID
    output: HigherComponentID
    activity: HigherComponentID
    first_active: HigherComponentID
    last_active: HigherComponentID
    extent: HigherComponentID
    halo_left: HigherComponentID
    halo_right: HigherComponentID
    growth: HigherComponentID
    termination: HigherComponentID
    normalization: HigherComponentID
    frame: HigherComponentID

    def functions(self) -> tuple[HigherComponentID, ...]:
        return tuple(getattr(self, role) for role in COMPONENT_ROLES)


@dataclass(frozen=True, slots=True)
class HigherInterfaceRecord:
    signature: PortSignatureID
    components: HigherMacroComponents


class HigherLocalInterfaceArena:
    """A ``LocalInterfaceID`` arena whose components have recursive sorts.

    Recursive components have their own typed publication contract.  They are
    not substitutable for finite-function interfaces and do not allocate the
    unused finite quotient arenas.
    """

    _SIGNATURE_KIND = "higher-semantic-signature"
    _INTERFACE_KIND = "higher-local-interface"

    @property
    def signature_kind(self) -> str:
        return self._SIGNATURE_KIND

    @property
    def interface_kind(self) -> str:
        return self._INTERFACE_KIND

    def __init__(self, semantics: HigherSemanticArena) -> None:
        if type(semantics) is not HigherSemanticArena:
            raise TypeError("higher local interfaces require their semantic arena")
        self.semantics = semantics
        self._morphism_sort: HigherMorphismSort | None = None
        self._morphism_validate: (
            Callable[[CoordinateOutputMorphismID], object] | None
        ) = None
        self.ledger: ResourceLedger = semantics.ledger
        self.owner = ArenaToken("higher-local-interfaces")
        self.ledger.register_execution_root(self)
        prefix = f"higher-local-interface-{len(self.ledger.inventory())}"
        self._higher_signature_owner = self.ledger.register(
            prefix + "-signatures",
            "higher_port_signature",
        )
        self._higher_signature_key_owner = self.ledger.register(
            prefix + "-signature-keys",
            "higher_port_signature_interner",
        )
        self._higher_node_owner = self.ledger.register(
            prefix + "-nodes",
            "higher_local_interface",
        )
        self._higher_key_owner = self.ledger.register(
            prefix + "-keys",
            "higher_local_interface_interner",
        )
        self._higher_signatures: MutableSequence[HigherMacroInterface] = (
            self.ledger.make_list(self._higher_signature_owner)
        )
        self._higher_signature_keys: MutableMapping[
            HigherMacroInterface, PortSignatureID
        ] = self.ledger.make_dict(self._higher_signature_key_owner)
        self._higher_nodes: MutableSequence[HigherInterfaceRecord] = (
            self.ledger.make_list(
                self._higher_node_owner,
            )
        )
        self._higher_keys: MutableMapping[HigherInterfaceRecord, LocalInterfaceID] = (
            self.ledger.make_dict(self._higher_key_owner)
        )
        self.ledger.register_container(
            self._higher_signature_owner,
            self._higher_signatures,
            node_count=lambda: len(self._higher_signatures),
            payloads=lambda: self._higher_signatures,
        )
        self.ledger.register_container(
            self._higher_signature_key_owner,
            self._higher_signature_keys,
            payloads=self._higher_signature_keys.items,
        )
        self.ledger.register_container(
            self._higher_node_owner,
            self._higher_nodes,
            node_count=lambda: len(self._higher_nodes),
            payloads=lambda: self._higher_nodes,
        )
        self.ledger.register_container(
            self._higher_key_owner,
            self._higher_keys,
            payloads=self._higher_keys.items,
        )

    def bind_morphism_sort(
        self,
        owner: ArenaToken,
        kind: str,
        validate: Callable[[CoordinateOutputMorphismID], object],
    ) -> HigherMorphismSort:
        """Bind the one recursive output arena admitted by this interface arena."""
        if type(owner) is not ArenaToken or type(kind) is not str or not kind:
            raise TypeError("higher morphism sort requires a scoped arena identity")
        if not callable(validate):
            raise TypeError("higher morphism sort requires allocated-range validation")
        result = HigherMorphismSort(owner, kind)
        if self._morphism_sort not in (None, result):
            raise ValueError("higher interface already has another morphism arena")
        self._morphism_sort, self._morphism_validate = result, validate
        return result

    def _validate_interface(
        self,
        interface: HigherMacroInterface,
        *,
        readonly: bool = False,
    ) -> None:
        if type(interface) is not HigherMacroInterface:
            raise TypeError("expected a higher macro interface")
        interface.__post_init__()
        for port in interface.inputs:
            node = self.semantics.expression(port.variable)
            if node.kind != "variable" or node.role != port.role:
                raise ValueError("higher interface port is not its canonical variable")
        for output in interface.outputs:
            if isinstance(output, HigherMorphismSort):
                if output != self._morphism_sort:
                    raise ValueError("higher interface has another morphism sort")
            else:
                self.semantics._validate_sort(output, readonly=readonly)

    def intern_interface(
        self,
        interface: HigherMacroInterface,
    ) -> PortSignatureID:
        self._validate_interface(interface)
        found = self._higher_signature_keys.get(interface)
        if found is not None:
            self.ledger.bump("higher_interface_signature_hits")
            return found
        self.ledger.reserve_many(
            (
                (self._higher_signature_owner, 1, 1),
                (self._higher_signature_key_owner, 1, 0),
            )
        )
        result = PortSignatureID(
            self.owner,
            self._SIGNATURE_KIND,
            len(self._higher_signatures),
        )
        self._higher_signatures.append(interface)
        self._higher_signature_keys[interface] = result
        self.ledger.bump("higher_interface_signature_evaluations")
        return result

    def interface(self, reference: PortSignatureID) -> HigherMacroInterface:
        if type(reference) is not PortSignatureID:
            raise TypeError("expected a higher semantic signature ID")
        reference.validate(
            self.owner,
            self._SIGNATURE_KIND,
            size=len(self._higher_signatures),
        )
        return self._higher_signatures[reference.local_id]

    def _validate_components(
        self,
        signature: PortSignatureID,
        components: HigherMacroComponents,
    ) -> HigherMacroInterface:
        interface = self.interface(signature)
        if type(components) is not HigherMacroComponents:
            raise TypeError("higher publication requires all thirteen components")
        declared = {port.variable for port in interface.inputs}
        for role, component, output in zip(
            COMPONENT_ROLES,
            components.functions(),
            interface.outputs,
            strict=True,
        ):
            if isinstance(output, HigherMorphismSort):
                if type(component) is not CoordinateOutputMorphismID:
                    raise TypeError(f"higher {role} requires a coordinate morphism")
                component.validate(output.owner, output.kind)
                validate = self._morphism_validate
                if validate is None:
                    raise ValueError("higher morphism arena is not bound")
                validate(component)
                continue
            if type(component) not in (HigherExpressionID, HigherFunctionID):
                raise TypeError(f"higher {role} has another component sort")
            scalar = cast(HigherExpressionID | HigherFunctionID, component)
            if self.semantics.component_sort(scalar) != output:
                raise ValueError(f"higher {role} has another result sort")
            free = set(self.semantics.component_free_variables(scalar))
            if not free <= declared:
                raise ValueError(f"higher {role} contains an undeclared input port")
        return interface

    def intern(
        self,
        signature: PortSignatureID,
        components: HigherMacroComponents,
    ) -> LocalInterfaceID:
        self._validate_components(signature, components)
        record = HigherInterfaceRecord(signature, components)
        found = self._higher_keys.get(record)
        if found is not None:
            self.ledger.bump("higher_interface_normal_form_hits")
            return found
        self.ledger.reserve_many(
            (
                (self._higher_node_owner, 1, 1),
                (self._higher_key_owner, 1, 0),
            )
        )
        result = LocalInterfaceID(
            self.owner,
            self._INTERFACE_KIND,
            len(self._higher_nodes),
        )
        self._higher_nodes.append(record)
        self._higher_keys[record] = result
        self.ledger.bump("higher_interface_publications")
        return result

    def resolve(self, reference: LocalInterfaceID) -> HigherInterfaceRecord:
        if type(reference) is not LocalInterfaceID:
            raise TypeError("expected a higher local-interface ID")
        reference.validate(
            self.owner, self._INTERFACE_KIND, size=len(self._higher_nodes)
        )
        return self._higher_nodes[reference.local_id]

    def normalize(
        self, signature: PortSignatureID, components: HigherMacroComponents
    ) -> HigherMacroComponents:
        """Higher components arrive canonical; syntax recipes are rejected."""
        if type(components) is not HigherMacroComponents:
            raise TypeError("higher normalization accepts only canonical components")
        self._validate_components(signature, components)
        return components


assert tuple(field.name for field in fields(HigherMacroComponents)) == COMPONENT_ROLES


__all__ = [
    "HigherComponentID",
    "HigherInterfaceRecord",
    "HigherLocalInterfaceArena",
    "HigherMacroComponents",
    "HigherMacroInterface",
    "HigherMorphismSort",
    "HigherOutputSort",
    "HigherPort",
]

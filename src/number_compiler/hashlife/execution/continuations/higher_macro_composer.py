"""Source-bound spatial composition of complete higher macro interfaces."""

from __future__ import annotations

from collections.abc import MutableMapping
from dataclasses import dataclass, fields
from hashlib import sha256
from typing import cast

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID,
    FieldCellActionID,
)
from number_compiler.hashlife.execution.continuations.higher_interfaces import (
    HigherInterfaceRecord,
    HigherLocalInterfaceArena,
    HigherMacroComponents,
    HigherMacroInterface,
    HigherMorphismSort,
    HigherOutputSort,
    HigherPort,
)
from number_compiler.hashlife.execution.continuations.higher_semantic import (
    HigherSemanticArena,
)
from number_compiler.hashlife.execution.continuations.higher_types import (
    FieldAtomSort,
    HigherExpressionID,
)
from number_compiler.hashlife.execution.field_images import (
    SourceBindingID,
    SourceCellArena,
    SourceCellID,
    SourceForestID,
)
from number_compiler.hashlife.execution.recursive_outputs import (
    RecursiveCoordinateMorphismArena,
)
from number_compiler.hashlife.execution.tile_absorption import (
    HigherBoundaryTransfer,
    HigherSpatialWiring,
    compose_higher_spatial_wiring,
    higher_boundary_transfer,
)
from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class SourceBoundHigherMacro:
    interface: LocalInterfaceID
    output: CoordinateOutputMorphismID
    width: int
    source_extent: int
    activity: HigherExpressionID
    first_active: HigherExpressionID
    last_active: HigherExpressionID
    extent: HigherExpressionID
    growth: HigherExpressionID


@dataclass(frozen=True, slots=True)
class _MacroBindingKey:
    action: FieldCellActionID
    source: SourceBindingID


@dataclass(frozen=True, slots=True)
class HigherMacroDeclaration:
    """Issued consumer law shared by source bindings and temporal images."""

    action: FieldCellActionID
    interface: LocalInterfaceID
    left: HigherExpressionID
    symbol: HigherExpressionID
    right: HigherExpressionID
    blank: int
    kernel_digest: str
    source_backed_temporal: bool
    morphism_sort: HigherMorphismSort

    def seal(self) -> tuple[tuple[object, ...], ...]:
        """Snapshot exact values independently of mutable-in-practice records."""
        if (
            type(self.action) is not FieldCellActionID
            or type(self.interface) is not LocalInterfaceID
            or any(
                type(port) is not HigherExpressionID
                for port in (self.left, self.symbol, self.right)
            )
            or type(self.blank) is not int
            or type(self.kernel_digest) is not str
            or type(self.source_backed_temporal) is not bool
            or type(self.morphism_sort) is not HigherMorphismSort
            or type(self.morphism_sort.owner) is not ArenaToken
            or type(self.morphism_sort.kind) is not str
        ):
            raise ValueError("higher spatial macro declaration has invalid types")
        result: list[tuple[object, ...]] = []
        for field in fields(self):
            value: object = getattr(self, field.name)
            if isinstance(value, ArenaHandle):
                value.__post_init__()
                result.append((type(value), value.owner, value.kind, value.local_id))
            elif isinstance(value, HigherMorphismSort):
                result.append((type(value), value.owner, value.kind))
            else:
                result.append((type(value), value))
        return tuple(result)


class HigherSpatialMacroComposer:
    """Compile source leaves and parents without emitting future coordinates."""

    def __init__(
        self,
        semantics: HigherSemanticArena,
        interfaces: HigherLocalInterfaceArena,
        outputs: RecursiveCoordinateMorphismArena,
        sources: SourceCellArena,
        action: FieldCellActionID,
        local_interface: LocalInterfaceID,
        left: HigherExpressionID,
        symbol: HigherExpressionID,
        right: HigherExpressionID,
        *,
        source_backed_temporal: bool = False,
    ) -> None:
        if any(
            owner.ledger is not semantics.ledger
            for owner in (interfaces, outputs, sources)
        ):
            raise ValueError("higher spatial macros require one index ledger")
        semantics.schema.validate_action(action)
        local = interfaces.resolve(local_interface)
        signature = interfaces.interface(local.signature)
        if tuple(port.role for port in signature.inputs) != (
            "left-boundary",
            "source-symbol",
            "right-boundary",
        ):
            raise ValueError("higher local macro requires its complete three ports")
        self.semantics, self.interfaces, self.outputs = semantics, interfaces, outputs
        self.sources, self.action = sources, action
        self.local_interface = local_interface
        self.kernel_digest = signature.kernel.digest
        self.left, self.symbol, self.right = left, symbol, right
        if type(source_backed_temporal) is not bool:
            raise TypeError("source-backed temporal selection must be Boolean")
        self.source_backed_temporal = source_backed_temporal
        self.blank = semantics.schema.alphabet(action)[1]
        self.ledger: ResourceLedger = semantics.ledger
        self.morphism_sort: HigherMorphismSort = interfaces.bind_morphism_sort(
            outputs.owner,
            outputs.kind,
            outputs.resolve,
        )
        self.ledger.register_execution_root(self)
        prefix = f"higher-spatial-macros-{len(self.ledger.inventory())}"
        self._binding_owner = self.ledger.register(
            prefix + "-bindings", "spatial_binding"
        )
        self._bindings: MutableMapping[_MacroBindingKey, SourceBoundHigherMacro] = (
            self.ledger.make_dict(self._binding_owner)
        )
        self.ledger.register_container(
            self._binding_owner,
            self._bindings,
            payloads=self._bindings.items,
        )
        self._declaration = self._current_declaration()
        self._declaration_seal = self._declaration.seal()
        self._issued_authority = (
            self.semantics,
            self.interfaces,
            self.outputs,
            self.sources,
            self.ledger,
            self.semantics.owner,
            self.interfaces.owner,
            self.outputs.owner,
            self.sources.owner,
            self._bindings,
            self._declaration,
            self._declaration_seal,
        )

    def _current_declaration(self) -> HigherMacroDeclaration:
        return HigherMacroDeclaration(
            self.action,
            self.local_interface,
            self.left,
            self.symbol,
            self.right,
            self.blank,
            self.kernel_digest,
            self.source_backed_temporal,
            self.morphism_sort,
        )

    def declaration(self) -> HigherMacroDeclaration:
        """Validate and return the original complete consumer declaration."""
        issued = self._issued_authority
        current = (
            self.semantics,
            self.interfaces,
            self.outputs,
            self.sources,
            self.ledger,
            self.semantics.owner,
            self.interfaces.owner,
            self.outputs.owner,
            self.sources.owner,
            self._bindings,
            self._declaration,
            self._declaration_seal,
        )
        if any(
            actual is not original
            for actual, original in zip(current, issued, strict=True)
        ):
            raise ValueError("higher spatial macro authority was changed")
        if (
            self._current_declaration().seal() != self._declaration_seal
            or self._declaration.seal() != self._declaration_seal
            or self.semantics.ledger is not self.ledger
            or self.interfaces.ledger is not self.ledger
            or self.outputs.ledger is not self.ledger
            or self.sources.ledger is not self.ledger
            or self.morphism_sort.owner is not self.outputs.owner
            or self.morphism_sort.kind != self.outputs.kind
            or not self.ledger.is_factory_container(self._bindings)
        ):
            raise ValueError("higher spatial macro declaration was changed")
        return self._declaration

    def _ports(self) -> tuple[HigherPort, HigherPort]:
        return HigherPort(self.left, "left-boundary"), HigherPort(
            self.right,
            "right-boundary",
        )

    def _scalar(self, value: object, role: str) -> HigherExpressionID:
        if type(value) is not HigherExpressionID:
            raise TypeError(f"higher spatial {role} is not a scalar expression")
        return value

    def _bound_interface(
        self, interface: LocalInterfaceID
    ) -> tuple[HigherInterfaceRecord, dict[str, HigherExpressionID]]:
        return self.interfaces.bound_interface(
            interface, error="higher child macro has another bound interface"
        )

    def _bound(
        self,
        interface: LocalInterfaceID,
        role: str,
        left: HigherExpressionID,
        right: HigherExpressionID,
    ) -> HigherExpressionID:
        record, ports = self._bound_interface(interface)
        value = self._scalar(getattr(record.components, role), role)
        return self.semantics.bind_free_many(
            value,
            ((ports["left-boundary"], left), (ports["right-boundary"], right)),
        )

    def _boundary_transfer(
        self,
        interface: LocalInterfaceID,
    ) -> HigherBoundaryTransfer:
        """Expose a child interface through the shared absorption algebra."""
        record, ports = self._bound_interface(interface)
        if ports["left-boundary"] != self.left or ports["right-boundary"] != self.right:
            raise ValueError("higher child macro has another port declaration")
        return higher_boundary_transfer(
            self.semantics,
            self.action,
            self.left,
            self.right,
            self._scalar(record.components.boundary_left, "boundary_left"),
            self._scalar(record.components.boundary_right, "boundary_right"),
        )

    def _spatial_wiring(
        self,
        left: SourceBoundHigherMacro,
        right: SourceBoundHigherMacro,
    ) -> HigherSpatialWiring:
        return compose_higher_spatial_wiring(
            self.semantics,
            self._boundary_transfer(left.interface),
            self._boundary_transfer(right.interface),
        )

    def _publish(
        self,
        identity: SemanticIdentity,
        components: HigherMacroComponents,
        outputs: tuple[object, ...],
    ) -> LocalInterfaceID:
        contract = HigherMacroInterface(
            identity,
            self._ports(),
            cast(tuple[HigherOutputSort, ...], outputs),
        )
        signature = self.interfaces.intern_interface(contract)
        return self.interfaces.intern(signature, components)

    def bind_symbol_expression(
        self,
        source_symbol: HigherExpressionID,
        *,
        source_extent: int,
    ) -> SourceBoundHigherMacro:
        """Construct one symbolic leaf; this grants no occurrence authority.

        This is the leaf constructor used by temporal image substitution.  The
        supplied symbol may depend on a separately admitted predecessor image,
        but this method only checks its semantic sort.  ``source_extent`` is
        symbolic composition metadata.  Callers must use ``validate_binding``
        or an issued temporal-image handle before treating the result as bound.
        """
        self.declaration()
        return self._bind_symbol_expression(
            source_symbol,
            source_extent=source_extent,
            source=None,
        )

    def _bind_symbol_expression(
        self,
        source_symbol: HigherExpressionID,
        *,
        source_extent: int,
        source: SourceCellID | None,
    ) -> SourceBoundHigherMacro:
        if self.semantics.expression(source_symbol).sort != self.semantics.symbol_sort(
            self.action
        ):
            raise ValueError("higher source symbol has another action alphabet")
        if type(source_extent) is not int or source_extent not in (0, 1):
            raise ValueError("higher source leaf extent must be zero or one")
        local = self.interfaces.resolve(self.local_interface)
        values = tuple(
            self.semantics.bind_free(
                self._scalar(component, role),
                self.symbol,
                source_symbol,
            )
            for role, component in zip(
                HigherMacroComponents.__dataclass_fields__,
                local.components.functions(),
                strict=True,
            )
        )
        components = HigherMacroComponents(*values)
        signature = self.interfaces.interface(local.signature)
        identity = SemanticIdentity(
            sha256(
                repr(
                    (
                        "source-bound-higher-leaf",
                        signature.kernel.digest,
                    )
                ).encode()
            ).hexdigest(),
            ("source-bound-higher-leaf", signature.kernel.digest),
        )
        interface = self._publish(
            identity,
            components,
            tuple(self.semantics.component_sort(value) for value in values),
        )
        output = (
            self.outputs.source_image(source, self.action, interface)
            if source is not None and self.source_backed_temporal
            else self.outputs.leaf(interface)
        )
        return SourceBoundHigherMacro(
            interface,
            output,
            1,
            source_extent,
            *(
                self._scalar(getattr(components, role), role)
                for role in (
                    "activity",
                    "first_active",
                    "last_active",
                    "extent",
                    "growth",
                )
            ),
        )

    def _leaf(self, source: SourceCellID) -> SourceBoundHigherMacro:
        symbol_value = self.sources.symbol(source)
        return self._bind_symbol_expression(
            self.semantics.symbol(self.action, symbol_value),
            source_extent=int(symbol_value != self.blank),
            source=source,
        )

    def combine(
        self,
        left: SourceBoundHigherMacro,
        right: SourceBoundHigherMacro,
    ) -> SourceBoundHigherMacro:
        """Compose symbolic macrocells without granting source authority."""
        self.declaration()
        if (
            type(left) is not SourceBoundHigherMacro
            or type(right) is not SourceBoundHigherMacro
        ):
            raise TypeError("higher spatial composition requires two canonical macros")
        for child in (left, right):
            self.interfaces.resolve(child.interface)
            self.outputs.resolve(child.output)
            if (
                type(child.width) is not int
                or child.width < 1
                or type(child.source_extent) is not int
                or not 0 <= child.source_extent <= child.width
            ):
                raise ValueError("higher spatial child has invalid extent metadata")
        return self._combine(left, right)

    def _combine(
        self,
        left: SourceBoundHigherMacro,
        right: SourceBoundHigherMacro,
    ) -> SourceBoundHigherMacro:
        arena = self.semantics
        incoming_left, incoming_right = self.left, self.right
        wiring = self._spatial_wiring(left, right)
        left_mid, right_mid = wiring.left_mid, wiring.right_mid

        def a(role: str) -> HigherExpressionID:
            return self._bound(left.interface, role, incoming_left, right_mid)

        def b(role: str) -> HigherExpressionID:
            return self._bound(right.interface, role, left_mid, incoming_right)

        boundary_left = wiring.transfer.left
        boundary_right = wiring.transfer.right

        def summary(
            child: SourceBoundHigherMacro,
            role: str,
            left_port: HigherExpressionID,
            right_port: HigherExpressionID,
        ) -> HigherExpressionID:
            value = getattr(child, role)
            return self.semantics.bind_free_many(
                value, ((self.left, left_port), (self.right, right_port))
            )

        active_a = summary(left, "activity", incoming_left, right_mid)
        active_b = summary(right, "activity", left_mid, incoming_right)
        boolean = FieldAtomSort("boolean", 2)
        zero, one = arena.constant(boolean, 0), arena.constant(boolean, 1)
        active = arena.select(active_a, one, active_b)
        width = left.width + right.width
        position = FieldAtomSort("field-active-position", width + 1)
        extent_sort = FieldAtomSort("field-active-extent", width + 1)
        absent = arena.constant(position, width)
        first = arena.select(
            active_a,
            arena.retag(
                summary(left, "first_active", incoming_left, right_mid),
                position,
            ),
            arena.select(
                active_b,
                arena.add_constant(
                    summary(right, "first_active", left_mid, incoming_right),
                    left.width,
                    position,
                ),
                absent,
            ),
        )
        last = arena.select(
            active_b,
            arena.add_constant(
                summary(right, "last_active", left_mid, incoming_right),
                left.width,
                position,
            ),
            arena.select(
                active_a,
                arena.retag(
                    summary(left, "last_active", incoming_left, right_mid),
                    position,
                ),
                absent,
            ),
        )
        extent = arena.select(
            active_b,
            arena.add_constant(
                summary(right, "extent", left_mid, incoming_right),
                left.width,
                extent_sort,
            ),
            arena.retag(
                summary(left, "extent", incoming_left, right_mid),
                extent_sort,
            ),
        )
        halo_left = arena.select(active_a, a("halo_left"), b("halo_left"))
        halo_right = arena.select(active_b, b("halo_right"), a("halo_right"))
        source_extent = (
            left.width + right.source_extent
            if right.source_extent
            else left.source_extent
        )
        growth_sort = FieldAtomSort("field-growth-biased", 2 * width + 1)
        growth = arena.add_constant(extent, width - source_extent, growth_sort)
        termination = arena.select(active, zero, one)
        output = self.outputs.branch(
            left.output,
            right.output,
            left.interface,
            right.interface,
            left.width,
        )
        # Coordinate magnitudes are recursive-summary metadata.  The local
        # interface retains only bounded presence/zero-offset observations,
        # so its port sorts cannot grow with this spatial parent.
        local_offset = arena.constant(FieldAtomSort("local-active-offset", 2), 0)
        local_extent = arena.select(active, one, zero)
        components = HigherMacroComponents(
            boundary_left,
            boundary_right,
            output,
            active,
            local_offset,
            local_offset,
            local_extent,
            halo_left,
            halo_right,
            zero,
            termination,
            output,
            a("frame"),
        )
        component_sorts: tuple[object, ...] = (
            arena.component_sort(boundary_left),
            arena.component_sort(boundary_right),
            self.morphism_sort,
            arena.component_sort(active),
            arena.component_sort(local_offset),
            arena.component_sort(local_offset),
            arena.component_sort(local_extent),
            arena.component_sort(halo_left),
            arena.component_sort(halo_right),
            arena.component_sort(zero),
            arena.component_sort(termination),
            self.morphism_sort,
            arena.component_sort(a("frame")),
        )
        identity = SemanticIdentity(
            sha256(
                repr(
                    (
                        "source-bound-higher-parent",
                        self.kernel_digest,
                    )
                ).encode()
            ).hexdigest(),
            (
                "source-bound-higher-parent",
                self.kernel_digest,
            ),
        )
        interface = self._publish(identity, components, component_sorts)
        return SourceBoundHigherMacro(
            interface,
            output,
            width,
            source_extent,
            active,
            first,
            last,
            extent,
            growth,
        )

    def _cell(self, source: SourceCellID) -> SourceBoundHigherMacro:
        # Validate the complete scoped identity before constructing or probing
        # an occurrence key.  In particular, a forged handle must not be able
        # to compare equal to a warm binding through its integer payload.
        self.sources.resolve(source)
        self.declaration()
        key = _MacroBindingKey(self.action, source)
        self.ledger.bump("higher_spatial_parent_requests")
        self.ledger.bump("spatial_parent_requests")
        found = self._bindings.get(key)
        if found is not None:
            self.ledger.bump("higher_spatial_parent_early_hits")
            self.ledger.bump("spatial_parent_cache_hits")
            return found
        pending = [(source, False)]
        while pending:
            current, ready = pending.pop()
            current_key = _MacroBindingKey(self.action, current)
            if current_key in self._bindings:
                continue
            node = self.sources.resolve(current)
            if node.level and not ready:
                left, right = self.sources.children(current)
                pending.extend(((current, True), (right, False), (left, False)))
                continue
            result = (
                self._leaf(current)
                if not node.level
                else self._combine(
                    *(
                        self._bindings[_MacroBindingKey(self.action, child)]
                        for child in self.sources.children(current)
                    )
                )
            )
            self.ledger.reserve(self._binding_owner, entries=1)
            self._bindings[current_key] = result
            self.ledger.bump("higher_spatial_parent_evaluations")
            self.ledger.bump("spatial_parent_evaluations")
        return self._bindings[key]

    def compile(self, source: SourceBindingID) -> SourceBoundHigherMacro:
        if type(source) is SourceCellID:
            return self._cell(source)
        if type(source) is not SourceForestID:
            raise TypeError("higher spatial macro requires a scoped source binding")
        forest = self.sources.resolve_forest(source)
        self.declaration()
        key = _MacroBindingKey(self.action, source)
        self.ledger.bump("higher_spatial_forest_requests")
        self.ledger.bump("spatial_parent_requests")
        found = self._bindings.get(key)
        if found is not None:
            self.ledger.bump("higher_spatial_forest_early_hits")
            self.ledger.bump("spatial_parent_cache_hits")
            return found
        macros = [self._cell(cell) for cell in forest.cells]
        while len(macros) > 1:
            combined: list[SourceBoundHigherMacro] = []
            for index in range(0, len(macros), 2):
                combined.append(
                    macros[index]
                    if index + 1 == len(macros)
                    else self._combine(macros[index], macros[index + 1])
                )
            macros = combined
        result = macros[0]
        self.ledger.reserve(self._binding_owner, entries=1)
        self._bindings[key] = result
        self.ledger.bump("higher_spatial_forest_evaluations")
        self.ledger.bump("spatial_parent_evaluations")
        return result

    def validate_binding(
        self,
        source: SourceBindingID,
        macro: SourceBoundHigherMacro,
    ) -> None:
        """Authenticate one live source occurrence and its compiled macro."""
        self.declaration()
        if type(macro) is not SourceBoundHigherMacro:
            raise TypeError("higher source binding requires a canonical macro")
        if type(source) is SourceCellID:
            self.sources.resolve(source)
        elif type(source) is SourceForestID:
            self.sources.resolve_forest(source)
        else:
            raise TypeError("higher source binding requires a scoped source")
        found = self._bindings.get(_MacroBindingKey(self.action, source))
        if found is None or found != macro:
            raise ValueError("higher macro is not bound to this source occurrence")
        self.interfaces.resolve(macro.interface)
        self.outputs.resolve(macro.output)

    def validate_provider_binding(
        self,
        provider: CoordinateOutputMorphismID,
        source: SourceBindingID,
        action: FieldCellActionID,
    ) -> None:
        """Authenticate a provider against its issued source and consumer action."""
        self.declaration()
        self.semantics.schema.validate_action(action)
        if action != self.action:
            raise ValueError("higher provider has another consumer action")
        if type(source) is SourceCellID:
            self.sources.resolve(source)
        elif type(source) is SourceForestID:
            self.sources.resolve_forest(source)
        else:
            raise TypeError("higher provider requires a scoped source binding")
        if type(provider) is not CoordinateOutputMorphismID:
            raise TypeError("higher provider requires a scoped output ID")
        self.outputs.resolve(provider)
        macro = self._bindings.get(_MacroBindingKey(self.action, source))
        if macro is None:
            raise ValueError("higher provider source was never compiled")
        self.validate_binding(source, macro)
        if macro.output != provider:
            raise ValueError("higher provider differs from its bound source output")

    def clear(self) -> None:
        """Discard source-specific construction memos after parent publication.

        The compiled interface and coordinate morphism live in their semantic
        arenas.  Keeping the source-to-intermediate-macro map after that point
        would retain a leaf-first occurrence tree that is neither part of the
        canonical parent nor needed to observe it.
        """
        retained = len(self._bindings)
        if not retained:
            return
        self._bindings.clear()
        self.ledger.release(self._binding_owner, entries=retained)


__all__ = [
    "HigherMacroDeclaration",
    "HigherSpatialMacroComposer",
    "SourceBoundHigherMacro",
]

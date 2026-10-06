"""Complete source-free higher interfaces for reverse/add field actions.

The compiler publishes the thirteen semantic channels for one local
coordinate as typed expressions over the two boundary states and the input
symbol.  It retains neither a source occurrence nor an emitted coordinate
table.  Temporal composition is delegated to ``HigherBimachineRuntime``,
which implements the output-complete two-sided bimachine equations.
"""

from __future__ import annotations

from collections.abc import MutableMapping
from dataclasses import dataclass
from typing import cast

from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID,
    FieldCellActionID,
)
from number_compiler.hashlife.execution.continuations.higher_bimachine import (
    HigherBimachineRuntime,
)
from number_compiler.hashlife.execution.continuations.higher_interfaces import (
    HigherLocalInterfaceArena,
    HigherMacroComponents,
    HigherMacroInterface,
    HigherPort,
)
from number_compiler.hashlife.execution.continuations.higher_semantic import (
    HigherSemanticArena,
)
from number_compiler.hashlife.execution.continuations.higher_types import (
    FieldAtomSort,
    HigherExpressionID,
)
from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.field_action import ReverseFieldActionArena
from number_compiler.sequences.reverse_add.higher_schema import (
    ReverseHigherActionSchema,
)


@dataclass(frozen=True, slots=True)
class ReverseHigherInterfaceCompilation:
    """Canonical complete local behavior, ready for a field transfer."""

    action: FieldCellActionID
    signature: PortSignatureID
    interface: LocalInterfaceID
    output_morphism: CoordinateOutputMorphismID
    left: HigherExpressionID
    symbol: HigherExpressionID
    right: HigherExpressionID


class ReverseHigherInterfaceCompiler:
    """Compile complete reverse local effects before source binding."""

    def __init__(
        self,
        actions: ReverseFieldActionArena,
        schema: ReverseHigherActionSchema,
        semantics: HigherSemanticArena,
        runtime: HigherBimachineRuntime,
        interfaces: HigherLocalInterfaceArena,
    ) -> None:
        if schema.actions is not actions or semantics.schema is not schema:
            raise ValueError("reverse higher compiler requires one action schema")
        if runtime.semantics is not semantics or interfaces.semantics is not semantics:
            raise ValueError("reverse higher compiler requires one semantic arena")
        ledger = actions.ledger
        if any(
            owner.ledger is not ledger for owner in (semantics, runtime, interfaces)
        ):
            raise ValueError("reverse higher compiler requires one index ledger")
        self.actions = actions
        self.schema = schema
        self.semantics = semantics
        self.runtime = runtime
        self.interfaces = interfaces
        self.ledger: ResourceLedger = ledger
        ledger.register_execution_root(self)
        prefix = f"reverse-higher-compiler-{len(ledger.inventory())}"
        self._cache_owner = ledger.register(prefix + "-cache", "query_memo")
        self._cache: MutableMapping[
            FieldCellActionID, ReverseHigherInterfaceCompilation
        ] = ledger.make_dict(self._cache_owner)
        ledger.register_container(
            self._cache_owner,
            self._cache,
            payloads=self._cache.items,
            evict=self.clear,
        )
        from number_compiler.sequences.reverse_add.higher_interface_audit import (
            register_reverse_higher_interface_contract,
        )

        register_reverse_higher_interface_contract(self)

    def clear(self) -> None:
        count = len(self._cache)
        self._cache.clear()
        self.ledger.release(self._cache_owner, entries=count)

    def _bounded_constant(
        self,
        role: str,
        value: int,
        maximum: int,
    ) -> HigherExpressionID:
        if (
            type(value) is not int
            or type(maximum) is not int
            or not 0 <= value <= maximum
        ):
            raise ValueError(f"reverse {role} lies outside its bounded interface")
        return self.semantics.constant(FieldAtomSort(role, max(2, maximum + 1)), value)

    def compile(self, action: FieldCellActionID) -> ReverseHigherInterfaceCompilation:
        """Publish one output-complete local action, canonical before source work."""
        self.actions.validate_action(action)
        found = self._cache.get(action)
        if found is not None:
            self.ledger.bump("reverse_higher_interface_early_hits")
            return found

        arena = self.semantics
        field = self.actions.resolve(action)
        left = arena.variable(arena.state_sort(action, 0), "left-boundary")
        symbol = arena.variable(arena.symbol_sort(action), "source-symbol")
        right = arena.variable(arena.state_sort(action, 1), "right-boundary")
        if self.schema.kind(action) == "primitive":
            boundary_left = arena.primitive_step(action, 0, left, symbol)
            boundary_right = arena.primitive_step(action, 1, right, symbol)
            output = arena.primitive_emit(action, left, symbol, right)
        else:
            boundary_left = self.runtime.step(action, 0, left, symbol)
            boundary_right = self.runtime.step(action, 1, right, symbol)
            output = self.runtime.emit(action, left, symbol, right)

        blank = self.schema.alphabet(action)[1]
        boolean = FieldAtomSort("boolean", 2)
        zero = arena.constant(boolean, 0)
        one = arena.constant(boolean, 1)
        output_blank = arena.equal_constant(output, blank)
        input_blank = arena.equal_constant(symbol, blank)
        active = arena.select(output_blank, zero, one)
        local_position = arena.constant(FieldAtomSort("field-active-position", 2), 0)
        growth = arena.select(input_blank, active, zero)
        geometry = field.geometry
        halo_left = self._bounded_constant(
            "halo-left",
            geometry.halo_left,
            geometry.halo_left,
        )
        halo_right = self._bounded_constant(
            "halo-right",
            geometry.halo_right,
            geometry.halo_right,
        )
        frame = self._bounded_constant(
            "frame-phase",
            geometry.phase,
            geometry.phase_count - 1,
        )
        components = HigherMacroComponents(
            boundary_left=boundary_left,
            boundary_right=boundary_right,
            output=output,
            activity=active,
            first_active=local_position,
            last_active=local_position,
            extent=active,
            halo_left=halo_left,
            halo_right=halo_right,
            growth=growth,
            termination=output_blank,
            normalization=output,
            frame=frame,
        )
        ports = (
            HigherPort(left, "left-boundary"),
            HigherPort(symbol, "source-symbol"),
            HigherPort(right, "right-boundary"),
        )
        contract = HigherMacroInterface(
            self.actions.semantic_identity(action),
            ports,
            tuple(
                arena.component_sort(cast(HigherExpressionID, component))
                for component in components.functions()
            ),
            geometry.phase_count,
        )
        signature = self.interfaces.intern_interface(contract)
        interface = self.interfaces.intern(signature, components)
        result = ReverseHigherInterfaceCompilation(
            action,
            signature,
            interface,
            field.output,
            left,
            symbol,
            right,
        )
        self.ledger.reserve(self._cache_owner, entries=1)
        self._cache[action] = result
        self.ledger.bump("reverse_higher_interface_publications")
        return result


__all__ = [
    "ReverseHigherInterfaceCompilation",
    "ReverseHigherInterfaceCompiler",
]

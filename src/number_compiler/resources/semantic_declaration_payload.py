"""Read-only proof of owned structured declaration memo bindings.

Paired structure walks transport lexical binders. Boolean proof states use
existing nodes and partial cubes; no production reducer or evaluator runs.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.interfaces.semantic_structures import (
    StructureArena,
    StructureDeclarationKey,
    StructureID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict

if TYPE_CHECKING:
    from number_compiler.resources.semantic_payload import SemanticPayloadRegistry


class SemanticDeclarationPayloadRegistry:
    def __init__(
        self, ledger: ResourceLedger, semantic: SemanticPayloadRegistry
    ) -> None:
        self.semantic = semantic
        self.keys: set[int] = set()
        self.invalid_bindings: set[tuple[int, int]] = set()
        actual = dict(ledger.iter_containers())
        for arena in semantic.structures:
            store, owner = arena._declarations._data, arena._declarations.owner
            if (
                type(store) is not LedgerDict
                or actual.get(owner) is not store
                or not ledger.is_factory_container(store)
            ):
                self.invalid_bindings.add((owner, id(store)))
                continue
            for key, value in store._data.items():
                try:
                    accepted = self._binding(arena, key, value)
                except (ValueError, TypeError, AttributeError, IndexError, KeyError):
                    accepted = False
                if accepted:
                    self.keys.add(id(key))
                else:
                    self.invalid_bindings.update(((owner, id(key)), (owner, id(value))))

    def _binding(self, arena: StructureArena, key: object, value: object) -> bool:
        if (
            type(key) is not StructureDeclarationKey
            or type(key.inputs) is not tuple
            or not self.semantic._signature(FunctionSignature(key.inputs, BOOL))
            or type(key.value) is not StructureID
            or key.value.owner is not arena.token
            or not self.semantic._structure_handle(key.value)
            or type(value) is not StructureID
            or value.owner is not arena.token
            or not self.semantic._structure_handle(value)
        ):
            return False
        original, target = arena.resolve(key.value), arena.resolve(value)
        if any(
            port not in key.inputs for port in original.signature.inputs
        ) or target.signature != FunctionSignature(
            key.inputs, original.signature.output
        ):
            return False
        return _structures_agree(arena, key.value, value)


def _structures_agree(
    arena: StructureArena, source: StructureID, target: StructureID
) -> bool:
    pending: list[
        tuple[StructureID, StructureID, tuple[tuple[PortVariable, PortVariable], ...]]
    ] = [(source, target, ())]
    seen = set()
    while pending:
        left, right, renaming = pending.pop()
        state = (left, right, renaming)
        if state in seen:
            continue
        seen.add(state)
        a, b = arena.resolve(left), arena.resolve(right)
        if a.kind != b.kind or a.signature.output != b.signature.output:
            return False
        mapping = dict(renaming)
        mapped = tuple(
            FinitePort(mapping.get(port.variable, port.variable), port.cardinality)
            for port in a.signature.inputs
        )
        if any(port not in b.signature.inputs for port in mapped):
            return False
        source_roots: tuple[int, ...] = (a.valid.local_id,)
        target_roots: tuple[int, ...] = (b.valid.local_id,)
        if a.atom is not None and b.atom is not None:
            source_roots += tuple(fn.local_id for fn in arena.bits.resolve(a.atom).bits)
            target_roots += tuple(fn.local_id for fn in arena.bits.resolve(b.atom).bits)
        if not _booleans_agree(
            arena.functions, source_roots, target_roots, mapping, b.signature.inputs
        ):
            return False
        if a.kind == "product":
            if len(a.components) != len(b.components):
                return False
            pending.extend(
                (x, y, renaming)
                for x, y in zip(a.components, b.components, strict=True)
            )
        elif a.kind == "function":
            if a.body is None or b.body is None or len(a.bound) != len(b.bound):
                return False
            for x, y in zip(a.bound, b.bound, strict=True):
                if x.cardinality != y.cardinality:
                    return False
                mapping[x.variable] = y.variable
            pending.append((a.body, b.body, tuple(sorted(mapping.items()))))
    return True


def _booleans_agree(
    arena: SemanticFunctionArena,
    source: tuple[int, ...],
    target: tuple[int, ...],
    renaming: dict[PortVariable, PortVariable],
    inputs: tuple[FinitePort, ...],
) -> bool:
    def renamed(var: PortVariable) -> PortVariable:
        base = PortVariable(var.time, var.side, var.role, 0)
        mapped = renaming.get(base, base)
        return PortVariable(mapped.time, mapped.side, mapped.role, var.bit)

    restricted = tuple(
        port for port in inputs if port.cardinality & (port.cardinality - 1)
    )
    positions = {port.variable: index for index, port in enumerate(restricted)}
    initial_cube = tuple((0, (1 << port.bits) - 1) for port in restricted)
    if len(source) != len(target):
        return False
    pending: list[
        tuple[
            tuple[int, ...],
            tuple[int, ...],
            tuple[tuple[PortVariable, bool], ...],
            tuple[tuple[int, int], ...],
        ]
    ] = [
        ((left,), (right,), (), initial_cube)
        for left, right in zip(source, target, strict=True)
    ]
    seen = set()
    while pending:
        roots, actual, assignments, cube = pending.pop()
        known = dict(assignments)
        normalized = []
        for root in roots:
            node = arena.nodes[root]
            while node.variable is not None and renamed(node.variable) in known:
                root = node.high if known[renamed(node.variable)] else node.low
                node = arena.nodes[root]
            normalized.append(root)
        roots = tuple(normalized)
        support = {renamed(var) for root in roots for var in arena.nodes[root].support}
        assignments = tuple((var, high) for var, high in assignments if var in support)
        state = (roots, actual, assignments, cube)
        if state in seen:
            continue
        seen.add(state)
        variables = support.difference(known)
        variables.update(
            node.variable
            for root in actual
            if (node := arena.nodes[root]).variable is not None
        )
        if not variables:
            left = tuple(arena.nodes[root].terminal for root in roots)
            right = tuple(arena.nodes[root].terminal for root in actual)
            if any(
                leaf is None or leaf.kind != "atom" or leaf.value not in (0, 1)
                for leaf in (*left, *right)
            ):
                return False
            expected = tuple(leaf.value for leaf in left if leaf is not None)
            result = tuple(leaf.value for leaf in right if leaf is not None)
            legal = all(
                low < port.cardinality
                for port, (low, _) in zip(restricted, cube, strict=True)
            )
            illegal = any(
                (low | remaining) >= port.cardinality
                for port, (low, remaining) in zip(restricted, cube, strict=True)
            )
            if legal and result != expected or illegal and any(result):
                return False
            continue
        variable = min(variables)
        for high in (False, True):
            next_actual = tuple(
                (node.high if high else node.low) if node.variable == variable else root
                for root in actual
                for node in (arena.nodes[root],)
            )
            next_cube = cube
            base = PortVariable(variable.time, variable.side, variable.role, 0)
            if base in positions:
                index = positions[base]
                low, remaining = cube[index]
                mask = 1 << variable.bit
                next_cube = (
                    cube[:index]
                    + ((low | mask if high else low, remaining & ~mask),)
                    + cube[index + 1 :]
                )
            next_assignments = (
                tuple(sorted((*assignments, (variable, high))))
                if variable in support
                else assignments
            )
            pending.append((roots, next_actual, next_assignments, next_cube))
    return True

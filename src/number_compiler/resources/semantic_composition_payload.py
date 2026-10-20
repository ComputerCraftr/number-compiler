"""Independent simultaneous-composition proof for actual bit memo bindings.

Proof states contain existing DAG roots and cofactors. They neither enumerate
primitive input tuples nor construct or publish replacement semantic functions.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, cast

from number_compiler.arithmetic.functions.finite_function_types import (
    AtomSort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
    BitSubstitutionKey,
    FactoredFunction,
    FactoredFunctionID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_store_validation import (
    audit_ledger_dict_registration,
)
from number_compiler.resources.semantic_declaration_payload import cofactor_cube
from number_compiler.resources.stores import LedgerDict

if TYPE_CHECKING:
    from number_compiler.resources.semantic_payload import SemanticPayloadRegistry


class SemanticCompositionPayloadRegistry:
    def __init__(
        self, ledger: ResourceLedger, semantic: SemanticPayloadRegistry
    ) -> None:
        self.semantic = semantic
        self.keys: set[int] = set()
        self.invalid_bindings: set[tuple[int, int]] = set()
        actual = dict(ledger.iter_containers())
        for arena in semantic.bits:
            snapshot = arena.composition_audit_snapshot()
            container = snapshot.container
            owner = snapshot.owner
            if not audit_ledger_dict_registration(
                actual, owner, container, self.invalid_bindings
            ):
                continue
            composition_store = cast(
                LedgerDict[BitSubstitutionKey, FactoredFunctionID], container
            )
            if not ledger.is_factory_container(composition_store):
                self.invalid_bindings.add((owner, id(snapshot.container)))
                continue
            for key, result in composition_store.items():
                try:
                    accepted = self._binding(arena, key, result)
                except (TypeError, ValueError, AttributeError, KeyError, IndexError):
                    accepted = False
                if accepted:
                    self.keys.add(id(key))
                else:
                    self.invalid_bindings.update(
                        ((owner, id(key)), (owner, id(result)))
                    )

    def _record(
        self, arena: BitFunctionArena, handle: object
    ) -> FactoredFunction | None:
        if (
            type(handle) is not FactoredFunctionID
            or handle.owner is not arena.token
            or not self.semantic.validate_bit_handle(handle)
        ):
            return None
        record = arena.resolve(handle)
        if any(
            fn.owner is not arena.functions.token for fn in (*record.bits, record.valid)
        ):
            return None
        return record

    def _binding(self, arena: BitFunctionArena, key: object, result: object) -> bool:
        if (
            type(key) is not BitSubstitutionKey
            or type(key.replacements) is not tuple
            or not key.replacements
        ):
            return False
        original = self._record(arena, key.function)
        target = self._record(arena, result)
        if original is None or target is None:
            return False
        declared = {port.variable: port for port in original.signature.inputs}
        replacements: dict[PortVariable, FactoredFunction] = {}
        previous: PortVariable | None = None
        for item in key.replacements:
            if (
                type(item) is not tuple
                or len(item) != 2
                or type(item[0]) is not PortVariable
            ):
                return False
            variable, handle = item
            PortVariable.__post_init__(variable)
            if (
                variable not in declared
                or previous is not None
                and not previous < variable
            ):
                return False
            replacement = self._record(arena, handle)
            if (
                replacement is None
                or type(replacement.signature.output) is not AtomSort
                or replacement.signature.output.cardinality
                != declared[variable].cardinality
            ):
                return False
            replacements[variable] = replacement
            previous = variable
        inputs = {
            port.variable: port
            for port in original.signature.inputs
            if port.variable not in replacements
        }
        for replacement in replacements.values():
            for port in replacement.signature.inputs:
                if port.variable in inputs and inputs[port.variable] != port:
                    return False
                inputs[port.variable] = port
        expected = FunctionSignature(
            tuple(inputs[var] for var in sorted(inputs)), original.signature.output
        )
        if target.signature != expected:
            return False
        return agreement(arena.functions, original, replacements, target)


def agreement(
    arena: SemanticFunctionArena,
    original: FactoredFunction,
    replacements: dict[PortVariable, FactoredFunction],
    target: FactoredFunction,
) -> bool:
    environment = tuple(
        sorted(
            (PortVariable(var.time, var.side, var.role, bit), root.local_id)
            for var, record in replacements.items()
            for bit, root in enumerate(record.bits)
        )
    )
    roots = tuple(root.local_id for root in (*original.bits, original.valid))
    actual = tuple(root.local_id for root in (*target.bits, target.valid))
    required = tuple(record.valid.local_id for record in replacements.values())
    restricted = tuple(
        port
        for port in target.signature.inputs
        if port.cardinality & (port.cardinality - 1)
    )
    positions = {port.variable: index for index, port in enumerate(restricted)}
    cube = tuple((0, (1 << port.bits) - 1) for port in restricted)
    pending: list[
        tuple[
            tuple[int, ...],
            tuple[tuple[PortVariable, int], ...],
            tuple[int, ...],
            tuple[int, ...],
            tuple[tuple[int, int], ...],
        ]
    ] = [(roots, environment, actual, required, cube)]
    seen: set[
        tuple[
            tuple[int, ...],
            tuple[tuple[PortVariable, int], ...],
            tuple[int, ...],
            tuple[int, ...],
            tuple[tuple[int, int], ...],
        ]
    ] = set()
    while pending:
        source, bindings, result, validities, bounds = pending.pop()
        mapping = dict(bindings)
        normalized: list[int] = []
        for identity in source:
            node = arena.nodes[identity]
            while node.variable is not None and node.variable in mapping:
                replacement = arena.nodes[mapping[node.variable]]
                if replacement.terminal is None:
                    break
                identity = node.high if replacement.terminal.value else node.low
                node = arena.nodes[identity]
            normalized.append(identity)
        source = tuple(normalized)
        support: set[PortVariable] = {
            var for identity in source for var in arena.nodes[identity].support
        }
        bindings = tuple(
            (var, identity) for var, identity in bindings if var in support
        )
        mapping = dict(bindings)
        state = (source, bindings, result, validities, bounds)
        if state in seen:
            continue
        seen.add(state)
        variables: set[PortVariable] = set()
        for identity in source:
            variable = arena.nodes[identity].variable
            if variable is not None:
                variable = (
                    arena.nodes[mapping[variable]].variable
                    if variable in mapping
                    else variable
                )
                if variable is not None:
                    variables.add(variable)
        # A later source bit can depend on an earlier external variable.
        # Split every live argument in global order, even before that source
        # bit becomes a root; otherwise a later revisit contradicts the cube.
        for identity in (*result, *validities, *(identity for _, identity in bindings)):
            current_variable = arena.nodes[identity].variable
            if current_variable is not None:
                variables.add(current_variable)
        if not variables:
            source_values = _terminals(arena, source)
            result_values = _terminals(arena, result)
            valid_values = _terminals(arena, validities)
            if source_values is None or result_values is None or valid_values is None:
                return False
            base_valid = source_values[-1] and all(valid_values)
            legal = all(
                low < port.cardinality
                for port, (low, _) in zip(restricted, bounds, strict=True)
            )
            illegal = any(
                (low | remaining) >= port.cardinality
                for port, (low, remaining) in zip(restricted, bounds, strict=True)
            )
            if not base_valid:
                expected = (0,) * len(source_values)
            elif result_values[-1]:
                if illegal:
                    return False
                expected = (*source_values[:-1], 1)
            else:
                if legal:
                    return False
                expected = (0,) * len(source_values)
            if result_values != expected:
                return False
            continue
        variable = min(variables)
        assert variable is not None
        for high in (False, True):

            def split(
                identity: int,
                *,
                selected_high: bool = high,
                selected_variable: PortVariable = variable,
            ) -> int:
                node = arena.nodes[identity]
                return (
                    (node.high if selected_high else node.low)
                    if node.variable == selected_variable
                    else identity
                )

            new_source: tuple[int, ...] = tuple(
                split(identity)
                if arena.nodes[identity].variable not in mapping
                else identity
                for identity in source
            )
            new_bounds = cofactor_cube(bounds, positions, variable, high)
            pending.append(
                (
                    new_source,
                    tuple((var, split(identity)) for var, identity in bindings),
                    tuple(map(split, result)),
                    tuple(map(split, validities)),
                    new_bounds,
                )
            )
    return True


def _terminals(
    arena: SemanticFunctionArena, roots: tuple[int, ...]
) -> tuple[int, ...] | None:
    leaves = tuple(arena.nodes[root].terminal for root in roots)
    if any(
        leaf is None or leaf.kind != "atom" or leaf.value not in (0, 1)
        for leaf in leaves
    ):
        return None
    return tuple(leaf.value for leaf in leaves if leaf is not None)

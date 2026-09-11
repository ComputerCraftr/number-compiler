"""Eta-long finite outputs factored into products, lambdas, and Boolean leaves.

Lambda bodies retain joint outer/bound ports. They are canonical functions,
not one specialized terminal per outer value. Function-valued INPUT ports are
not admitted. Bound aliases are separate from named semantic declarations.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from typing import Literal

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.arithmetic.functions.finite_function_types import (
    AtomSort,
    FinitePort,
    FunctionSignature,
    FunctionSort,
    ProductSort,
    SemanticFunctionID,
    SemanticSort,
    _ports,
    _sort,
    _union_inputs,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_function_transactions import (
    _Transaction,
)
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
    FactoredFunction,
    FactoredFunctionID,
    _Circuit,
    _PendingFunction,
    substitute_boolean,
)
from number_compiler.resources.ledger import OwnedMemo
from number_compiler.resources.stores import LedgerDict, LedgerList


@dataclass(frozen=True, slots=True)
class StructureID(ArenaHandle):
    """One canonical eta-long structured finite output."""


@dataclass(frozen=True, slots=True)
class StructureDeclarationKey:
    value: StructureID
    inputs: tuple[FinitePort, ...]

    def __post_init__(self) -> None:
        if type(self.value) is not StructureID:
            raise TypeError("declaration requires a canonical structured function")
        _ports(self.inputs)


@dataclass(frozen=True, slots=True)
class StructuredNode:
    signature: FunctionSignature
    kind: Literal["atom", "product", "function"]
    valid: SemanticFunctionID
    atom: FactoredFunctionID | None = None
    components: tuple[StructureID, ...] = ()
    body: StructureID | None = None
    bound: tuple[FinitePort, ...] = ()


@dataclass(frozen=True, slots=True)
class _Rewrite:
    root: int
    replacements: tuple[tuple[FinitePort, int], ...] = ()
    mask: int | None = None


class StructureArena:
    def __init__(self, bits: BitFunctionArena) -> None:
        if type(bits) is not BitFunctionArena:
            raise TypeError("structured semantics needs a factored bit arena")
        self.bits, self.functions, self.ledger = bits, bits.functions, bits.ledger
        self.token = ArenaToken("semantic-structures")
        self.ledger.register_execution_root(self)
        prefix = f"semantic-structures-{len(self.ledger.inventory())}"
        self.node_owner = self.ledger.register(prefix + "-nodes", "semantic_structure")
        self.key_owner = self.ledger.register(
            prefix + "-keys", "semantic_structure_interner"
        )
        self.nodes: LedgerList[StructuredNode] = self.ledger.make_list(self.node_owner)
        self.keys: LedgerDict[StructuredNode, int] = self.ledger.make_dict(
            self.key_owner
        )
        declaration_owner = self.ledger.register(prefix + "-declarations", "query_memo")
        self._declarations: OwnedMemo[StructureDeclarationKey, StructureID] = OwnedMemo(
            self.ledger, declaration_owner, evictable=True
        )

    def _handle(self, identity: int) -> StructureID:
        return StructureID(self.token, "semantic-structure", identity)

    def resolve(self, reference: StructureID) -> StructuredNode:
        if type(reference) is not StructureID:
            raise ValueError("structured output requires a scoped semantic handle")
        ArenaHandle.validate(
            reference, self.token, "semantic-structure", size=len(self.nodes)
        )
        return self.nodes[reference.local_id]

    def declare(
        self, value: StructureID, inputs: tuple[FinitePort, ...]
    ) -> StructureID:
        """Add finite declarations to a complete function before observing it.

        The cache is a semantic operation on canonical IDs, with no expression,
        source, generation, or observed scalar in its key or result.
        """
        node = self.resolve(value)
        _ports(inputs)
        if any(port not in inputs for port in node.signature.inputs):
            raise ValueError("declaration must preserve every existing finite input")
        self.ledger.bump("semantic_structure_declaration_requests")
        if inputs == node.signature.inputs:
            self.ledger.bump("semantic_structure_declaration_identity_hits")
            return value
        key = StructureDeclarationKey(value, inputs)
        cached = self._declarations.get(key)
        if cached is not None:
            cached_node = self.resolve(cached)
            if cached_node.signature != FunctionSignature(
                inputs, node.signature.output
            ):
                raise ValueError("cached declaration has another complete interface")
            self.ledger.bump("semantic_structure_declaration_early_hits")
            return cached
        if (
            self.ledger.max_cache_entries is not None
            and self.ledger.entries >= self.ledger.max_cache_entries
        ):
            from number_compiler.arithmetic.contracts.block_effect import (
                BlockContextBudgetExceeded,
            )

            raise BlockContextBudgetExceeded(
                "semantic declaration cache budget exhausted before construction"
            )
        builder = _Builder(self)
        mask = builder.circuit(inputs).admitted()
        root = builder.rewrite(_Rewrite(value.local_id, mask=mask))
        from number_compiler.hashlife.interfaces.semantic_structure_publication import (
            prepare_structures,
        )

        prepared = None
        try:
            prepared = prepare_structures(builder, (root,))
            prepared.reserve_with(((self._declarations.owner, 1, 0),))
            prepared.publish_reserved()
            result = prepared.roots[0]
            self._declarations._data[key] = result
            self.ledger.bump("semantic_structure_declaration_evaluations")
            return result
        finally:
            if prepared is None:
                builder.tx.close()
            else:
                prepared.cancel()

    def atom(self, function: FactoredFunctionID) -> StructureID:
        value = self.bits.resolve(function)
        builder = _Builder(self)
        root = builder.intern(
            StructuredNode(value.signature, "atom", value.valid, atom=function)
        )
        return builder.finish(root)

    def product(self, components: tuple[StructureID, ...]) -> StructureID:
        if type(components) is not tuple or not components:
            raise ValueError(
                "structured product requires immutable nonempty components"
            )
        nodes = tuple(self.resolve(item) for item in components)
        inputs = _union_inputs(*(node.signature.inputs for node in nodes))
        builder = _Builder(self)
        circuit = builder.circuit(inputs)
        valid = circuit.admitted()
        for node in nodes:
            valid = circuit.conjunction(
                valid, builder.tx.resign(node.valid.local_id, circuit.signature)
            )
        children = tuple(
            builder.rewrite(_Rewrite(item.local_id, mask=valid)) for item in components
        )
        signature = FunctionSignature(
            inputs, ProductSort(tuple(node.signature.output for node in nodes))
        )
        root = builder.intern(
            StructuredNode(
                signature,
                "product",
                self.functions._handle(valid),
                components=tuple(self._handle(item) for item in children),
            )
        )
        return builder.finish(root)

    def curry(
        self, body: StructureID, bound_ports: tuple[FinitePort, ...]
    ) -> StructureID:
        node = self.resolve(body)
        _ports(bound_ports)
        if any(port not in node.signature.inputs for port in bound_ports):
            raise ValueError("lambda declarations are not free inputs of its body")
        outer = tuple(port for port in node.signature.inputs if port not in bound_ports)
        aliases = _aliases(outer, bound_ports, node.signature.output)
        builder = _Builder(self)
        joint = _union_inputs(outer, aliases)
        replacements = tuple(
            (old, builder.variable(joint, new))
            for old, new in zip(bound_ports, aliases)
        )
        valid = builder.circuit(outer).admitted()
        rewritten = builder.rewrite(_Rewrite(body.local_id, replacements, valid))
        signature = FunctionSignature(
            outer, FunctionSort(bound_ports, node.signature.output)
        )
        root = builder.intern(
            StructuredNode(
                signature,
                "function",
                self.functions._handle(valid),
                body=self._handle(rewritten),
                bound=aliases,
            )
        )
        return builder.finish(root)

    def _arguments(
        self,
        declared: tuple[FinitePort, ...],
        arguments: Mapping[PortVariable, FactoredFunctionID],
    ) -> tuple[tuple[FinitePort, int], ...]:
        available = {port.variable: port for port in declared}
        result = []
        for variable, reference in arguments.items():
            if type(variable) is not PortVariable:
                raise ValueError("arguments require typed port names")
            PortVariable.__post_init__(variable)
            value = self.bits.resolve(reference)
            port = available.get(variable)
            if (
                port is None
                or type(value.signature.output) is not AtomSort
                or value.signature.output.cardinality != port.cardinality
            ):
                raise ValueError("argument has another finite input domain")
            result.append((port, reference.local_id))
        return tuple(sorted(result, key=lambda item: item[0].variable))

    def substitute(
        self,
        value: StructureID,
        replacements: Mapping[PortVariable, FactoredFunctionID],
    ) -> StructureID:
        node = self.resolve(value)
        arguments = self._arguments(node.signature.inputs, replacements)
        builder = _Builder(self)
        root = builder.rewrite(_Rewrite(value.local_id, arguments))
        return builder.finish(root)

    def apply(
        self,
        function: StructureID,
        arguments: Mapping[PortVariable, FactoredFunctionID],
    ) -> StructureID:
        node = self.resolve(function)
        if (
            node.kind != "function"
            or type(node.signature.output) is not FunctionSort
            or node.body is None
        ):
            raise ValueError("application requires a canonical function output")
        replacements = self._arguments(node.signature.output.inputs, arguments)
        if len(replacements) != len(node.bound):
            raise ValueError("application requires every declared argument")
        by_name = {port.variable: value for port, value in replacements}
        actual = tuple(
            (alias, by_name[declaration.variable])
            for declaration, alias in zip(node.signature.output.inputs, node.bound)
        )
        builder = _Builder(self)
        root = builder.rewrite(
            _Rewrite(node.body.local_id, actual, node.valid.local_id)
        )
        return builder.finish(root)

    def component(self, product: StructureID, index: int) -> StructureID:
        node = self.resolve(product)
        if (
            node.kind != "product"
            or type(index) is not int
            or not 0 <= index < len(node.components)
        ):
            raise ValueError("invalid structured product projection")
        return node.components[index]

    def evaluate_atom(
        self, value: StructureID, inputs: Mapping[PortVariable, int]
    ) -> int | None:
        node = self.resolve(value)
        if node.kind != "atom" or node.atom is None:
            raise ValueError("only a finite atom can be lowered to a scalar")
        return self.bits.evaluate(node.atom, inputs)


def _binding_height(output: SemanticSort) -> int:
    """Reserve lower variable bands for selectors of returned functions.

    This depends only on the immutable type, never on a particular expression
    or observation. Sibling product components may reuse a band because each
    has its own lexical scope. Nested functions require disjoint bands.
    """
    _sort(output)
    heights: dict[int, int] = {}
    pending = [(output, False)]
    while pending:
        current, ready = pending.pop()
        identity = id(current)
        if identity in heights:
            continue
        if type(current) is AtomSort:
            heights[identity] = 0
            continue
        if isinstance(current, ProductSort):
            children = current.items
        else:
            assert isinstance(current, FunctionSort)
            children = (current.output,)
        if ready:
            child_height = max(heights[id(child)] for child in children)
            heights[identity] = child_height + (
                len(current.inputs) if type(current) is FunctionSort else 0
            )
        else:
            pending.append((current, True))
            pending.extend((child, False) for child in children)
    return heights[id(output)]


def _aliases(
    outer: tuple[FinitePort, ...],
    declared: tuple[FinitePort, ...],
    output: SemanticSort | None = None,
) -> tuple[FinitePort, ...]:
    occupied = {port.variable for port in outer}
    aliases = []
    cursor = 0
    # Count available slots, not raw indices: externally bound names can leave
    # holes in the canonical band. Descendant selectors still precede every
    # enclosing entry port when they are renamed in the joint body.
    reserved = 0 if output is None else _binding_height(output)
    while reserved:
        variable = PortVariable(cursor, 0, "semantic-bound", 0)
        cursor += 1
        if variable not in occupied:
            reserved -= 1
    for declaration in declared:
        while True:
            variable = PortVariable(cursor, 0, "semantic-bound", 0)
            cursor += 1
            if variable not in occupied:
                break
        aliases.append(FinitePort(variable, declaration.cardinality))
        occupied.add(variable)
    return tuple(aliases)


class _Builder:
    def __init__(self, arena: StructureArena) -> None:
        self.arena = arena
        self.tx = _Transaction(arena.functions)
        self.bit_base = len(arena.bits.nodes)
        self.base = len(arena.nodes)
        self.bits: list[_PendingFunction] = []
        self.bit_keys: dict[_PendingFunction, int] = {}
        self.nodes: list[StructuredNode] = []
        self.keys: dict[StructuredNode, int] = {}
        self.rewrites: dict[_Rewrite, int] = {}
        self._circuits: dict[tuple[FinitePort, ...], _Circuit] = {}

    def circuit(self, inputs: tuple[FinitePort, ...]) -> _Circuit:
        self.arena.ledger.bump("semantic_structure_circuit_requests")
        existing = self._circuits.get(inputs)
        if existing is not None:
            self.arena.ledger.bump("semantic_structure_circuit_hits")
            return existing
        self.tx.reserve_workspace(entries=1)
        result = _Circuit(self.arena.functions, inputs, self.tx)
        self._circuits[inputs] = result
        self.arena.ledger.bump("semantic_structure_circuit_evaluations")
        self.arena.ledger.bump(
            "semantic_structure_circuit_workspace_peak",
            max(
                0,
                len(self._circuits)
                - self.arena.ledger.counters.get(
                    "semantic_structure_circuit_workspace_peak", 0
                ),
            ),
        )
        return result

    def node(self, identity: int) -> StructuredNode:
        return (
            self.arena.nodes[identity]
            if identity < self.base
            else self.nodes[identity - self.base]
        )

    def bit(self, identity: int) -> _PendingFunction:
        if identity >= self.bit_base:
            return self.bits[identity - self.bit_base]
        node = self.arena.bits.nodes[identity]
        return _PendingFunction(
            node.signature,
            tuple(item.local_id for item in node.bits),
            node.valid.local_id,
        )

    def intern_bit(self, value: _PendingFunction) -> int:
        record = FactoredFunction(
            value.signature,
            tuple(self.arena.functions._handle(item) for item in value.bits),
            self.arena.functions._handle(value.valid),
        )
        found = self.arena.bits.keys.get(record)
        if found is None:
            found = self.bit_keys.get(value)
        if found is not None:
            return found
        result = self.bit_base + len(self.bits)
        self.tx.reserve_staged(entries=2, nodes=1)
        try:
            self.bits.append(value)
            self.bit_keys[value] = result
        except BaseException:
            self.tx.close()
            raise
        return result

    def variable(self, inputs: tuple[FinitePort, ...], port: FinitePort) -> int:
        circuit = self.circuit(inputs)
        roots = tuple(
            self.tx.bit(
                inputs,
                PortVariable(
                    port.variable.time, port.variable.side, port.variable.role, bit
                ),
            )
            for bit in range(port.bits)
        )
        signature = FunctionSignature(
            inputs, AtomSort(port.variable.role, port.cardinality)
        )
        return self.intern_bit(circuit.normalized(signature, roots, circuit.admitted()))

    def intern(self, node: StructuredNode) -> int:
        found = self.arena.keys.get(node)
        if found is None:
            found = self.keys.get(node)
        if found is not None:
            return found
        identity = self.base + len(self.nodes)
        self.tx.reserve_staged(entries=2, nodes=1)
        try:
            self.nodes.append(node)
            self.keys[node] = identity
        except BaseException:
            self.tx.close()
            raise
        return identity

    def _prepare_rewrite(
        self, task: _Rewrite
    ) -> tuple[_Circuit, dict[PortVariable, int], int]:
        node = self.node(task.root)
        removed = {port.variable for port, _ in task.replacements}
        inputs = _union_inputs(
            tuple(
                port for port in node.signature.inputs if port.variable not in removed
            ),
            *(self.bit(value).signature.inputs for _, value in task.replacements),
            () if task.mask is None else self.tx.node(task.mask).signature.inputs,
        )
        circuit = self.circuit(inputs)
        valid = circuit.admitted()
        replacements: dict[PortVariable, int] = {}
        for port, identity in task.replacements:
            value = self.bit(identity)
            valid = circuit.conjunction(
                valid, self.tx.resign(value.valid, circuit.signature)
            )
            for bit, root in enumerate(value.bits):
                variable = PortVariable(
                    port.variable.time, port.variable.side, port.variable.role, bit
                )
                replacements[variable] = self.tx.resign(root, circuit.signature)
        old_valid = substitute_boolean(circuit, node.valid.local_id, replacements)
        valid = circuit.conjunction(valid, old_valid)
        if task.mask is not None:
            valid = circuit.conjunction(
                valid, self.tx.resign(task.mask, circuit.signature)
            )
        return circuit, replacements, valid

    def rewrite(self, root: _Rewrite) -> int:
        pending = [(root, False)]
        prepared: dict[
            _Rewrite,
            tuple[
                tuple[FinitePort, ...],
                int,
                tuple[_Rewrite, ...],
                tuple[FinitePort, ...],
            ],
        ] = {}
        while pending:
            task, ready = pending.pop()
            if task in self.rewrites:
                continue
            node = self.node(task.root)
            self.arena.ledger.bump("semantic_structure_rewrite_frames")
            if ready:
                inputs, valid, children, aliases = prepared[task]
                signature = FunctionSignature(inputs, node.signature.output)
                if node.kind == "product":
                    result = StructuredNode(
                        signature,
                        "product",
                        self.arena.functions._handle(valid),
                        components=tuple(
                            self.arena._handle(self.rewrites[item]) for item in children
                        ),
                    )
                else:
                    result = StructuredNode(
                        signature,
                        "function",
                        self.arena.functions._handle(valid),
                        body=self.arena._handle(self.rewrites[children[0]]),
                        bound=aliases,
                    )
                self.rewrites[task] = self.intern(result)
                continue
            circuit, replacements, valid = self._prepare_rewrite(task)
            if node.kind == "atom":
                if node.atom is None:
                    raise AssertionError("canonical atom is missing its factored value")
                atom = self.bit(node.atom.local_id)
                bits = tuple(
                    substitute_boolean(circuit, bit, replacements) for bit in atom.bits
                )
                signature = FunctionSignature(circuit.inputs, node.signature.output)
                identity = self.intern_bit(circuit.normalized(signature, bits, valid))
                self.rewrites[task] = self.intern(
                    StructuredNode(
                        signature,
                        "atom",
                        self.arena.functions._handle(valid),
                        atom=self.arena.bits._handle(identity),
                    )
                )
                continue
            if node.kind == "product":
                children = tuple(
                    _Rewrite(child.local_id, task.replacements, valid)
                    for child in node.components
                )
                aliases = ()
            else:
                if node.body is None or type(node.signature.output) is not FunctionSort:
                    raise AssertionError("canonical function is missing its typed body")
                aliases = _aliases(
                    circuit.inputs,
                    node.signature.output.inputs,
                    node.signature.output.output,
                )
                joint = _union_inputs(circuit.inputs, aliases)
                renaming = tuple(
                    (old, self.variable(joint, new))
                    for old, new in zip(node.bound, aliases)
                )
                arguments = tuple(
                    sorted(
                        (*task.replacements, *renaming),
                        key=lambda item: item[0].variable,
                    )
                )
                children = (_Rewrite(node.body.local_id, arguments, valid),)
            prepared[task] = circuit.inputs, valid, children, aliases
            pending.append((task, True))
            pending.extend((child, False) for child in children)
        return self.rewrites[root]

    def finish(self, root: int) -> StructureID:
        from number_compiler.hashlife.interfaces.semantic_structure_publication import (
            publish_structure,
        )

        return publish_structure(self, root)

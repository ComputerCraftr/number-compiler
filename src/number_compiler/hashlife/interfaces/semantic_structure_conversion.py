"""Canonical compatibility conversion into factored complete semantic outputs.

Old scalar/product-terminal functions are construction inputs only. The result
uses one joint lambda body and shared Boolean components, not a table of closed
functions indexed by outer assignments. All construction remains transient
until the caller publishes its complete set of roots atomically.
"""

from __future__ import annotations

from number_compiler.arithmetic.functions.finite_function_types import (
    AtomSort,
    FunctionSignature,
    FunctionSort,
    ProductSort,
    SemanticFunctionID,
    _union_inputs,
)
from number_compiler.hashlife.interfaces.semantic_structures import (
    StructureBuilder,
    StructuredNode,
    StructureRewrite,
    _aliases,
)
from number_compiler.resources.metric_keys import (
    hashlife_interfaces as _interfaces_keys,
)


class StructureConversion:
    def __init__(self, builder: StructureBuilder) -> None:
        self.builder = builder
        self.converted: dict[int, int] = {}
        self.choices: dict[tuple[int, int, int], int] = {}
        self.invalid: dict[FunctionSignature, int] = {}

    def _undefined(self, signature: FunctionSignature) -> int:
        builder, arena = self.builder, self.builder.arena
        pending = [(signature, False)]
        dependencies: dict[FunctionSignature, tuple[FunctionSignature, ...]] = {}
        while pending:
            current, ready = pending.pop()
            if current in self.invalid:
                continue
            circuit = builder.circuit(current.inputs)
            output = current.output
            if type(output) is AtomSort:
                atom = builder.intern_bit(
                    circuit.normalized(
                        current,
                        (circuit.zero,) * (output.cardinality - 1).bit_length(),
                        circuit.zero,
                    )
                )
                self.invalid[current] = builder.intern(
                    StructuredNode(
                        current,
                        "atom",
                        arena.functions._handle(circuit.zero),
                        atom=arena.bits._handle(atom),
                    )
                )
            elif ready:
                children = dependencies[current]
                if type(output) is ProductSort:
                    node = StructuredNode(
                        current,
                        "product",
                        arena.functions._handle(circuit.zero),
                        components=tuple(
                            arena._handle(self.invalid[item]) for item in children
                        ),
                    )
                else:
                    assert isinstance(output, FunctionSort)
                    node = StructuredNode(
                        current,
                        "function",
                        arena.functions._handle(circuit.zero),
                        body=arena._handle(self.invalid[children[0]]),
                        bound=_aliases(current.inputs, output.inputs, output.output),
                    )
                self.invalid[current] = builder.intern(node)
            else:
                if type(output) is ProductSort:
                    children = tuple(
                        FunctionSignature(current.inputs, item) for item in output.items
                    )
                else:
                    assert isinstance(output, FunctionSort)
                    children = (
                        FunctionSignature(
                            _union_inputs(
                                current.inputs,
                                _aliases(current.inputs, output.inputs, output.output),
                            ),
                            output.output,
                        ),
                    )
                dependencies[current] = children
                pending.append((current, True))
                pending.extend((child, False) for child in children)
        return self.invalid[signature]

    def _select(self, condition: int, yes: int, no: int) -> int:
        builder, arena = self.builder, self.builder.arena
        root = condition, yes, no
        pending = [(root, False)]
        dependencies: dict[tuple[int, int, int], tuple[tuple[int, int, int], ...]] = {}
        while pending:
            key, ready = pending.pop()
            if key in self.choices:
                continue
            predicate, first, second = key
            if first == second:
                self.choices[key] = first
                continue
            a, b = builder.node(first), builder.node(second)
            if a.signature != b.signature or a.kind != b.kind or a.bound != b.bound:
                raise ValueError(
                    "semantic branch structures have incompatible normalized interfaces"
                )
            circuit = builder.circuit(a.signature.inputs)
            guard = builder.tx.resign(predicate, circuit.signature)
            valid = builder.tx.choose(guard, a.valid.local_id, b.valid.local_id)
            arena.ledger.bump(_interfaces_keys.SEMANTIC_STRUCTURE_CONVERSION_CHOICES)
            if a.kind == "atom":
                assert a.atom is not None and b.atom is not None
                left, right = builder.bit(a.atom.local_id), builder.bit(b.atom.local_id)
                roots = tuple(
                    builder.tx.choose(guard, x, y)
                    for x, y in zip(left.bits, right.bits, strict=True)
                )
                atom = builder.intern_bit(circuit.normalized(a.signature, roots, valid))
                self.choices[key] = builder.intern(
                    StructuredNode(
                        a.signature,
                        "atom",
                        arena.functions._handle(valid),
                        atom=arena.bits._handle(atom),
                    )
                )
            elif ready:
                children = dependencies[key]
                if a.kind == "product":
                    node = StructuredNode(
                        a.signature,
                        "product",
                        arena.functions._handle(valid),
                        components=tuple(
                            arena._handle(self.choices[item]) for item in children
                        ),
                    )
                else:
                    node = StructuredNode(
                        a.signature,
                        "function",
                        arena.functions._handle(valid),
                        body=arena._handle(self.choices[children[0]]),
                        bound=a.bound,
                    )
                self.choices[key] = builder.intern(node)
            else:
                if a.kind == "product":
                    children = tuple(
                        (predicate, x.local_id, y.local_id)
                        for x, y in zip(a.components, b.components, strict=True)
                    )
                else:
                    assert a.body is not None and b.body is not None
                    children = ((predicate, a.body.local_id, b.body.local_id),)
                dependencies[key] = children
                pending.append((key, True))
                pending.extend((child, False) for child in children)
        return self.choices[root]

    def convert(self, reference: SemanticFunctionID) -> int:
        builder, arena = self.builder, self.builder.arena
        arena.functions.resolve(reference)
        pending = [(reference.local_id, False)]
        while pending:
            identity, ready = pending.pop()
            if identity in self.converted:
                continue
            node = builder.tx.node(identity)
            leaf = node.terminal
            arena.ledger.bump(_interfaces_keys.SEMANTIC_STRUCTURE_CONVERSION_FRAMES)
            if not ready:
                children = (node.low, node.high) if leaf is None else leaf.references
                pending.append((identity, True))
                pending.extend((child, False) for child in children)
                continue
            circuit = builder.circuit(node.signature.inputs)
            valid = circuit.admitted()
            if leaf is None:
                assert node.variable is not None
                condition = builder.tx.bit(node.signature.inputs, node.variable)
                result = self._select(
                    condition, self.converted[node.high], self.converted[node.low]
                )
            elif leaf.kind == "invalid":
                result = self._undefined(node.signature)
            elif leaf.kind == "atom":
                output = node.signature.output
                assert isinstance(output, AtomSort)
                roots = tuple(
                    circuit.one if (leaf.value >> bit) & 1 else circuit.zero
                    for bit in range((output.cardinality - 1).bit_length())
                )
                atom = builder.intern_bit(
                    circuit.normalized(node.signature, roots, valid)
                )
                result = builder.intern(
                    StructuredNode(
                        node.signature,
                        "atom",
                        arena.functions._handle(valid),
                        atom=arena.bits._handle(atom),
                    )
                )
            elif leaf.kind == "product":
                children = tuple(
                    builder.rewrite(StructureRewrite(self.converted[child], mask=valid))
                    for child in leaf.references
                )
                result = builder.intern(
                    StructuredNode(
                        node.signature,
                        "product",
                        arena.functions._handle(valid),
                        components=tuple(arena._handle(child) for child in children),
                    )
                )
            else:
                output = node.signature.output
                assert isinstance(output, FunctionSort)
                aliases = _aliases(node.signature.inputs, output.inputs, output.output)
                joint = _union_inputs(node.signature.inputs, aliases)
                replacements = tuple(
                    (old, builder.variable(joint, new))
                    for old, new in zip(output.inputs, aliases, strict=True)
                )
                body = builder.rewrite(
                    StructureRewrite(
                        self.converted[leaf.references[0]], replacements, valid
                    )
                )
                result = builder.intern(
                    StructuredNode(
                        node.signature,
                        "function",
                        arena.functions._handle(valid),
                        body=arena._handle(body),
                        bound=aliases,
                    )
                )
            self.converted[identity] = result
        return self.converted[reference.local_id]

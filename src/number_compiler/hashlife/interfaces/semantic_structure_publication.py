"""Prepare factored structured results for atomic multi-arena publication."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.hashlife.interfaces.semantic_bits import (
    FactoredFunction,
    FactoredFunctionID,
)
from number_compiler.hashlife.interfaces.semantic_publication import (
    PreparedFunctions,
    prepare_functions,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.semantic_structures import (
        StructureArena,
        StructuredNode,
        StructureID,
        _Builder,
    )


@dataclass(slots=True)
class PreparedStructures:
    arena: StructureArena
    base: int
    bit_base: int
    functions: PreparedFunctions
    bits: tuple[FactoredFunction, ...]
    nodes: tuple[StructuredNode, ...]
    roots: tuple[StructureID, ...]

    def validate_current(self) -> None:
        self.functions.validate_current()
        if (
            len(self.arena.nodes) != self.base
            or len(self.arena.bits.nodes) != self.bit_base
        ):
            raise RuntimeError("structured semantic publication was interleaved")

    def reservations(self) -> tuple[tuple[int, int, int], ...]:
        self.validate_current()
        return (
            *self.functions.reservations(),
            (self.arena.bits.node_owner, len(self.bits), len(self.bits)),
            (self.arena.bits.key_owner, len(self.bits), 0),
            (self.arena.node_owner, len(self.nodes), len(self.nodes)),
            (self.arena.key_owner, len(self.nodes), 0),
        )

    def reserve_with(self, additional: tuple[tuple[int, int, int], ...] = ()) -> None:
        """Atomically convert Boolean workspace and reserve structured outputs."""
        self.validate_current()
        self.functions.reserve_with(
            (
                (self.arena.bits.node_owner, len(self.bits), len(self.bits)),
                (self.arena.bits.key_owner, len(self.bits), 0),
                (self.arena.node_owner, len(self.nodes), len(self.nodes)),
                (self.arena.key_owner, len(self.nodes), 0),
                *additional,
            )
        )

    def cancel(self) -> None:
        """Release construction workspace when a prepared result is abandoned."""
        active = self.functions.transaction is not None
        self.functions.cancel()
        if active:
            self.bits = ()
            self.nodes = ()
            self.roots = ()

    def publish_reserved(self) -> None:
        self.validate_current()
        if not self.functions.reserved or self.functions.transaction is None:
            raise RuntimeError(
                "structured semantic publication requires an atomic reservation"
            )
        arena, ledger = self.arena, self.arena.ledger
        # Check ALL participating stores before any append. A mistaken internal
        # caller cannot partially publish Boolean nodes with an unreserved tail.
        for owner, entries, nodes in (
            (
                arena.functions.node_owner,
                self.functions.base + len(self.functions.nodes),
                self.functions.base + len(self.functions.nodes),
            ),
            (
                arena.functions.key_owner,
                len(arena.functions.keys) + len(self.functions.nodes),
                0,
            ),
            (
                arena.bits.node_owner,
                self.bit_base + len(self.bits),
                self.bit_base + len(self.bits),
            ),
            (arena.bits.key_owner, len(arena.bits.keys) + len(self.bits), 0),
            (
                arena.node_owner,
                self.base + len(self.nodes),
                self.base + len(self.nodes),
            ),
            (arena.key_owner, len(arena.keys) + len(self.nodes), 0),
        ):
            ledger.check_store_capacity(owner, entries, nodes)
        function_journal = self.functions._publish_stores()
        bit_node_base = len(arena.bits.nodes)
        structure_node_base = len(arena.nodes)
        previous_bits = tuple(
            (record, arena.bits.keys.get(record)) for record in self.bits
        )
        previous_nodes = tuple((node, arena.keys.get(node)) for node in self.nodes)
        try:
            for offset, record in enumerate(self.bits):
                arena.bits.nodes.append(record)
                arena.bits.keys[record] = self.bit_base + offset
            for offset, node in enumerate(self.nodes):
                arena.nodes.append(node)
                arena.keys[node] = self.base + offset
            self.functions._commit()
        except BaseException:
            for node, previous in reversed(previous_nodes):
                if previous is None:
                    if node in arena.keys:
                        del arena.keys[node]
                else:
                    arena.keys[node] = previous
            arena.nodes._rollback_unpublished(structure_node_base)
            for record, previous in reversed(previous_bits):
                if previous is None:
                    if record in arena.bits.keys:
                        del arena.bits.keys[record]
                else:
                    arena.bits.keys[record] = previous
            arena.bits.nodes._rollback_unpublished(bit_node_base)
            self.functions._rollback_stores(function_journal)
            raise
        ledger.bump("semantic_structure_published_nodes", len(self.nodes))
        ledger.bump("semantic_structure_factored_nodes_published", len(self.bits))


def prepare_structures(builder: _Builder, roots: tuple[int, ...]) -> PreparedStructures:
    """Reduce reachable roots in charged workspace without retaining nodes."""
    from number_compiler.hashlife.interfaces.semantic_structures import StructuredNode

    arena = builder.arena
    if len(arena.nodes) != builder.base or len(arena.bits.nodes) != builder.bit_base:
        raise RuntimeError("structured semantic publication was interleaved")
    if type(roots) is not tuple or any(
        type(root) is not int or not 0 <= root < builder.base + len(builder.nodes)
        for root in roots
    ):
        raise ValueError("structured publication roots require local construction IDs")
    structure_count = len(builder.nodes)
    bit_count = len(builder.bits)
    structure_edges = sum(
        len(node.components) + int(node.body is not None) + int(node.atom is not None)
        for node in builder.nodes
    )
    semantic_references = sum(len(value.bits) + 1 for value in builder.bits)
    traversal_entries = structure_count + structure_edges + len(roots)
    publication_entries = (
        semantic_references + 3 * bit_count + 3 * structure_count + len(roots)
    )
    builder.tx.reserve_workspace(
        entries=max(traversal_entries, publication_entries),
        nodes=structure_count + bit_count,
    )
    structures: set[int] = set()
    bits: set[int] = set()
    semantic: set[int] = set()
    pending = list(roots)
    while pending:
        current = pending.pop()
        if current < builder.base or current in structures:
            continue
        structures.add(current)
        node = builder.node(current)
        semantic.add(node.valid.local_id)
        pending.extend(child.local_id for child in node.components)
        if node.body is not None:
            pending.append(node.body.local_id)
        if node.atom is not None and node.atom.local_id >= builder.bit_base:
            identity = node.atom.local_id
            bits.add(identity)
            value = builder.bit(identity)
            semantic.update((*value.bits, value.valid))
    semantic_roots = tuple(sorted(semantic))
    prepared = prepare_functions(builder.tx, semantic_roots)
    semantic_ids = dict(zip(semantic_roots, prepared.roots))
    bit_ids: dict[int, FactoredFunctionID] = {}
    fresh_bits: dict[FactoredFunction, int] = {}
    for identity in sorted(bits):
        value = builder.bit(identity)
        record = FactoredFunction(
            value.signature,
            tuple(semantic_ids[item] for item in value.bits),
            semantic_ids[value.valid],
        )
        found = arena.bits.keys.get(record)
        if found is None:
            found = fresh_bits.get(record)
        if found is None:
            found = builder.bit_base + len(fresh_bits)
            fresh_bits[record] = found
        bit_ids[identity] = arena.bits._handle(found)
    structure_ids: dict[int, StructureID] = {}
    fresh_structures: dict[StructuredNode, int] = {}
    for identity in sorted(structures):
        node = builder.node(identity)
        atom = None if node.atom is None else bit_ids.get(node.atom.local_id, node.atom)
        body = (
            None
            if node.body is None
            else structure_ids.get(node.body.local_id, node.body)
        )
        children = tuple(
            structure_ids.get(child.local_id, child) for child in node.components
        )
        structure = StructuredNode(
            node.signature,
            node.kind,
            semantic_ids[node.valid.local_id],
            atom,
            children,
            body,
            node.bound,
        )
        found = arena.keys.get(structure)
        if found is None:
            found = fresh_structures.get(structure)
        if found is None:
            found = builder.base + len(fresh_structures)
            fresh_structures[structure] = found
        structure_ids[identity] = arena._handle(found)
    return PreparedStructures(
        arena,
        builder.base,
        builder.bit_base,
        prepared,
        tuple(fresh_bits),
        tuple(fresh_structures),
        tuple(structure_ids.get(root, arena._handle(root)) for root in roots),
    )


def publish_structure(builder: _Builder, root: int) -> StructureID:
    prepared = None
    try:
        prepared = prepare_structures(builder, (root,))
        prepared.reserve_with()
        prepared.publish_reserved()
        return prepared.roots[0]
    finally:
        if prepared is None:
            builder.tx.close()
        else:
            prepared.cancel()

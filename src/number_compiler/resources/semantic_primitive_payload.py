"""Primitive macro inventory: ownership, contract, and original geometry only.

This is not an independent functional source-to-quotient equivalence proof.
That claim is tested by the producer's differential and algebraic tests.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import _effect_key
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.fields.dyadic_tile import DyadicTile
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.actions.diamond_actions import CellID, CellNode
from number_compiler.hashlife.interfaces.diamond_quotient import DiamondQuotientID
from number_compiler.hashlife.interfaces.semantic_primitive_macro import (
    CONTRACT,
    PrimitiveMacroArena,
    PrimitiveMacroBinding,
)
from number_compiler.hashlife.interfaces.semantic_primitive_tasks import (
    PrimitiveMacroKey,
    PrimitiveMacroObservation,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_containers import audit_mapping_items
from number_compiler.resources.stores import LedgerDict

if TYPE_CHECKING:
    from number_compiler.resources.semantic_payload import SemanticPayloadRegistry


class PrimitiveMacroPayloadRegistry:
    record_types = (PrimitiveMacroKey, PrimitiveMacroBinding, PrimitiveMacroObservation)

    def __init__(
        self, ledger: ResourceLedger, semantic: SemanticPayloadRegistry
    ) -> None:
        self.semantic = semantic
        self.valid_objects: set[int] = set()
        self.invalid_bindings: set[tuple[int, int]] = set()
        actual = dict(ledger.iter_containers())
        self.arenas = tuple(
            root
            for root in ledger.iter_execution_roots()
            if type(root) is PrimitiveMacroArena
            and root.ledger is ledger
            and root.runtime.ledger is ledger
            and root.runtime.primitive_macros is root
            and root.runtime.semantic_quotients is root.quotients
            and root.quotients in semantic.quotients
            and root.cells is root.runtime.cells
            and root.kernels is root.runtime.kernels
            and root.structures in semantic.structures
            and root.structures is root.quotients.structures
            and root.bits is root.structures.bits
            and root.primitives in semantic.primitives
            and type(root.bindings._data) is LedgerDict
            and actual.get(root.bindings.owner) is root.bindings._data
            and ledger.is_factory_container(root.bindings._data)
        )

    def audit(self) -> None:
        for arena in self.arenas:
            for key, value in audit_mapping_items(arena.bindings._data):
                try:
                    accepted = self._binding(arena, key, value)
                except (ValueError, TypeError, AttributeError, IndexError, KeyError):
                    accepted = False
                if accepted:
                    self.valid_objects.update((id(key), id(value)))
                else:
                    self.invalid_bindings.update(
                        (
                            (arena.bindings.owner, id(key)),
                            (arena.bindings.owner, id(value)),
                        )
                    )

    def contract(self, value: object) -> bool:
        if type(value) is not SemanticIdentity:
            return False
        try:
            value.validate()
            behavior = value.behavior
            if (
                len(behavior) != 3
                or behavior[0] != CONTRACT
                or type(behavior[2]) is not int
                or not 1 <= behavior[2] <= 1 << 62
                or behavior[2] & (behavior[2] - 1)
            ):
                return False
            return any(
                behavior[1] == _effect_key(kernel.effect)
                for arena in self.arenas
                for kernel in arena.kernels._kernels
            )
        except (ValueError, TypeError, AttributeError):
            return False

    def _binding(self, arena: PrimitiveMacroArena, key: object, value: object) -> bool:
        if (
            type(key) is not PrimitiveMacroKey
            or type(key.kernel) is not ActionProgramID
            or key.kernel.owner is not arena.kernels.owner
            or key.kernel.kind != "diamond-kernel"
            or not self.semantic.kernel_handle(key.kernel)
            or type(key.source) is not CellID
            or key.source.owner is not arena.cells.token
            or not self.semantic.kernel_handle(key.source)
            or type(value) is not PrimitiveMacroBinding
            or type(value.original_extent) is not int
            or type(value.quotient) is not DiamondQuotientID
            or value.quotient.owner is not arena.quotients.owner
        ):
            return False
        kernel = arena.kernels._kernels[key.kernel.local_id]
        source = arena.cells.source_geometry._construction.source
        if (kernel.base, kernel.blank) != (source.base, source.blank):
            return False
        node = arena.cells._nodes[key.source.local_id]
        if (
            not 0 <= node.level < 63
            or _source_extent(arena, key.source.local_id) != value.original_extent
        ):
            return False
        quotient = arena.quotients.resolve(value.quotient)
        if not self.semantic._quotient_record(quotient):
            return False
        interface = arena.quotients.interface(quotient.signature)
        behavior = (CONTRACT, _effect_key(kernel.effect), node.width)
        expected_ports = tuple(
            sorted(
                (
                    FinitePort(PortVariable(0, 0, "macro-left", 0), kernel.left_count),
                    FinitePort(
                        PortVariable(0, 1, "macro-right", 0), kernel.right_count
                    ),
                    FinitePort(PortVariable(0, 0, "macro-coordinate", 0), node.width),
                ),
                key=lambda p: p.variable,
            )
        )
        # Sort names come from the actual primitive semantic adapter, not a
        # copied textual label. The existing registry audits that record too.
        laws = arena.primitives.records.get(key.kernel)
        if laws is None:
            return False
        symbol = laws.symbol_sort
        position = AtomSort("cell-active-position", node.width + 1)
        extent = AtomSort("cell-active-extent", node.width + 1)
        outputs = (
            laws.left_sort,
            laws.right_sort,
            symbol,
            BOOL,
            position,
            position,
            extent,
            symbol,
            symbol,
            AtomSort("cell-growth-biased-by-width", 2 * node.width + 1),
            BOOL,
            symbol,
            AtomSort("cell-coordinate", node.width),
        )
        return (
            interface.kernel.behavior == behavior
            and self.contract(interface.kernel)
            and interface.inputs == expected_ports
            and interface.outputs == outputs
            and interface.phase_count == 1
        )


def _source_extent(arena: PrimitiveMacroArena, root: int) -> int | None:
    """Original source/join DAG only; never call a source or future observer."""
    nodes = arena.cells._nodes
    source_tiles = {
        tile.node_id: tile
        for _, tile in audit_mapping_items(arena.cells.source_geometry.nodes)
    }
    pending = [(root, False)]
    extents: dict[int, int] = {}
    tiles: dict[int, int] = {}
    while pending:
        identity, ready = pending.pop()
        if identity in extents:
            continue
        if not 0 <= identity < len(nodes):
            return None
        node = nodes[identity]
        if type(node) is not CellNode or node.original_forward is not True:
            return None
        CellNode.__post_init__(node)
        if node.kind == "source":
            tile = source_tiles.get(node.source_tile)
            if type(tile) is not DyadicTile or tile.level != node.level:
                return None
            extent = _tile_extent(
                tile, arena.cells.source_geometry._construction.source.blank, tiles
            )
            if extent is None:
                return None
            extents[identity] = extent
        elif (
            node.kind == "join"
            and 0 <= node.left < identity
            and 0 <= node.right < identity
            and nodes[node.left].level == nodes[node.right].level == node.level - 1
        ):
            if ready:
                right = extents[node.right]
                extents[identity] = (
                    (1 << (node.level - 1)) + right if right else extents[node.left]
                )
            else:
                pending.extend(
                    ((identity, True), (node.right, False), (node.left, False))
                )
        else:
            return None
    return extents[root]


def _tile_extent(root: DyadicTile, blank: int, extents: dict[int, int]) -> int | None:
    pending = [(root, False)]
    active: set[int] = set()
    while pending:
        tile, ready = pending.pop()
        if id(tile) in extents:
            continue
        if type(tile.level) is not int or tile.level < 0:
            return None
        if not tile.level:
            if type(tile.symbol) is not int or not 0 <= tile.symbol <= blank:
                return None
            extents[id(tile)] = int(tile.symbol != blank)
        elif (
            type(tile.left) is DyadicTile
            and type(tile.right) is DyadicTile
            and tile.left.level == tile.right.level == tile.level - 1
        ):
            if ready:
                active.remove(id(tile))
                right = extents[id(tile.right)]
                extents[id(tile)] = (
                    (1 << (tile.level - 1)) + right if right else extents[id(tile.left)]
                )
            else:
                if id(tile) in active:
                    return None
                active.add(id(tile))
                pending.extend(((tile, True), (tile.right, False), (tile.left, False)))
        else:
            return None
    return extents[id(root)]

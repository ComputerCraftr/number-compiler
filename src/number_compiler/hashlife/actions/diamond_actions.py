"""Canonical temporal syntax and parametric spatial images, without future tapes.

An image is an unevaluated complete action on a cell. Splitting an image makes
views of that image; it does not apply the action to isolated children with
incorrect boundary conditions. Execution and port substitution belong to the
diamond scheduler.
"""

from __future__ import annotations

from collections.abc import MutableMapping, MutableSequence
from dataclasses import dataclass, replace
from typing import TYPE_CHECKING, Literal, TypeAlias

from number_compiler.arithmetic.contracts.block_effect import BlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaHandle,
    ArenaToken,
)
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.hashlife.actions.lazy_compiler import (
    LazyCompiler,
    ProgramComposition,
)
from number_compiler.resources.metric_keys import (
    hashlife_actions as _actions_keys,
)
from number_compiler.resources.metric_keys import shared as _shared_keys
from number_compiler.resources.stores import append_indexed_node

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena


@dataclass(frozen=True, slots=True)
class CellID(ArenaHandle):
    """A scoped original-source cell or unevaluated spatial image."""


@dataclass(frozen=True, slots=True)
class FormalSymbolID(ArenaHandle):
    """One cofactor of the free ORIGINAL kernel-alphabet parameter.

    The ordinal names an alternative input symbol, never a computed midpoint.
    Its complete finite domain exists implicitly; no source or image tile is
    allocated. Output-function compilation must keep all these alternatives
    until the full function is canonical, before selecting the actual input.
    """


InputCellID: TypeAlias = CellID | FormalSymbolID


@dataclass(frozen=True, slots=True)
class PortProgramID(ArenaHandle):
    """A scoped executable port expression owned by the scheduler."""


@dataclass(frozen=True, slots=True)
class PortSignatureID(ArenaHandle):
    """A scoped signature reference; composed domains are never multiplied."""


@dataclass(frozen=True, slots=True)
class PortSignature:
    base: int
    alphabet_size: int
    left_domain: int | None
    right_domain: int | None
    halo_left: int = 0
    halo_right: int = 0
    first: PortSignatureID | None = None
    second: PortSignatureID | None = None
    horizon: int | None = None
    kernel: ActionProgramID | None = None
    left_role: Literal["left-boundary"] = "left-boundary"
    right_role: Literal["right-boundary"] = "right-boundary"

    def __post_init__(self) -> None:
        if (
            type(self.base) is not int
            or self.base < 2
            or type(self.alphabet_size) is not int
            or self.alphabet_size < 1
        ):
            raise ValueError("invalid port alphabet")
        if any(
            size is not None and (type(size) is not int or size < 1)
            for size in (self.left_domain, self.right_domain)
        ):
            raise ValueError("port domains are positive finite sizes or symbolic")
        if any(
            type(size) is not int or size < 0
            for size in (self.halo_left, self.halo_right)
        ):
            raise ValueError("halo extents must be nonnegative integers")
        if (self.first is None) != (self.second is None):
            raise ValueError("a composed interface needs both child signatures")
        if self.first is not None and self.second is not None:
            if (
                type(self.first) is not PortSignatureID
                or type(self.second) is not PortSignatureID
                or self.first.kind != "diamond-port-signature"
                or self.second.kind != "diamond-port-signature"
                or self.first.owner is not self.second.owner
            ):
                raise ValueError(
                    "composed interface children require one signature arena"
                )
            if self.left_domain is not None or self.right_domain is not None:
                raise ValueError(
                    "composed interfaces retain child references, not product domains"
                )
        if self.horizon is not None and (
            type(self.horizon) is not int or self.horizon < 0
        ):
            raise ValueError("invalid optional horizon")
        if self.left_role != "left-boundary" or self.right_role != "right-boundary":
            raise ValueError("port roles must preserve their boundary direction")
        if self.kernel is not None:
            if (
                type(self.kernel) is not ActionProgramID
                or self.kernel.kind != "diamond-kernel"
            ):
                raise ValueError(
                    "primitive signatures require a scoped kernel identity"
                )
            if (
                self.first is not None
                or self.left_domain is None
                or self.right_domain is None
            ):
                raise ValueError(
                    "a primitive kernel signature needs complete finite domains"
                )

    @property
    def admissibility(self) -> Literal["unbound", "primitive", "composed"]:
        """A record's shape is not by itself a proof of kernel admission."""
        return (
            "primitive"
            if self.kernel is not None
            else "composed"
            if self.first is not None
            else "unbound"
        )

    def validate_kernel(self, arena: DiamondKernelArena) -> None:
        """Check the actual immutable kernel before using a primitive signature."""
        if self.kernel is None:
            raise ValueError("signature is not bound to a primitive kernel")
        primitive = arena.kernel(self.kernel)
        if (self.base, self.alphabet_size, self.left_domain, self.right_domain) != (
            primitive.base,
            primitive.blank + 1,
            primitive.left_count,
            primitive.right_count,
        ):
            raise ValueError("port signature does not describe its kernel")


@dataclass(frozen=True, slots=True)
class BoundedCellAction:
    """Slots for a complete effect; the scheduler must admit each program role.

    These references do not prove extensional equivalence or output completeness
    merely by existing. Their execution contracts must be validated by the
    owning scheduler before interning an executable bounded action.
    """

    signature: PortSignature
    boundary_left: PortProgramID
    boundary_right: PortProgramID
    output: PortProgramID
    activity: PortProgramID
    extent: PortProgramID
    halo: PortProgramID

    def __post_init__(self) -> None:
        if type(self.signature) is not PortSignature:
            raise TypeError("cell actions require a port signature")
        references = (
            self.boundary_left,
            self.boundary_right,
            self.output,
            self.activity,
            self.extent,
            self.halo,
        )
        if any(type(reference) is not PortProgramID for reference in references):
            raise TypeError("cell action fields must be executable port-program IDs")
        owner = self.boundary_left.owner
        if any(
            reference.owner is not owner or reference.kind != "diamond-port-program"
            for reference in references
        ):
            raise ValueError("cell action programs must belong to one port arena")


@dataclass(frozen=True, slots=True)
class TemporalActionNode:
    kind: Literal["identity", "atom", "compose"]
    left: int = -1
    right: int = -1
    compiler_id: int = -1
    base: int = 0
    blank: int = 0
    exponent: int = 0

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (
                self.left,
                self.right,
                self.compiler_id,
                self.base,
                self.blank,
                self.exponent,
            )
        ):
            raise ValueError("temporal node metadata must be integers")
        if self.kind == "identity":
            if (
                self.left,
                self.right,
                self.compiler_id,
                self.base,
                self.blank,
                self.exponent,
            ) != (-1, -1, -1, 0, 0, 0):
                raise ValueError(
                    "identity has no primitive, children, or alphabet payload"
                )
            return
        if self.base < 2 or self.blank < 1 or self.exponent < 0:
            raise ValueError("invalid temporal action metadata")
        if self.kind == "atom":
            valid = self.compiler_id >= 0 and self.left == self.right == -1
        elif self.kind == "compose":
            valid = self.left >= 0 and self.right >= 0 and self.compiler_id == -1
        else:
            valid = False
        if not valid:
            raise ValueError("invalid temporal action constructor")

    @property
    def first(self) -> int:
        return self.left

    @property
    def second(self) -> int:
        return self.right


class TemporalActionArena:
    """Read-only compiler import plus canonical binary composition of actions.

    The real identity has ID zero. Importing compiler syntax stages all new
    nodes before a single reservation, so a failed import publishes no prefix.
    No source-specific schedule or boundary universe is constructed.
    """

    def __init__(self, compiler: LazyCompiler) -> None:
        self.compiler, self.ledger = compiler, compiler.ledger
        self.token = ArenaToken("diamond-temporal")
        self.ledger.register_execution_root(self)
        prefix = f"diamond-temporal-{len(self.ledger.inventory())}"
        self._node_owner = self.ledger.register(prefix + "-nodes", "temporal_action")
        self._index_owner = self.ledger.register(
            prefix + "-interner", "action_interner"
        )
        self._nodes: MutableSequence[TemporalActionNode] = self.ledger.make_list(
            self._node_owner
        )
        self._ids: MutableMapping[TemporalActionNode, int] = self.ledger.make_dict(
            self._index_owner
        )
        self.identity = self._intern(TemporalActionNode("identity"))

    def _handle(self, index: int) -> ActionProgramID:
        return ActionProgramID(self.token, "diamond-action", index)

    def resolve(self, action: ActionProgramID) -> TemporalActionNode:
        if type(action) is not ActionProgramID:
            raise TypeError("expected a temporal action ID")
        action.validate(self.token, "diamond-action", size=len(self._nodes))
        return self._nodes[action.local_id]

    def node(self, action: ActionProgramID) -> TemporalActionNode:
        return self.resolve(action)

    def intern(self, effect: BlockEffect) -> ActionProgramID:
        """Import an already admitted compiler definition without mutating it.

        External definitions must first use the compiler's atomic admission API;
        keeping that stage explicit prevents a cell/action budget failure from
        silently publishing a new compiler DAG.
        """
        return self.from_compiler(self.compiler.reference(effect))

    def reference(self, index: int) -> ActionProgramID:
        handle = self._handle(index)
        self.resolve(handle)
        return handle

    def primitive_reference(self, action: ActionProgramID) -> ActionProgramID:
        return self._primitive_binding(action)[0]

    def _primitive_binding(
        self, action: ActionProgramID
    ) -> tuple[ActionProgramID, BlockEffect]:
        """Resolve both ownership boundaries once for a primitive lookup."""
        node = self.resolve(action)
        if node.kind != "atom":
            raise ValueError("temporal action is not a primitive")
        handle = ActionProgramID(
            self.compiler.token, "action-program", node.compiler_id
        )
        return handle, self.compiler.resolve(handle)

    def _intern(self, node: TemporalActionNode) -> ActionProgramID:
        found = self._ids.get(node)
        if found is not None:
            return self._handle(found)
        index = append_indexed_node(
            self.ledger,
            self._nodes,
            self._ids,
            self._node_owner,
            self._index_owner,
            node,
            node,
        )
        return self._handle(index)

    def from_compiler(self, reference: ActionProgramID) -> ActionProgramID:
        root = self.compiler.resolve(reference)
        staged: dict[TemporalActionNode, int] = {}
        nodes: list[TemporalActionNode] = []
        resolved: dict[int, int] = {}
        pending = [(root, False)]
        visits = 0
        while pending:
            effect, ready = pending.pop()
            visits += 1
            compiler_id = self.compiler.reference(effect).local_id
            if compiler_id in resolved:
                continue
            if type(effect) is ProgramComposition and isinstance(
                effect, ProgramComposition
            ):
                if not ready:
                    pending.extend(
                        ((effect, True), (effect.second, False), (effect.first, False))
                    )
                    continue
                node = TemporalActionNode(
                    "compose",
                    resolved[self.compiler.reference(effect.first).local_id],
                    resolved[self.compiler.reference(effect.second).local_id],
                    base=effect.base,
                    blank=effect.blank,
                    exponent=effect.exponent,
                )
            else:
                node = TemporalActionNode(
                    "atom",
                    compiler_id=compiler_id,
                    base=effect.base,
                    blank=effect.blank,
                    exponent=effect.exponent,
                )
            index = self._ids.get(node)
            if index is None:
                index = staged.get(node)
            if index is None:
                index = len(self._nodes) + len(nodes)
                staged[node] = index
                nodes.append(node)
            resolved[compiler_id] = index
        count = len(nodes)
        self.ledger.reserve_many(
            ((self._node_owner, count, count), (self._index_owner, count, 0))
        )
        for node in nodes:
            self._ids[node] = len(self._nodes)
            self._nodes.append(node)
        self.ledger.bump(_actions_keys.DIAMOND_TEMPORAL_IMPORT_VISITS, visits)
        return self._handle(resolved[reference.local_id])

    def primitive(self, action: ActionProgramID) -> BlockEffect:
        return self._primitive_binding(action)[1]

    def compose(
        self, before: ActionProgramID, after: ActionProgramID
    ) -> ActionProgramID:
        result, node = self._plan_compose(before, after)
        if node is not None:
            result = self._intern(node)
        self.ledger.bump(_shared_keys.DIAMOND_TEMPORAL_COMPOSITION_REQUESTS)
        self.ledger.bump(
            _shared_keys.DIAMOND_TEMPORAL_COMPOSITION_HITS
            if node is None
            else _shared_keys.DIAMOND_TEMPORAL_COMPOSITION_EVALUATIONS
        )
        return result

    def _plan_compose(
        self, before: ActionProgramID, after: ActionProgramID
    ) -> tuple[ActionProgramID, TemporalActionNode | None]:
        """Resolve a canonical composition without publishing or reserving it."""
        first, second = self.resolve(before), self.resolve(after)
        if first.kind == "identity" or second.kind == "identity":
            return (after if first.kind == "identity" else before), None
        if first.base != second.base or first.blank != second.blank:
            raise ValueError("temporal actions have incompatible alphabets")
        node = TemporalActionNode(
            "compose",
            before.local_id,
            after.local_id,
            base=first.base,
            blank=first.blank,
            exponent=first.exponent + second.exponent,
        )
        found = self._ids.get(node)
        return (
            (self._handle(len(self._nodes)), node)
            if found is None
            else (self._handle(found), None)
        )

    def power(self, action: ActionProgramID, exponent: int) -> ActionProgramID:
        self.resolve(action)
        if type(exponent) is not int or exponent < 0:
            raise ValueError("power requires a nonnegative integer exponent")
        result, factor = self.identity, action
        while exponent:
            if exponent & 1:
                # Powers of the same action commute. The largest prefix stays
                # adjacent to the original source rather than an image thunk.
                result = self.compose(factor, result)
            exponent >>= 1
            if exponent:
                factor = self.compose(factor, factor)
        return result


@dataclass(frozen=True, slots=True)
class CellNode:
    kind: Literal["source", "image", "slice", "join", "mirror"]
    level: int
    left: int = -1
    right: int = -1
    action: int = -1
    offset: int = 0
    source_tile: int = -1
    source_start: int = 0
    original_forward: bool = False

    def __post_init__(self) -> None:
        if type(self.kind) is not str:
            raise ValueError("spatial cell kind must be an exact string")
        if type(self.original_forward) is not bool:
            raise ValueError("original-source metadata must be a Boolean")
        if any(
            type(value) is not int
            for value in (
                self.level,
                self.left,
                self.right,
                self.action,
                self.offset,
                self.source_tile,
                self.source_start,
            )
        ):
            raise ValueError("cell geometry and child identities must be integers")
        if self.level < 0 or self.offset < 0 or self.source_start < 0:
            raise ValueError("negative cell geometry")
        if self.kind == "source":
            valid = (
                self.source_tile >= 0
                and self.left == self.right == self.action == -1
                and self.offset == 0
            )
        else:
            valid = self.source_tile == -1 and self.source_start == 0 and self.left >= 0
            if self.kind == "image":
                valid = (
                    valid and self.action >= 0 and self.right == -1 and self.offset == 0
                )
            elif self.kind == "join":
                valid = (
                    valid and self.right >= 0 and self.action == -1 and self.offset == 0
                )
            elif self.kind in ("slice", "mirror"):
                valid = (
                    valid
                    and self.right == self.action == -1
                    and (self.kind == "slice" or self.offset == 0)
                )
            else:
                valid = False
        if not valid:
            raise ValueError("invalid spatial cell constructor")

    @property
    def width(self) -> int:
        return 1 << self.level


@dataclass(frozen=True, slots=True)
class _CellKey:
    kind: str
    level: int
    left: int
    right: int
    action: int
    offset: int
    source_tile: int


class ImageCellArena:
    """Canonical original cells and parametric images on a fixed padded grid."""

    def __init__(
        self, actions: TemporalActionArena, source_geometry: SourceGeometry
    ) -> None:
        if source_geometry.ledger is not actions.ledger:
            raise ValueError("spatial and temporal arenas require the same ledger")
        self.actions, self.source_geometry = actions, source_geometry
        self.ledger = actions.ledger
        self.token = ArenaToken("diamond-cells")
        self.formal_token = ArenaToken("diamond-original-symbols")
        self.ledger.register_execution_root(self)
        prefix = f"diamond-cells-{len(self.ledger.inventory())}"
        self._node_owner = self.ledger.register(prefix + "-nodes", "diamond_cell")
        self._index_owner = self.ledger.register(prefix + "-interner", "image_interner")
        self._nodes: MutableSequence[CellNode] = self.ledger.make_list(self._node_owner)
        self._ids: MutableMapping[_CellKey, int] = self.ledger.make_dict(
            self._index_owner
        )

    def _handle(self, index: int) -> CellID:
        return CellID(self.token, "diamond-cell", index)

    def resolve(self, cell: CellID) -> CellNode:
        if type(cell) is not CellID:
            raise TypeError("expected a spatial cell ID")
        cell.validate(self.token, "diamond-cell", size=len(self._nodes))
        return self._nodes[cell.local_id]

    def node(self, cell: CellID) -> CellNode:
        return self.resolve(cell)

    def require_original(self, cell: CellID) -> CellNode:
        """Check one scoped immutable source-closure proof, without a DAG walk.

        Only source nodes and forward joins of such nodes acquire this flag.
        Images and reflected views cannot acquire it from their children.
        """
        node = self.resolve(cell)
        if node.original_forward is not True:
            raise ValueError(
                "operation requires original source geometry in forward orientation"
            )
        return node

    def formal_symbol(self, index: int) -> FormalSymbolID:
        """Reference an implicit kernel constant, without allocating geometry."""
        result = FormalSymbolID(self.formal_token, "diamond-formal-symbol", index)
        self.validate_input(result)
        return result

    def validate_input(self, cell: InputCellID) -> InputCellID:
        if type(cell) is FormalSymbolID:
            blank = self.source_geometry._construction.source.blank
            cell.validate(self.formal_token, "diamond-formal-symbol", size=blank + 1)
        elif type(cell) is CellID:
            self.resolve(cell)
        else:
            raise TypeError("expected a spatial cell or formal original symbol")
        return cell

    def input_level(self, cell: InputCellID) -> int:
        self.validate_input(cell)
        return 0 if isinstance(cell, FormalSymbolID) else self.resolve(cell).level

    def input_symbol(self, cell: InputCellID) -> int:
        self.validate_input(cell)
        return (
            cell.local_id
            if isinstance(cell, FormalSymbolID)
            else self.source_symbol(cell)
        )

    def source_symbol(self, cell: CellID) -> int:
        node = self.resolve(cell)
        if node.kind != "source" or node.level != 0:
            raise ValueError("only original-source leaves contain symbols")
        return self.source_geometry.read(node.source_start)

    def _intern(self, node: CellNode) -> CellID:
        original = node.kind == "source"
        if node.kind == "join":
            original = (
                self.resolve(self._handle(node.left)).original_forward
                and self.resolve(self._handle(node.right)).original_forward
            )
        # Metadata is derived from allocated children, never caller authority.
        node = replace(node, original_forward=original)
        key = self._key(node)
        found = self._ids.get(key)
        if found is not None:
            self.ledger.bump(_actions_keys.DIAMOND_CELL_INTERNER_HITS)
            self.ledger.bump(
                _actions_keys.DIAMOND_SOURCE_ORIGIN_METADATA_READS,
                2 if node.kind == "join" else 0,
            )
            return self._handle(found)
        index = append_indexed_node(
            self.ledger,
            self._nodes,
            self._ids,
            self._node_owner,
            self._index_owner,
            key,
            node,
        )
        self.ledger.bump(_actions_keys.DIAMOND_CELL_INTERNER_EVALUATIONS)
        self.ledger.bump(
            _actions_keys.DIAMOND_SOURCE_ORIGIN_METADATA_READS,
            2 if node.kind == "join" else 0,
        )
        return self._handle(index)

    @staticmethod
    def _key(node: CellNode) -> _CellKey:
        return _CellKey(
            node.kind,
            node.level,
            node.left,
            node.right,
            node.action,
            node.offset,
            node.source_tile,
        )

    def source(self, start: int, level: int) -> CellID:
        tile = self.source_geometry.tile_at(start, level)
        if tile is None:
            raise ValueError(
                "requested cell is not an existing original-source subtree"
            )
        return self._intern(
            CellNode("source", level, source_tile=tile.node_id, source_start=start)
        )

    def source_span(self, start: int, length: int) -> tuple[tuple[int, CellID], ...]:
        """Existing original-source forest for a padded logical interval."""
        if type(start) is not int or type(length) is not int or start < 0 or length < 0:
            raise ValueError("invalid original-source interval")
        root = self.source_geometry._read_root
        if root is None or start < root.start or start + length > root.end:
            raise ValueError(
                "interval lies outside initialized original-source geometry"
            )
        result: list[tuple[int, CellID]] = []
        stop = start + length
        while start < stop:
            level = (stop - start).bit_length() - 1
            if start:
                level = min(level, (start & -start).bit_length() - 1)
            result.append((start, self.source(start, level)))
            start += 1 << level
        self.ledger.bump(_actions_keys.DIAMOND_SOURCE_FOREST_REQUESTS)
        self.ledger.bump(_actions_keys.DIAMOND_SOURCE_FOREST_CHUNKS, len(result))
        peak = self.ledger.counters.get(
            _actions_keys.DIAMOND_SOURCE_FOREST_PEAK_CHUNKS, 0
        )
        self.ledger.bump(
            _actions_keys.DIAMOND_SOURCE_FOREST_PEAK_CHUNKS,
            max(0, len(result) - peak),
        )
        return tuple(result)

    def source_forest(self) -> tuple[CellID, ...]:
        root = self.source_geometry._read_root
        if root is None:
            raise ValueError("original-source geometry is not initialized")
        return tuple(cell for _, cell in self.source_span(root.start, root.length))

    def reference(self, index: int) -> CellID:
        handle = self._handle(index)
        self.resolve(handle)
        return handle

    def image(self, action: ActionProgramID, cell: CellID) -> CellID:
        temporal, node = self.actions.resolve(action), self.resolve(cell)
        if temporal.kind == "identity":
            return cell
        original = self.source_geometry._construction.source
        if temporal.base != original.base or temporal.blank != original.blank:
            raise ValueError(
                "image action and source geometry have incompatible alphabets"
            )
        # Function composition is normalized before the image interner is read.
        # No intermediate image or per-generation application is published.
        nested = node.kind == "image"
        staged: TemporalActionNode | None = None
        if nested:
            action, staged = self.actions._plan_compose(
                self.actions._handle(node.action), action
            )
            cell = self._handle(node.left)
            node = self.resolve(cell)
            if node.kind == "image":
                raise AssertionError(
                    "image interner retained an unnormalized application"
                )
        image_node = CellNode(
            "image", node.level, left=cell.local_id, action=action.local_id
        )
        key = self._key(image_node)
        found = self._ids.get(key)
        if found is not None:
            if staged is not None:
                raise AssertionError("image references an unpublished temporal action")
            result = self._handle(found)
            self.ledger.bump(_actions_keys.DIAMOND_CELL_INTERNER_HITS)
        else:
            reservations = [(self._node_owner, 1, 1), (self._index_owner, 1, 0)]
            if staged is not None:
                reservations.extend(
                    (
                        (self.actions._node_owner, 1, 1),
                        (self.actions._index_owner, 1, 0),
                    )
                )
            self.ledger.reserve_many(tuple(reservations))
            if staged is not None:
                self.actions._ids[staged] = len(self.actions._nodes)
                self.actions._nodes.append(staged)
            result = self._handle(len(self._nodes))
            self._ids[key] = result.local_id
            self._nodes.append(image_node)
            self.ledger.bump(_actions_keys.DIAMOND_CELL_INTERNER_EVALUATIONS)
        if nested:
            self.ledger.bump(_shared_keys.DIAMOND_TEMPORAL_COMPOSITION_REQUESTS)
            self.ledger.bump(
                _shared_keys.DIAMOND_TEMPORAL_COMPOSITION_HITS
                if staged is None
                else _shared_keys.DIAMOND_TEMPORAL_COMPOSITION_EVALUATIONS
            )
        self.ledger.bump(_shared_keys.DIAMOND_IMAGE_NORMALIZED_REQUESTS)
        return result

    def slice(self, cell: CellID, offset: int, level: int) -> CellID:
        node = self.resolve(cell)
        if (
            type(offset) is not int
            or type(level) is not int
            or offset < 0
            or level < 0
            or level > node.level
        ):
            raise ValueError("invalid cell slice geometry")
        width = 1 << level
        if offset % width or offset + width > 1 << node.level:
            raise ValueError("cell slice must be aligned and contained")
        if level == node.level:
            self.ledger.bump(_actions_keys.DIAMOND_SLICE_REQUESTS)
            return cell
        visits = 0
        reflected = False
        while node.kind in ("slice", "join", "mirror"):
            visits += 1
            if node.kind == "mirror":
                # Reflection changes the slice origin and preserves the
                # reflected orientation of the selected result. It does not
                # commute a nonlinear action through an image program.
                offset = (1 << node.level) - offset - width
                reflected = not reflected
                cell = self._handle(node.left)
            elif node.kind == "slice":
                offset += node.offset
                cell = self._handle(node.left)
            else:
                middle = 1 << (node.level - 1)
                if offset >= middle:
                    offset -= middle
                    cell = self._handle(node.right)
                else:
                    cell = self._handle(node.left)
            node = self.resolve(cell)
            if node.level == level:
                self.ledger.bump(_actions_keys.DIAMOND_SLICE_REQUESTS)
                self.ledger.bump(
                    _actions_keys.DIAMOND_SLICE_NORMALIZATION_VISITS, visits
                )
                return self.mirror(cell) if reflected else cell
        if node.kind == "source":
            result = self.source(node.source_start + offset, level)
        else:
            result = self._intern(
                CellNode("slice", level, left=cell.local_id, offset=offset)
            )
        self.ledger.bump(_actions_keys.DIAMOND_SLICE_REQUESTS)
        self.ledger.bump(_actions_keys.DIAMOND_SLICE_NORMALIZATION_VISITS, visits)
        return self.mirror(result) if reflected else result

    def split(self, cell: CellID) -> tuple[CellID, CellID]:
        node = self.resolve(cell)
        if not node.level:
            raise ValueError("a leaf has no spatial children")
        return self.slice(cell, 0, node.level - 1), self.slice(
            cell, 1 << (node.level - 1), node.level - 1
        )

    def join(self, left: CellID, right: CellID) -> CellID:
        first, second = self.resolve(left), self.resolve(right)
        if first.level != second.level:
            raise ValueError("spatial siblings require equal levels")
        reflected = first.kind == second.kind == "mirror"
        if reflected:
            left, right = self._handle(second.left), self._handle(first.left)
            first, second = self.resolve(left), self.resolve(right)
        if (
            first.kind == second.kind == "slice"
            and first.left == second.left
            and first.offset % (2 << first.level) == 0
            and second.offset == first.offset + (1 << first.level)
        ):
            parent = self._handle(first.left)
            result = self.slice(parent, first.offset, first.level + 1)
        else:
            candidate = (
                self.source_geometry.existing_parent(
                    first.source_tile, second.source_tile
                )
                if first.kind == second.kind == "source"
                else None
            )
            if candidate is not None:
                start, tile = candidate
                result = self._intern(
                    CellNode(
                        "source",
                        tile.level,
                        source_tile=tile.node_id,
                        source_start=start,
                    )
                )
            else:
                result = self._intern(
                    CellNode(
                        "join",
                        first.level + 1,
                        left=left.local_id,
                        right=right.local_id,
                    )
                )
        return self.mirror(result) if reflected else result

    def mirror(self, cell: CellID) -> CellID:
        node = self.resolve(cell)
        if node.kind == "mirror":
            return self._handle(node.left)
        if not node.level:
            return cell
        return self._intern(CellNode("mirror", node.level, left=cell.local_id))

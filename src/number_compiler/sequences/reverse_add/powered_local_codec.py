"""Exact bounded spatial actions for reverse/add source macrocells.

This is the runtime port of the finite-tile action algorithm.  A source cell is
represented by its complete action on the two finite primitive boundary
domains, in both scan orientations.  Parent actions are composed from child
action IDs and canonicalized under reflection before publication.  No digit
word, carry row, future tile, or proof-machine state is retained.

The codec is deliberately spatial.  Temporal composition must substitute the
coordinate output and all thirteen macro channels through this action; treating
spatial word-action composition as temporal composition would be incorrect.
"""

from __future__ import annotations

from collections.abc import Mapping, MutableMapping, MutableSequence
from dataclasses import dataclass
from types import MappingProxyType
from typing import TYPE_CHECKING

from number_compiler.arithmetic.automata.symmetry_powering import ActionTransform
from number_compiler.arithmetic.contracts.block_effect import (
    BoundarySide,
    BoundaryState,
)
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.local_action_codec import (
    compile_source_cell,
    initialize_local_stores,
    local_cache_hit,
    publish_oriented_action,
)
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.hashlife.execution.field_images import (
    SourceCellArena,
    SourceCellID,
    SourceForestID,
)
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.resources.payload_contracts import PayloadAuditStoreBinding


@dataclass(frozen=True, slots=True)
class ReverseLocalActionID(ArenaHandle):
    """Canonical finite local action plus its geometric orientation."""

    transform: ActionTransform = ActionTransform.IDENTITY

    def __post_init__(self) -> None:
        super(ReverseLocalActionID, self).__post_init__()
        if type(self.transform) is not ActionTransform or int(self.transform) & ~1:
            raise ValueError("reverse local actions support only proved reflection")


@dataclass(frozen=True, slots=True)
class ReverseLocalAction:
    """Both oriented word actions on both primitive boundary domains."""

    left_forward: tuple[int, ...]
    left_reverse: tuple[int, ...]
    right_forward: tuple[int, ...]
    right_reverse: tuple[int, ...]

    def mirrored(self) -> ReverseLocalAction:
        return ReverseLocalAction(
            self.left_reverse,
            self.left_forward,
            self.right_reverse,
            self.right_forward,
        )


@dataclass(frozen=True, slots=True)
class ReversePoweredLocalCodecMetrics:
    action_count: int
    source_bindings: int
    leaf_requests: int
    leaf_hits: int
    spatial_requests: int
    spatial_hits: int
    semantic_alias_hits: int
    mirror_alias_hits: int


@dataclass(frozen=True, slots=True)
class ReversePoweredLocalAuditSnapshot:
    """Fresh immutable owner view used only by explicit resource audits."""

    ledger: ResourceLedger
    sources: SourceCellArena
    base: int
    blank: int
    owner: ArenaToken
    states: tuple[tuple[BoundaryState, ...], tuple[BoundaryState, ...]]
    state_ids: tuple[Mapping[BoundaryState, int], Mapping[BoundaryState, int]]
    state_owners: tuple[int, int]
    state_backings: tuple[object, object]
    state_index_layout_valid: bool
    node_owner: int
    key_owner: int
    compose_owner: int
    leaf_owner: int
    source_owner: int
    node_backing: object
    key_backing: object
    compose_backing: object
    leaf_backing: object
    source_backing: object
    nodes: tuple[ReverseLocalAction, ...]
    keys: Mapping[ReverseLocalAction, int]
    compositions: Mapping[
        tuple[ReverseLocalActionID, ReverseLocalActionID], ReverseLocalActionID
    ]
    leaf_actions: Mapping[int, ReverseLocalActionID]
    source_actions: Mapping[SourceCellID | SourceForestID, ReverseLocalActionID]


class ReversePoweredLocalCodec:
    """Index-owned extensional codec over canonical recursive source cells."""

    _KIND = "reverse-powered-local-action"

    def __init__(
        self,
        base: int,
        sources: SourceCellArena,
        *,
        ledger: ResourceLedger | None = None,
    ) -> None:
        resources = sources.ledger if ledger is None else ledger
        if type(resources) is not ResourceLedger or sources.ledger is not resources:
            raise ValueError("reverse powered local codec requires one index ledger")
        if type(base) is not int or base < 2:
            raise ValueError("reverse powered local codec requires an exact radix")
        self.base = base
        self.blank = 2 * base - 1
        self.sources = sources
        self.ledger = resources
        self.kernel = BaseBlockEffect(base)
        left = self.kernel.boundary_universe(BoundarySide.LEFT)
        right = self.kernel.boundary_universe(BoundarySide.RIGHT)
        if left is None or right is None:
            raise AssertionError("primitive reverse boundary is not finite")
        self._states = left, right
        self.owner = ArenaToken("reverse-powered-local-codec")
        self.ledger.register_execution_root(self)
        prefix = f"reverse-powered-local-{len(self.ledger.inventory())}"
        state_owners = (
            self.ledger.register(
                prefix + "-left-state-index", "reverse_local_state_index"
            ),
            self.ledger.register(
                prefix + "-right-state-index", "reverse_local_state_index"
            ),
        )
        state_ids: tuple[
            MutableMapping[BoundaryState, int], MutableMapping[BoundaryState, int]
        ] = (
            self.ledger.make_dict(state_owners[0]),
            self.ledger.make_dict(state_owners[1]),
        )
        self.ledger.reserve_many(
            ((state_owners[0], len(left), 0), (state_owners[1], len(right), 0)),
        )
        state_ids[0].update((state, index) for index, state in enumerate(left))
        state_ids[1].update((state, index) for index, state in enumerate(right))
        self._state_ids = state_ids
        self._state_owners = state_owners
        self._left_state_ids, self._right_state_ids = state_ids
        self._node_owner = self.ledger.register(
            prefix + "-nodes", "reverse_local_action"
        )
        self._key_owner = self.ledger.register(
            prefix + "-interner", "reverse_local_action_interner"
        )
        self._compose_owner = self.ledger.register(
            prefix + "-compose", "reverse_local_action_composition"
        )
        self._leaf_owner = self.ledger.register(
            prefix + "-leaves", "reverse_local_leaf_binding"
        )
        self._source_owner = self.ledger.register(
            prefix + "-sources", "reverse_local_source_binding"
        )
        self._nodes: MutableSequence[ReverseLocalAction]
        self._keys: MutableMapping[ReverseLocalAction, int]
        self._compose: MutableMapping[
            tuple[ReverseLocalActionID, ReverseLocalActionID], ReverseLocalActionID
        ]
        self._leaf_actions: MutableMapping[int, ReverseLocalActionID]
        self._source_actions: MutableMapping[
            SourceCellID | SourceForestID, ReverseLocalActionID
        ]
        initialize_local_stores(self)
        self.ledger.register_container(
            self._compose_owner,
            self._compose,
            payloads=self._compose.items,
            composition_count=lambda: len(self._compose),
        )
        self.leaf_requests = 0
        self.leaf_hits = 0
        self.spatial_requests = 0
        self.spatial_hits = 0
        self.semantic_alias_hits = 0
        self.mirror_alias_hits = 0
        from number_compiler.sequences.reverse_add.field_action_payload_audit import (
            audit_reverse_powered_codec_owner,
        )

        self.ledger.register_payload_audit_contract(
            self,
            "reverse_add",
            self.payload_audit_store_bindings(),
            audit_reverse_powered_codec_owner,
        )

    def payload_audit_store_bindings(
        self,
    ) -> tuple[PayloadAuditStoreBinding, ...]:
        """Return exact ledger bindings for this codec's retained state."""
        from number_compiler.resources.payload_contracts import (
            PayloadAuditStoreBinding,
        )

        return (
            PayloadAuditStoreBinding(
                self._node_owner, "_nodes", "reverse_local_action"
            ),
            PayloadAuditStoreBinding(
                self._key_owner, "_keys", "reverse_local_action_interner"
            ),
            PayloadAuditStoreBinding(
                self._compose_owner, "_compose", "reverse_local_action_composition"
            ),
            PayloadAuditStoreBinding(
                self._leaf_owner, "_leaf_actions", "reverse_local_leaf_binding"
            ),
            PayloadAuditStoreBinding(
                self._source_owner, "_source_actions", "reverse_local_source_binding"
            ),
            PayloadAuditStoreBinding(
                self._state_owners[0], "_left_state_ids", "reverse_local_state_index"
            ),
            PayloadAuditStoreBinding(
                self._state_owners[1], "_right_state_ids", "reverse_local_state_index"
            ),
        )

    def payload_audit_snapshot(self) -> ReversePoweredLocalAuditSnapshot:
        """Copy all rows once, retaining only backing identities by reference."""
        return ReversePoweredLocalAuditSnapshot(
            ledger=self.ledger,
            sources=self.sources,
            base=self.base,
            blank=self.blank,
            owner=self.owner,
            states=self._states,
            state_ids=(
                MappingProxyType(dict(self._state_ids[0].items())),
                MappingProxyType(dict(self._state_ids[1].items())),
            ),
            state_owners=self._state_owners,
            state_backings=(self._left_state_ids, self._right_state_ids),
            state_index_layout_valid=(
                self._state_ids[0] is self._left_state_ids
                and self._state_ids[1] is self._right_state_ids
            ),
            node_owner=self._node_owner,
            key_owner=self._key_owner,
            compose_owner=self._compose_owner,
            leaf_owner=self._leaf_owner,
            source_owner=self._source_owner,
            node_backing=self._nodes,
            key_backing=self._keys,
            compose_backing=self._compose,
            leaf_backing=self._leaf_actions,
            source_backing=self._source_actions,
            nodes=tuple(self._nodes),
            keys=MappingProxyType(dict(self._keys.items())),
            compositions=MappingProxyType(dict(self._compose.items())),
            leaf_actions=MappingProxyType(dict(self._leaf_actions.items())),
            source_actions=MappingProxyType(dict(self._source_actions.items())),
        )

    def audit_action_record_is_exact(self, index: int, action: object) -> bool:
        """Check one node against both oriented-domain widths and its interner."""
        if (
            type(index) is not int
            or not 0 <= index < len(self._nodes)
            or type(action) is not ReverseLocalAction
        ):
            return False
        try:
            left_width = len(self._states[0])
            right_width = len(self._states[1])
            mappings = (
                action.left_forward,
                action.left_reverse,
                action.right_forward,
                action.right_reverse,
            )
            widths = (left_width, left_width, right_width, right_width)
            reference = self._handle(index)
            return (
                all(
                    type(mapping) is tuple
                    and len(mapping) == width
                    and all(type(item) is int and 0 <= item < width for item in mapping)
                    for mapping, width in zip(mappings, widths, strict=True)
                )
                and self.resolve(reference) is action
                and self._keys.get(action) == index
            )
        except (TypeError, ValueError, IndexError, KeyError, AttributeError):
            return False

    def audit_composition_is_exact(
        self,
        left: ReverseLocalActionID,
        right: ReverseLocalActionID,
        result: ReverseLocalActionID,
    ) -> bool:
        """Recompute the exact oriented spatial join without publishing it."""
        try:
            before, after, actual = (
                self.resolve(left),
                self.resolve(right),
                self.resolve(result),
            )
            expected = ReverseLocalAction(
                self._then(before.left_forward, after.left_forward),
                self._then(after.left_reverse, before.left_reverse),
                self._then(before.right_forward, after.right_forward),
                self._then(after.right_reverse, before.right_reverse),
            )
            return actual == expected and self._compose.get((left, right)) == result
        except (TypeError, ValueError, IndexError, KeyError, AttributeError):
            return False

    def audit_leaf_binding_is_exact(self, symbol: object, action_id: object) -> bool:
        """Check a leaf binding against fresh primitive boundary maps."""
        if type(symbol) is not int or not 0 <= symbol <= self.blank:
            return False
        if type(action_id) is not ReverseLocalActionID:
            return False
        try:
            expected = ReverseLocalAction(
                self._mapping(BoundarySide.LEFT, symbol),
                self._mapping(BoundarySide.LEFT, symbol),
                self._mapping(BoundarySide.RIGHT, symbol),
                self._mapping(BoundarySide.RIGHT, symbol),
            )
            return self.resolve(action_id) == expected
        except (TypeError, ValueError, IndexError, KeyError, AttributeError):
            return False

    def audit_source_binding_is_valid(self, source: object, action_id: object) -> bool:
        """Validate source authority and its issued local-action handle."""
        if type(action_id) is not ReverseLocalActionID:
            return False
        try:
            if type(source) is SourceCellID:
                self.sources.resolve(source)
            elif type(source) is SourceForestID:
                self.sources.resolve_forest(source)
            else:
                return False
            self.resolve(action_id)
        except (TypeError, ValueError, IndexError, KeyError, AttributeError):
            return False
        return True

    def _handle(
        self,
        local_id: int,
        transform: ActionTransform = ActionTransform.IDENTITY,
    ) -> ReverseLocalActionID:
        return ReverseLocalActionID(self.owner, self._KIND, local_id, transform)

    def resolve(self, reference: ReverseLocalActionID) -> ReverseLocalAction:
        if type(reference) is not ReverseLocalActionID:
            raise TypeError("expected a reverse powered local action ID")
        reference.validate(self.owner, self._KIND, size=len(self._nodes))
        raw = self._nodes[reference.local_id]
        return raw.mirrored() if reference.transform is ActionTransform.MIRROR else raw

    def _intern(
        self,
        action: ReverseLocalAction,
        reservations: tuple[tuple[int, int, int], ...] = (),
    ) -> ReverseLocalActionID:
        mirrored = action.mirrored()
        canonical, transform = min(
            ((action, ActionTransform.IDENTITY), (mirrored, ActionTransform.MIRROR)),
            key=lambda item: (
                item[0].left_forward,
                item[0].left_reverse,
                item[0].right_forward,
                item[0].right_reverse,
                int(item[1]),
            ),
        )
        return publish_oriented_action(self, canonical, transform, reservations)

    def _mapping(self, side: BoundarySide, symbol: int) -> tuple[int, ...]:
        index = int(side)
        states, ids = self._states[index], self._state_ids[index]
        return tuple(ids[self.kernel.advance(side, state, symbol)] for state in states)

    def _leaf(
        self,
        symbol: int,
        reservations: tuple[tuple[int, int, int], ...] = (),
    ) -> ReverseLocalActionID:
        if type(symbol) is not int or not 0 <= symbol <= self.blank:
            raise ValueError("reverse local leaf is outside the pair alphabet")
        self.leaf_requests += 1
        found = local_cache_hit(
            self, self._leaf_actions.get(symbol), reservations, spatial=False
        )
        if found is not None:
            return found
        left = self._mapping(BoundarySide.LEFT, symbol)
        right = self._mapping(BoundarySide.RIGHT, symbol)
        result = self._intern(
            ReverseLocalAction(left, left, right, right),
            ((self._leaf_owner, 1, 0), *reservations),
        )
        self._leaf_actions[symbol] = result
        return result

    def leaf(self, symbol: int) -> ReverseLocalActionID:
        return self._leaf(symbol)

    @staticmethod
    def _then(before: tuple[int, ...], after: tuple[int, ...]) -> tuple[int, ...]:
        return tuple(after[value] for value in before)

    def _compose_actions(
        self,
        left: ReverseLocalActionID,
        right: ReverseLocalActionID,
        reservations: tuple[tuple[int, int, int], ...] = (),
    ) -> ReverseLocalActionID:
        """Return the action of spatial concatenation ``left || right``."""
        a, b = self.resolve(left), self.resolve(right)
        self.spatial_requests += 1
        # Resolution above must precede this lookup.  The complete scoped
        # handles keep owner, kind, ID, and orientation in the cache key.
        key = left, right
        found = local_cache_hit(
            self, self._compose.get(key), reservations, spatial=True
        )
        if found is not None:
            return found
        result = self._intern(
            ReverseLocalAction(
                self._then(a.left_forward, b.left_forward),
                self._then(b.left_reverse, a.left_reverse),
                self._then(a.right_forward, b.right_forward),
                self._then(b.right_reverse, a.right_reverse),
            ),
            ((self._compose_owner, 1, 0), *reservations),
        )
        self._compose[key] = result
        return result

    def compose(
        self,
        left: ReverseLocalActionID,
        right: ReverseLocalActionID,
    ) -> ReverseLocalActionID:
        return self._compose_actions(left, right)

    def transformed(
        self,
        action: ReverseLocalActionID,
        transform: ActionTransform,
    ) -> ReverseLocalActionID:
        self.resolve(action)
        if type(transform) is not ActionTransform or int(transform) & ~1:
            raise ValueError(
                "reverse local codec has only the proved mirror automorphism"
            )
        return self._handle(action.local_id, action.transform ^ transform)

    def apply(
        self,
        action: ReverseLocalActionID,
        side: BoundarySide,
        state: BoundaryState,
        *,
        reverse: bool = False,
    ) -> BoundaryState:
        record = self.resolve(action)
        if type(side) is not BoundarySide or type(reverse) is not bool:
            raise TypeError(
                "reverse local observation requires a direction and orientation"
            )
        index = int(side)
        state_id = self._state_ids[index].get(state)
        if state_id is None:
            raise ValueError("boundary state is outside the primitive reverse domain")
        if side is BoundarySide.LEFT:
            mapping = record.left_reverse if reverse else record.left_forward
        else:
            mapping = record.right_reverse if reverse else record.right_forward
        return self._states[index][mapping[state_id]]

    def apply_index(
        self,
        action: ReverseLocalActionID,
        side: BoundarySide,
        state: int,
        *,
        reverse: bool = False,
    ) -> int:
        """Apply a source action directly to the schema's bounded state ID."""
        record = self.resolve(action)
        if (
            type(side) is not BoundarySide
            or type(state) is not int
            or type(reverse) is not bool
        ):
            raise TypeError("reverse indexed action requires exact bounded inputs")
        domain = self._states[int(side)]
        if not 0 <= state < len(domain):
            raise ValueError("reverse indexed state lies outside its port domain")
        if side is BoundarySide.LEFT:
            mapping = record.left_reverse if reverse else record.left_forward
        else:
            mapping = record.right_reverse if reverse else record.right_forward
        return mapping[state]

    @staticmethod
    def _source_key(
        source: SourceCellID | SourceForestID,
    ) -> SourceCellID | SourceForestID:
        if type(source) not in (SourceCellID, SourceForestID):
            raise TypeError("reverse local source requires a scoped cell or forest ID")
        return source

    def _source_cell_action(self, source: SourceCellID) -> ReverseLocalActionID:
        """Compile one canonical dyadic source cell with an iterative trampoline."""
        return compile_source_cell(self, source)

    def source_action(
        self,
        source: SourceCellID | SourceForestID,
    ) -> ReverseLocalActionID:
        """Compile an exact source cover without recursion or packed digit state."""
        if type(source) is SourceCellID:
            return self._source_cell_action(source)
        if type(source) is not SourceForestID:
            raise TypeError("reverse local source requires a scoped cell or forest ID")
        # Validate the forest before probing the retained binding cache.
        forest = self.sources.resolve_forest(source)
        source_key = self._source_key(source)
        found = self._source_actions.get(source_key)
        if found is not None:
            return found
        first, *following = forest.cells
        result = self._source_cell_action(first)
        for cell in following:
            result = self._compose_actions(result, self._source_cell_action(cell))
        self.ledger.reserve(self._source_owner, entries=1, nodes=0)
        self._source_actions[source_key] = result
        return result

    def metrics(self) -> ReversePoweredLocalCodecMetrics:
        return ReversePoweredLocalCodecMetrics(
            len(self._nodes),
            len(self._source_actions),
            self.leaf_requests,
            self.leaf_hits,
            self.spatial_requests,
            self.spatial_hits,
            self.semantic_alias_hits,
            self.mirror_alias_hits,
        )


__all__ = [
    "ReverseLocalAction",
    "ReverseLocalActionID",
    "ReversePoweredLocalCodec",
    "ReversePoweredLocalCodecMetrics",
]

"""Bounded spatial carry actions for Collatz radix-4 source macrocells.

The codec retains only the extensional action of a source word on the three
possible multiplication carries.  It never emits quotient digits and never
constructs future dyadic geometry.  Temporal substitution belongs to the
higher Collatz field action; spatial word composition is not a temporal
successor implementation.
"""

from __future__ import annotations
from number_compiler.arithmetic.contracts.iterative_queries import defer_binary_children
from number_compiler.arithmetic.contracts.local_action_codec import (
    initialize_local_stores,
    publish_oriented_action,
    local_cache_hit,
    compile_source_cell,
)

from collections.abc import MutableMapping, MutableSequence
from dataclasses import dataclass

from number_compiler.arithmetic.automata.symmetry_powering import (
    ActionTransform,
    FiniteKernel,
)
from number_compiler.arithmetic.carry.carry_symmetry import collatz_mul3_carry_kernel
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.hashlife.execution.field_images import (
    SourceCellArena,
    SourceCellID,
    SourceForestID,
)
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class CollatzLocalActionID(ArenaHandle):
    """Scoped identity of one oriented three-carry word action."""

    transform: ActionTransform = ActionTransform.IDENTITY

    def __post_init__(self) -> None:
        super(CollatzLocalActionID, self).__post_init__()
        if type(self.transform) is not ActionTransform or int(self.transform) & ~1:
            raise ValueError("Collatz local actions support only geometric reflection")


@dataclass(frozen=True, slots=True)
class CollatzLocalAction:
    """Forward and reverse functions on the bounded carry domain."""

    forward: tuple[int, int, int]
    reverse: tuple[int, int, int]

    def __post_init__(self) -> None:
        for mapping in (self.forward, self.reverse):
            if (
                type(mapping) is not tuple
                or len(mapping) != 3
                or any(
                    type(value) is not int or not 0 <= value < 3 for value in mapping
                )
            ):
                raise ValueError(
                    "Collatz local actions require two three-state mappings"
                )

    def mirrored(self) -> CollatzLocalAction:
        return CollatzLocalAction(self.reverse, self.forward)


@dataclass(frozen=True, slots=True)
class CollatzPoweredLocalCodecMetrics:
    action_count: int
    source_bindings: int
    leaf_requests: int
    leaf_hits: int
    spatial_requests: int
    spatial_hits: int
    semantic_alias_hits: int
    mirror_alias_hits: int


class CollatzPoweredLocalCodec:
    """Index-owned finite spatial codec for the verified Mul3 carry law."""

    _KIND = "collatz-powered-local-action"

    def __init__(
        self,
        sources: SourceCellArena,
        *,
        ledger: ResourceLedger | None = None,
    ) -> None:
        resources = sources.ledger if ledger is None else ledger
        if type(resources) is not ResourceLedger or sources.ledger is not resources:
            raise ValueError("Collatz powered local codec requires one index ledger")
        kernel = collatz_mul3_carry_kernel(4)
        if (
            type(kernel) is not FiniteKernel
            or kernel.state_count != 3
            or kernel.alphabet_size != 4
        ):
            raise AssertionError("the Collatz Mul3 carry kernel has changed shape")
        self.sources = sources
        self.ledger = resources
        self.kernel = kernel
        self.owner = ArenaToken("collatz-powered-local-codec")
        self.ledger.register_execution_root(self)
        prefix = f"collatz-powered-local-{len(self.ledger.inventory())}"
        self._node_owner = self.ledger.register(
            prefix + "-nodes", "collatz_local_action"
        )
        self._key_owner = self.ledger.register(
            prefix + "-interner", "collatz_local_action_interner"
        )
        self._compose_owner = self.ledger.register(
            prefix + "-compose", "collatz_local_action_composition"
        )
        self._leaf_owner = self.ledger.register(
            prefix + "-leaves", "collatz_local_leaf_binding"
        )
        self._source_owner = self.ledger.register(
            prefix + "-sources", "collatz_local_source_binding"
        )
        self._binary_source_owner = self.ledger.register(
            prefix + "-binary-sources", "collatz_local_source_binding"
        )
        self._nodes: MutableSequence[CollatzLocalAction]
        self._keys: MutableMapping[CollatzLocalAction, int]
        self._compose: MutableMapping[
            tuple[CollatzLocalActionID, CollatzLocalActionID], CollatzLocalActionID
        ]
        self._leaf_actions: MutableMapping[int, CollatzLocalActionID]
        self._source_actions: MutableMapping[
            SourceCellID | SourceForestID, CollatzLocalActionID
        ]
        initialize_local_stores(self)
        self._binary_source_actions: MutableMapping[
            SourceCellID | SourceForestID, CollatzLocalActionID
        ] = self.ledger.make_dict(self._binary_source_owner)
        self.ledger.register_container(
            self._node_owner,
            self._nodes,
            node_count=lambda: len(self._nodes),
            payloads=lambda: self._nodes,
        )
        self.ledger.register_container(
            self._key_owner,
            self._keys,
            payloads=self._keys.items,
        )
        self.ledger.register_container(
            self._compose_owner,
            self._compose,
            payloads=self._compose.items,
            composition_count=lambda: len(self._compose),
        )
        self.ledger.register_container(
            self._leaf_owner,
            self._leaf_actions,
            payloads=self._leaf_actions.items,
        )
        self.ledger.register_container(
            self._source_owner,
            self._source_actions,
            payloads=self._source_actions.items,
        )
        self.ledger.register_container(
            self._binary_source_owner,
            self._binary_source_actions,
            payloads=self._binary_source_actions.items,
        )
        self.leaf_requests = 0
        self.leaf_hits = 0
        self.spatial_requests = 0
        self.spatial_hits = 0
        self.semantic_alias_hits = 0
        self.mirror_alias_hits = 0

    def _handle(
        self,
        local_id: int,
        transform: ActionTransform = ActionTransform.IDENTITY,
    ) -> CollatzLocalActionID:
        return CollatzLocalActionID(self.owner, self._KIND, local_id, transform)

    def resolve(self, reference: CollatzLocalActionID) -> CollatzLocalAction:
        if type(reference) is not CollatzLocalActionID:
            raise TypeError("expected a Collatz powered local action ID")
        reference.validate(self.owner, self._KIND, size=len(self._nodes))
        if (
            type(reference.transform) is not ActionTransform
            or int(reference.transform) & ~1
        ):
            raise ValueError("malformed Collatz local action transform")
        action = self._nodes[reference.local_id]
        return (
            action.mirrored()
            if reference.transform is ActionTransform.MIRROR
            else action
        )

    def _intern(
        self,
        action: CollatzLocalAction,
        reservations: tuple[tuple[int, int, int], ...] = (),
    ) -> CollatzLocalActionID:
        if type(action) is not CollatzLocalAction:
            raise TypeError("Collatz local interning requires an extensional action")
        action.__post_init__()
        mirrored = action.mirrored()
        canonical, transform = min(
            ((action, ActionTransform.IDENTITY), (mirrored, ActionTransform.MIRROR)),
            key=lambda item: (item[0].forward, item[0].reverse, int(item[1])),
        )
        return publish_oriented_action(self, canonical, transform, reservations)

    def _leaf(
        self,
        symbol: int,
        reservations: tuple[tuple[int, int, int], ...] = (),
    ) -> CollatzLocalActionID:
        if type(symbol) is not int or not 0 <= symbol < self.kernel.alphabet_size:
            raise ValueError("Collatz local leaf is outside the radix-4 alphabet")
        self.leaf_requests += 1
        found = local_cache_hit(
            self, self._leaf_actions.get(symbol), reservations, spatial=False
        )
        if found is not None:
            return found
        mapping = (
            self.kernel.transition(0, symbol),
            self.kernel.transition(1, symbol),
            self.kernel.transition(2, symbol),
        )
        result = self._intern(
            CollatzLocalAction(mapping, mapping),
            ((self._leaf_owner, 1, 0), *reservations),
        )
        self._leaf_actions[symbol] = result
        return result

    def leaf(self, symbol: int) -> CollatzLocalActionID:
        return self._leaf(symbol)

    @staticmethod
    def _then(
        before: tuple[int, int, int],
        after: tuple[int, int, int],
    ) -> tuple[int, int, int]:
        return after[before[0]], after[before[1]], after[before[2]]

    def _compose_actions(
        self,
        left: CollatzLocalActionID,
        right: CollatzLocalActionID,
        reservations: tuple[tuple[int, int, int], ...] = (),
    ) -> CollatzLocalActionID:
        """Return the action of spatial concatenation ``left || right``."""
        a, b = self.resolve(left), self.resolve(right)
        self.spatial_requests += 1
        # Both operands have already been resolved.  Keep their complete
        # scoped identities in the retained key so local integer aliases from
        # another codec or sort can never hit this composition.
        key = left, right
        found = local_cache_hit(
            self, self._compose.get(key), reservations, spatial=True
        )
        if found is not None:
            return found
        result = self._intern(
            CollatzLocalAction(
                self._then(a.forward, b.forward),
                self._then(b.reverse, a.reverse),
            ),
            ((self._compose_owner, 1, 0), *reservations),
        )
        self._compose[key] = result
        return result

    def compose(
        self,
        left: CollatzLocalActionID,
        right: CollatzLocalActionID,
    ) -> CollatzLocalActionID:
        return self._compose_actions(left, right)

    def transformed(
        self,
        action: CollatzLocalActionID,
        transform: ActionTransform,
    ) -> CollatzLocalActionID:
        self.resolve(action)
        if type(transform) is not ActionTransform or int(transform) & ~1:
            raise ValueError(
                "Collatz local codec has only the proved mirror automorphism"
            )
        return self._handle(action.local_id, action.transform ^ transform)

    def apply(
        self,
        action: CollatzLocalActionID,
        state: int,
        *,
        reverse: bool = False,
    ) -> int:
        record = self.resolve(action)
        if type(state) is not int or not 0 <= state < 3 or type(reverse) is not bool:
            raise ValueError(
                "Collatz carry observation requires a three-state exact port"
            )
        mapping = record.reverse if reverse else record.forward
        return mapping[state]

    @staticmethod
    def _source_key(
        source: SourceCellID | SourceForestID,
    ) -> SourceCellID | SourceForestID:
        if type(source) is SourceCellID:
            return source
        if type(source) is SourceForestID:
            return source
        raise TypeError("Collatz local source requires a scoped cell or forest ID")

    def _cell_action(self, source: SourceCellID) -> CollatzLocalActionID:
        """Compile one canonical source subtree bottom-up without recursion."""
        return compile_source_cell(self, source)

    def source_action(
        self,
        source: SourceCellID | SourceForestID,
    ) -> CollatzLocalActionID:
        """Compile a source cell or complete canonical forest compositionally."""
        if type(source) is SourceCellID:
            return self._cell_action(source)
        if type(source) is not SourceForestID:
            raise TypeError("Collatz local source requires a scoped cell or forest ID")
        forest = self.sources.resolve_forest(source)
        key = self._source_key(source)
        found = self._source_actions.get(key)
        if found is not None:
            return found
        first, *following = forest.cells
        result = self._cell_action(first)
        for cell in following:
            result = self._compose_actions(result, self._cell_action(cell))
        self.ledger.reserve(self._source_owner, entries=1)
        self._source_actions[key] = result
        return result

    def radix4_source_action(
        self,
        source: SourceCellID | SourceForestID,
    ) -> CollatzLocalActionID:
        """Compile an aligned binary source as radix-4 carry actions.

        The physical Collatz source arena stores binary digits.  The bounded
        multiplication interface, however, is the verified radix-4 ``Mul3``
        carry kernel.  Pairing ``b[2i] + 2*b[2i+1]`` is the morphism between
        those alphabets.  Missing and distinguished-blank high bits are zero
        padding; no future digit or normalized tail is constructed.

        ``source_action`` remains the exact radix-4 word API used by proof and
        component tests.  Keeping the two occurrence maps distinct prevents a
        binary source handle from aliasing its unrelated radix-4 reading.
        """
        key = self._source_key(source)
        self.sources.binding_extent(source)
        base, blank = self.sources.alphabet()
        if base != 2:
            raise ValueError("Collatz production sources must be binary")
        found = self._binary_source_actions.get(key)
        if found is not None:
            return found
        result: CollatzLocalActionID | None
        if type(source) is SourceCellID:
            result = self._binary_cell_action(source, blank)
        else:
            assert type(source) is SourceForestID
            cells = self.sources.resolve_forest(source).cells
            result = None
            for cell in cells:
                action = self._binary_cell_action(cell, blank)
                result = (
                    action if result is None else self._compose_actions(result, action)
                )
            if result is None:
                raise AssertionError("source forests always contain a cell")
        self.ledger.reserve(self._binary_source_owner, entries=1)
        self._binary_source_actions[key] = result
        self.ledger.bump("collatz_radix4_source_morphism_compilations")
        return result

    @staticmethod
    def _binary_bit(symbol: int, blank: int) -> int:
        value = 0 if symbol == blank else symbol
        if value not in (0, 1):
            raise ValueError("Collatz binary source contains another symbol")
        return value

    def _binary_cell_action(
        self,
        source: SourceCellID,
        blank: int,
    ) -> CollatzLocalActionID:
        """Compile aligned radix-4 pairs over one canonical dyadic subtree."""
        key = self._source_key(source)
        found = self._binary_source_actions.get(key)
        if found is not None:
            return found
        pending: list[tuple[SourceCellID, bool]] = [(source, False)]
        while pending:
            current, ready = pending.pop()
            current_key = self._source_key(current)
            if current_key in self._binary_source_actions:
                continue
            record = self.sources.resolve(current)
            if record.level == 0:
                low = self._binary_bit(self.sources.symbol(current), blank)
                result = self._leaf(low)
            elif record.level == 1:
                low_cell, high_cell = self.sources.children(current)
                low = self._binary_bit(self.sources.symbol(low_cell), blank)
                high = self._binary_bit(self.sources.symbol(high_cell), blank)
                result = self._leaf(low | (high << 1))
            elif not ready:
                defer_binary_children(pending, current, self.sources.children)
                continue
            else:
                left, right = self.sources.children(current)
                result = self._compose_actions(
                    self._binary_source_actions[self._source_key(left)],
                    self._binary_source_actions[self._source_key(right)],
                )
            self.ledger.reserve(self._binary_source_owner, entries=1)
            self._binary_source_actions[current_key] = result
        return self._binary_source_actions[key]

    def metrics(self) -> CollatzPoweredLocalCodecMetrics:
        return CollatzPoweredLocalCodecMetrics(
            len(self._nodes),
            len(self._source_actions) + len(self._binary_source_actions),
            self.leaf_requests,
            self.leaf_hits,
            self.spatial_requests,
            self.spatial_hits,
            self.semantic_alias_hits,
            self.mirror_alias_hits,
        )


__all__ = [
    "CollatzLocalAction",
    "CollatzLocalActionID",
    "CollatzPoweredLocalCodec",
    "CollatzPoweredLocalCodecMetrics",
]

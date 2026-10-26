"""Shared bookkeeping and source traversal for bounded oriented local codecs.

Callers retain concrete action validation and source-authority resolution. This
kernel does not publish future geometry or interpret temporal successors.
"""

from __future__ import annotations

from collections.abc import MutableMapping, MutableSequence
from typing import Protocol, TypeVar, overload

from number_compiler.arithmetic.automata.symmetry_powering import ActionTransform
from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple
from number_compiler.arithmetic.contracts.iterative_queries import defer_binary_children
from number_compiler.arithmetic.contracts.scoped_handles import (
    ArenaHandle,
    ArenaToken,
)
from number_compiler.hashlife.execution.field_images import (
    SourceCellArena,
    SourceCellID,
    SourceForestID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.lifecycle import cleanup_all
from number_compiler.resources.stores import LedgerDict, append_indexed_node

A = TypeVar("A")
H = TypeVar("H")
ScopedH = TypeVar("ScopedH", bound=ArenaHandle)
K = TypeVar("K")
V = TypeVar("V")
Reservations = tuple[tuple[int, int, int], ...]


def validate_local_handle(
    reference: object,
    handle_type: type[ScopedH],
    owner: ArenaToken,
    kind: str,
    *,
    size: int,
) -> ScopedH:
    """Validate exact handle sort, owner, kind, and allocated local range."""
    if not isinstance(reference, handle_type) or type(reference) is not handle_type:
        raise TypeError(f"expected {handle_type.__name__}")
    return reference.validate(owner, kind, size=size)


def validate_mirror_transform(
    transform: object,
    *,
    message: str,
) -> ActionTransform:
    """Accept only the identity/reflection subgroup used by local codecs."""
    if type(transform) is not ActionTransform or int(transform) & ~1:
        raise ValueError(message)
    return transform


@overload
def compose_finite_lookup_maps(
    before: tuple[int, int, int], after: tuple[int, int, int]
) -> tuple[int, int, int]: ...


@overload
def compose_finite_lookup_maps(
    before: tuple[int, ...], after: tuple[int, ...]
) -> tuple[int, ...]: ...


def compose_finite_lookup_maps(
    before: tuple[int, ...], after: tuple[int, ...]
) -> tuple[int, ...]:
    """Compose admitted endomorphisms in application order: ``after ∘ before``.

    Each family validates maps when admitting an action record. Revalidating
    every finite tuple here would repeat work on every internal spatial join.
    """
    return tuple(after[value] for value in before)


def validate_finite_lookup_map(
    mapping: object, *, expected_size: int | None = None
) -> None:
    """Validate one nonempty finite endomorphism at an action admission edge."""
    if not is_exact_object_tuple(mapping):
        raise TypeError("finite lookup maps must be immutable tuples")
    size = len(mapping)
    if expected_size is not None and size != expected_size:
        raise ValueError("finite lookup map has the wrong state-domain size")
    if size == 0:
        raise ValueError("finite lookup maps require a nonempty state domain")
    if any(type(value) is not int or not 0 <= value < size for value in mapping):
        raise ValueError("finite lookup map leaves its state domain")


def publish_source_binding(
    ledger: ResourceLedger,
    owner: int,
    store: LedgerDict[K, V],
    key: K,
    value: V,
) -> V:
    """Reserve and publish one source binding with rollback on store failure."""
    if (
        store.ledger is not ledger
        or store.owner != owner
        or not ledger.is_factory_container(store)
    ):
        raise ValueError("source binding store is outside its ledger owner")
    if key in store:
        existing = store[key]
        if existing != value:
            raise ValueError("source binding changed during publication")
        return existing
    ledger.reserve(owner, entries=1, nodes=0)
    try:
        store[key] = value
    except BaseException:

        def rollback_publication() -> None:
            removed = store.rollback_inserted_value(key, value)
            if not removed and key in store:
                raise RuntimeError("source binding rollback found another value")
            ledger.release(owner, entries=1, nodes=0)

        cleanup_all((rollback_publication,))
        raise
    return value


class LocalCodec(Protocol[A, H]):
    sources: SourceCellArena
    ledger: ResourceLedger
    _node_owner: int
    _key_owner: int
    _compose_owner: int
    _leaf_owner: int
    _source_owner: int
    _nodes: MutableSequence[A]
    _keys: MutableMapping[A, int]
    _compose: MutableMapping[tuple[H, H], H]
    _leaf_actions: MutableMapping[int, H]
    _source_actions: LedgerDict[SourceCellID | SourceForestID, H]
    semantic_alias_hits: int
    mirror_alias_hits: int
    leaf_hits: int
    spatial_hits: int

    def scoped_handle(self, local_id: int, transform: ActionTransform) -> H: ...
    @staticmethod
    def _source_key(
        source: SourceCellID | SourceForestID,
    ) -> SourceCellID | SourceForestID: ...
    def _leaf(self, symbol: int, reservations: Reservations = ()) -> H: ...
    def _compose_actions(
        self, left: H, right: H, reservations: Reservations = ()
    ) -> H: ...

    def initialize_local_stores(self) -> None:
        self._nodes = self.ledger.make_list(self._node_owner)
        self._keys = self.ledger.make_dict(self._key_owner)
        self._compose = self.ledger.make_dict(self._compose_owner)
        self._leaf_actions = self.ledger.make_dict(self._leaf_owner)
        self._source_actions = self.ledger.make_dict(self._source_owner)

    def publish_oriented_action(
        self,
        canonical: A,
        transform: ActionTransform,
        reservations: Reservations,
    ) -> H:
        found = self._keys.get(canonical)
        if found is not None:
            self.ledger.reserve_many(reservations)
            self.semantic_alias_hits += 1
            if transform is ActionTransform.MIRROR:
                self.mirror_alias_hits += 1
            return self.scoped_handle(found, transform)
        local_id = append_indexed_node(
            self.ledger,
            self._nodes,
            self._keys,
            self._node_owner,
            self._key_owner,
            canonical,
            canonical,
            reservations=reservations,
        )
        if transform is ActionTransform.MIRROR:
            self.mirror_alias_hits += 1
        return self.scoped_handle(local_id, transform)

    def local_cache_hit(
        self,
        cached: H | None,
        reservations: Reservations,
        *,
        spatial: bool = False,
    ) -> H | None:
        if cached is not None:
            self.ledger.reserve_many(reservations)
            if spatial:
                self.spatial_hits += 1
            else:
                self.leaf_hits += 1
        return cached

    def compile_source_cell(self, source: SourceCellID) -> H:
        self.sources.resolve(source)
        source_key = self._source_key(source)
        found = self._source_actions.get(source_key)
        if found is not None:
            return found
        pending: list[tuple[SourceCellID, bool]] = [(source, False)]
        while pending:
            current, ready = pending.pop()
            current_key = self._source_key(current)
            if current_key in self._source_actions:
                continue
            record = self.sources.resolve(current)
            if record.level == 0:
                result = self._leaf(
                    self.sources.symbol(current), ((self._source_owner, 1, 0),)
                )
            elif not ready:
                defer_binary_children(pending, current, self.sources.children)
                continue
            else:
                left, right = self.sources.children(current)
                result = self._compose_actions(
                    self._source_actions[self._source_key(left)],
                    self._source_actions[self._source_key(right)],
                    ((self._source_owner, 1, 0),),
                )
            self._source_actions[current_key] = result
        return self._source_actions[source_key]

    def compile_source_forest(self, source: SourceForestID) -> H:
        """Compose a validated forest's adjacent source-cell actions once."""
        forest = self.sources.resolve_forest(source)
        source_key = self._source_key(source)
        found = self._source_actions.get(source_key)
        if found is not None:
            return found
        if not forest.cells:
            raise ValueError("source forests must contain at least one cell")
        cells = iter(forest.cells)
        result = self.compile_source_cell(next(cells))
        for cell in cells:
            result = self._compose_actions(result, self.compile_source_cell(cell))
        return publish_source_binding(
            self.ledger, self._source_owner, self._source_actions, source_key, result
        )


def initialize_local_stores(codec: LocalCodec[A, H]) -> None:
    return codec.initialize_local_stores()


def publish_oriented_action(
    codec: LocalCodec[A, H],
    canonical: A,
    transform: ActionTransform,
    reservations: Reservations,
) -> H:
    return codec.publish_oriented_action(canonical, transform, reservations)


def local_cache_hit(
    codec: LocalCodec[A, H],
    cached: H | None,
    reservations: Reservations,
    *,
    spatial: bool = False,
) -> H | None:
    return codec.local_cache_hit(cached, reservations, spatial=spatial)


def compile_source_cell(codec: LocalCodec[A, H], source: SourceCellID) -> H:
    return codec.compile_source_cell(source)


def compile_source_forest(codec: LocalCodec[A, H], source: SourceForestID) -> H:
    return codec.compile_source_forest(source)

"""Shared bookkeeping and source traversal for bounded oriented local codecs.

Callers retain concrete action validation and source-authority resolution. This
kernel does not publish future geometry or interpret temporal successors.
"""

from __future__ import annotations

from collections.abc import MutableMapping, MutableSequence
from typing import Protocol, TypeVar

from number_compiler.arithmetic.automata.symmetry_powering import ActionTransform
from number_compiler.arithmetic.contracts.iterative_queries import defer_binary_children
from number_compiler.hashlife.execution.field_images import (
    SourceCellArena,
    SourceCellID,
    SourceForestID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import append_indexed_node

A = TypeVar("A")
H = TypeVar("H")
Reservations = tuple[tuple[int, int, int], ...]


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
    _source_actions: MutableMapping[SourceCellID | SourceForestID, H]
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

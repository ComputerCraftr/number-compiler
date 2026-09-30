"""Shared bookkeeping and source traversal for bounded oriented local codecs.

Callers retain concrete action validation and source-authority resolution. This
kernel does not publish future geometry or interpret temporal successors.
"""

from __future__ import annotations
from number_compiler.arithmetic.contracts.iterative_queries import defer_binary_children
from collections.abc import MutableMapping, MutableSequence
from typing import Protocol, TypeVar
from number_compiler.arithmetic.automata.symmetry_powering import ActionTransform
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

    def _handle(self, local_id: int, transform: ActionTransform) -> H: ...
    def _source_key(
        self, source: SourceCellID | SourceForestID
    ) -> SourceCellID | SourceForestID: ...
    def _leaf(self, symbol: int, reservations: Reservations = ()) -> H: ...
    def _compose_actions(
        self, left: H, right: H, reservations: Reservations = ()
    ) -> H: ...


def initialize_local_stores(codec: LocalCodec[A, H]) -> None:
    codec._nodes = codec.ledger.make_list(codec._node_owner)
    codec._keys = codec.ledger.make_dict(codec._key_owner)
    codec._compose = codec.ledger.make_dict(codec._compose_owner)
    codec._leaf_actions = codec.ledger.make_dict(codec._leaf_owner)
    codec._source_actions = codec.ledger.make_dict(codec._source_owner)


def publish_oriented_action(
    codec: LocalCodec[A, H],
    canonical: A,
    transform: ActionTransform,
    reservations: Reservations,
) -> H:
    found = codec._keys.get(canonical)
    if found is not None:
        codec.ledger.reserve_many(reservations)
        codec.semantic_alias_hits += 1
        if transform is ActionTransform.MIRROR:
            codec.mirror_alias_hits += 1
        return codec._handle(found, transform)
    local_id = append_indexed_node(
        codec.ledger,
        codec._nodes,
        codec._keys,
        codec._node_owner,
        codec._key_owner,
        canonical,
        canonical,
        reservations=reservations,
    )
    if transform is ActionTransform.MIRROR:
        codec.mirror_alias_hits += 1
    return codec._handle(local_id, transform)


def local_cache_hit(
    codec: LocalCodec[A, H],
    cached: H | None,
    reservations: Reservations,
    *,
    spatial: bool = False,
) -> H | None:
    if cached is not None:
        codec.ledger.reserve_many(reservations)
        if spatial:
            codec.spatial_hits += 1
        else:
            codec.leaf_hits += 1
    return cached


def compile_source_cell(codec: LocalCodec[A, H], source: SourceCellID) -> H:
    codec.sources.resolve(source)
    source_key = codec._source_key(source)
    found = codec._source_actions.get(source_key)
    if found is not None:
        return found
    pending: list[tuple[SourceCellID, bool]] = [(source, False)]
    while pending:
        current, ready = pending.pop()
        current_key = codec._source_key(current)
        if current_key in codec._source_actions:
            continue
        record = codec.sources.resolve(current)
        if record.level == 0:
            result = codec._leaf(
                codec.sources.symbol(current), ((codec._source_owner, 1, 0),)
            )
        elif not ready:
            defer_binary_children(pending, current, codec.sources.children)
            continue
        else:
            left, right = codec.sources.children(current)
            result = codec._compose_actions(
                codec._source_actions[codec._source_key(left)],
                codec._source_actions[codec._source_key(right)],
                ((codec._source_owner, 1, 0),),
            )
        codec._source_actions[current_key] = result
    return codec._source_actions[source_key]

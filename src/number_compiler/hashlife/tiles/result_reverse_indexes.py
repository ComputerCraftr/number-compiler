"""Result reference indexing owned by the completed-result arena."""

from __future__ import annotations

from typing import TYPE_CHECKING, cast

from number_compiler.hashlife.tiles.tile_result_records import (
    CompletedResult,
    FusedVariantKey,
    PoweredResultKey,
    ResultDependencyHead,
    ResultDependencyLinks,
    ResultDependencyMember,
    ResultVariantKey,
)
from number_compiler.hashlife.tiles.tile_result_types import is_execution_key
from number_compiler.hashlife.tiles.tiles import TileID
from number_compiler.resources.metric_keys import (
    hashlife_tiles as _tiles_keys,
)

_MISSING_REVERSE_VALUE = object()

if TYPE_CHECKING:
    from number_compiler.hashlife.tiles.tile_result_types import (
        ExecutionKey as _ExecutionKey,
    )
    from number_compiler.hashlife.tiles.tile_result_types import (
        ExecutionValue,
        ReverseValue,
    )
    from number_compiler.hashlife.tiles.tile_result_types import (
        ReverseKey as _ReverseKey,
    )
    from number_compiler.hashlife.tiles.tile_results import CompletedResultArena


def index_entries(self: CompletedResultArena, tiles: tuple[TileID, ...]) -> int:
    return len(tiles) + sum(
        1 for tile in tiles if ResultDependencyHead(tile) not in self.reverse_view
    )


def add_membership(
    self: CompletedResultArena, tile: TileID, key: _ExecutionKey
) -> None:
    head_key = ResultDependencyHead(tile)
    previous = self.reverse_view.get(head_key)
    if previous is not None and not is_execution_key(previous):
        raise ValueError("completed-result reverse head is corrupt")
    member_key = ResultDependencyMember(tile, key)
    if member_key in self.reverse_view:
        raise ValueError("completed-result reverse membership is duplicated")
    self.write_reverse(member_key, ResultDependencyLinks(None, previous))
    if is_execution_key(previous):
        old_key = ResultDependencyMember(tile, previous)
        links = self.reverse_view.get(old_key)
        if type(links) is not ResultDependencyLinks:
            raise ValueError("completed-result reverse link is corrupt")
        self.write_reverse(old_key, ResultDependencyLinks(key, links.following))
    self.write_reverse(head_key, key)


def reverse_snapshot(
    self: CompletedResultArena,
    tiles: tuple[TileID, ...],
    key: _ExecutionKey,
) -> tuple[tuple[_ReverseKey, object], ...]:
    touched: list[_ReverseKey] = []
    for tile in tiles:
        head_key = ResultDependencyHead(tile)
        member_key = ResultDependencyMember(tile, key)
        touched.extend((head_key, member_key))
        previous = self.reverse_view.get(head_key)
        if is_execution_key(previous):
            touched.append(ResultDependencyMember(tile, previous))
    return tuple(
        (item, self.reverse_view.get(item, _MISSING_REVERSE_VALUE))
        for item in dict.fromkeys(touched)
    )


def restore_reverse(
    self: CompletedResultArena,
    snapshot: tuple[tuple[_ReverseKey, object], ...],
) -> None:
    for key, value in snapshot:
        if value is _MISSING_REVERSE_VALUE:
            self.discard_reverse(key)
        else:
            # Snapshot entries came from this typed store; only the absence
            # sentinel widened their annotation while the mutation was pending.
            self.write_reverse(key, cast("ReverseValue", value))


def has_completed_result_input(
    self: CompletedResultArena,
    action: object,
    tile: object,
) -> bool:
    """Return whether an exact result exists for ``action`` on ``tile``.

    This is a negative promotion preflight, not cache authority.  It validates
    the requested handles and every traversed reverse link, while the caller's
    later exact-key lookup remains responsible for admitting ports and result
    semantics.
    """
    from number_compiler.hashlife.actions.field_actions import FieldCellActionID

    if type(action) is not FieldCellActionID:
        raise TypeError("completed-result presence requires a field action ID")
    if type(tile) is not TileID:
        raise TypeError("completed-result presence requires a tile ID")
    self.action_validator(action)
    self.tiles.resolve(tile)
    visits = 1
    try:
        current = self.reverse_view.get(ResultDependencyHead(tile))
        if current is None:
            return False
        if not is_execution_key(current):
            raise ValueError("completed-result reverse head is corrupt")
        previous = None
        members = 0
        while current is not None:
            members += 1
            if members > len(self.reverse_view):
                raise ValueError("completed-result reverse index contains a cycle")
            visits += 1
            member = self.reverse_view.get(ResultDependencyMember(tile, current))
            if type(member) is not ResultDependencyLinks or member.previous != previous:
                raise ValueError("completed-result reverse link is corrupt")
            if type(current) is PoweredResultKey and (
                current.action == action and current.input == tile
            ):
                visits += 1
                retained = self.memo_view.get(current)
                if type(retained) is not CompletedResult:
                    raise ValueError("completed-result reverse member lost its result")
                return True
            previous, current = current, member.following
            if current is not None and not is_execution_key(current):
                raise ValueError("completed-result reverse link is corrupt")
        return False
    finally:
        self.ledger.bump(_tiles_keys.COMPLETED_RESULT_PRESENCE_INDEX_VISITS, visits)


def remove_membership(
    self: CompletedResultArena, tile: TileID, key: _ExecutionKey
) -> None:
    member_key = ResultDependencyMember(tile, key)
    links = self.discard_reverse(member_key)
    if type(links) is not ResultDependencyLinks:
        raise ValueError("completed-result reverse membership is missing")
    removed = 1
    head_key = ResultDependencyHead(tile)
    if links.previous is None:
        if links.following is None:
            self.discard_reverse(head_key)
            removed += 1
        else:
            self.write_reverse(head_key, links.following)
    else:
        before_key = ResultDependencyMember(tile, links.previous)
        before = self.reverse_view[before_key]
        if type(before) is not ResultDependencyLinks:
            raise ValueError("completed-result previous link is corrupt")
        self.write_reverse(
            before_key,
            ResultDependencyLinks(
                before.previous,
                links.following,
            ),
        )
    if links.following is not None:
        after_key = ResultDependencyMember(tile, links.following)
        after = self.reverse_view[after_key]
        if type(after) is not ResultDependencyLinks:
            raise ValueError("completed-result following link is corrupt")
        self.write_reverse(
            after_key,
            ResultDependencyLinks(
                links.previous,
                after.following,
            ),
        )
    self.ledger.release(self.reverse_owner, entries=removed)
    self.ledger.bump(_tiles_keys.COMPLETED_RESULT_REVERSE_INDEX_REMOVALS, removed)


def publish_indexed_result(
    arena: CompletedResultArena,
    key: _ExecutionKey,
    value: ExecutionValue,
    *,
    retained_nodes: int = 0,
    referenced: tuple[TileID, ...] | None = None,
) -> None:
    """Atomically insert an admitted, absent result and its reverse links.

    Callers own semantic admission and duplicate checks. This transaction owns
    reservations and rollback, including a failed reverse-index snapshot.
    """
    if referenced is None:
        referenced = arena.tiles_for(key, value)
    reservations = (
        (arena.memo_owner, 1, retained_nodes),
        (arena.reverse_owner, arena.index_entries(referenced), 0),
    )
    reverse_snapshot = arena.reverse_snapshot(referenced, key)
    arena.ledger.reserve_many(reservations)
    try:
        arena.write_memo_reserved(key, value)
        for tile in referenced:
            arena.add_membership(tile, key)
    except BaseException:
        arena.discard_memo(key)
        arena.restore_reverse(reverse_snapshot)
        for owner, entries, nodes in reservations:
            arena.ledger.release(owner, entries, nodes)
        raise


def restore_variant_publication(
    arena: CompletedResultArena,
    key: _ExecutionKey,
    reverse_snapshot: tuple[tuple[_ReverseKey, object], ...],
    variant_key: ResultVariantKey | FusedVariantKey,
    old_variants: int,
) -> None:
    """Restore only stores mutated by publication, before caller releases credits."""
    arena.discard_memo(key)
    arena.restore_reverse(reverse_snapshot)
    if old_variants:
        arena.write_variant(variant_key, old_variants)
    else:
        arena.discard_variant(variant_key)

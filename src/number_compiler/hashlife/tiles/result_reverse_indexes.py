"""Result reference indexing owned by the completed-result arena."""

from __future__ import annotations

from typing import TYPE_CHECKING, cast

from number_compiler.hashlife.tiles.tile_result_records import (
    CompletedResult,
    PoweredResultKey,
    _FusedVariantKey,
    _ResultVariantKey,
    _ReverseHead,
    _ReverseLinks,
    _ReverseMember,
)
from number_compiler.hashlife.tiles.tile_result_types import is_execution_key
from number_compiler.hashlife.tiles.tile_results import (
    _MISSING,
)
from number_compiler.hashlife.tiles.tiles import TileID
from number_compiler.resources.metric_keys import (
    hashlife_tiles as _tiles_keys,
)

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


def _index_entries(self: CompletedResultArena, tiles: tuple[TileID, ...]) -> int:
    return len(tiles) + sum(
        1 for tile in tiles if _ReverseHead(tile) not in self._reverse
    )


def _add_membership(
    self: CompletedResultArena, tile: TileID, key: _ExecutionKey
) -> None:
    head_key = _ReverseHead(tile)
    previous = self._reverse.get(head_key)
    if previous is not None and not is_execution_key(previous):
        raise ValueError("completed-result reverse head is corrupt")
    member_key = _ReverseMember(tile, key)
    if member_key in self._reverse:
        raise ValueError("completed-result reverse membership is duplicated")
    self._write_reverse(member_key, _ReverseLinks(None, previous))
    if is_execution_key(previous):
        old_key = _ReverseMember(tile, previous)
        links = self._reverse.get(old_key)
        if type(links) is not _ReverseLinks:
            raise ValueError("completed-result reverse link is corrupt")
        self._write_reverse(old_key, _ReverseLinks(key, links.following))
    self._write_reverse(head_key, key)


def _reverse_snapshot(
    self: CompletedResultArena,
    tiles: tuple[TileID, ...],
    key: _ExecutionKey,
) -> tuple[tuple[_ReverseKey, object], ...]:
    touched: list[_ReverseKey] = []
    for tile in tiles:
        head_key = _ReverseHead(tile)
        member_key = _ReverseMember(tile, key)
        touched.extend((head_key, member_key))
        previous = self._reverse.get(head_key)
        if is_execution_key(previous):
            touched.append(_ReverseMember(tile, previous))
    return tuple(
        (item, self._reverse.get(item, _MISSING)) for item in dict.fromkeys(touched)
    )


def _restore_reverse(
    self: CompletedResultArena,
    snapshot: tuple[tuple[_ReverseKey, object], ...],
) -> None:
    for key, value in snapshot:
        if value is _MISSING:
            self._reverse.pop(key, None)
        else:
            # Snapshot entries came from this typed store; only the absence
            # sentinel widened their annotation while the mutation was pending.
            self._reverse[key] = cast("ReverseValue", value)


def _has_completed_result_input(
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
    self._validate_action(action)
    self.tiles.resolve(tile)
    visits = 1
    try:
        current = self._reverse.get(_ReverseHead(tile))
        if current is None:
            return False
        if not is_execution_key(current):
            raise ValueError("completed-result reverse head is corrupt")
        previous = None
        members = 0
        while current is not None:
            members += 1
            if members > len(self._reverse):
                raise ValueError("completed-result reverse index contains a cycle")
            visits += 1
            member = self._reverse.get(_ReverseMember(tile, current))
            if type(member) is not _ReverseLinks or member.previous != previous:
                raise ValueError("completed-result reverse link is corrupt")
            if type(current) is PoweredResultKey and (
                current.action == action and current.input == tile
            ):
                visits += 1
                retained = self._memo.get(current)
                if type(retained) is not CompletedResult:
                    raise ValueError("completed-result reverse member lost its result")
                return True
            previous, current = current, member.following
            if current is not None and not is_execution_key(current):
                raise ValueError("completed-result reverse link is corrupt")
        return False
    finally:
        self.ledger.bump(_tiles_keys.COMPLETED_RESULT_PRESENCE_INDEX_VISITS, visits)


def _remove_membership(
    self: CompletedResultArena, tile: TileID, key: _ExecutionKey
) -> None:
    member_key = _ReverseMember(tile, key)
    links = self._reverse.pop(member_key, None)
    if type(links) is not _ReverseLinks:
        raise ValueError("completed-result reverse membership is missing")
    removed = 1
    head_key = _ReverseHead(tile)
    if links.previous is None:
        if links.following is None:
            self._reverse.pop(head_key, None)
            removed += 1
        else:
            self._reverse[head_key] = links.following
    else:
        before_key = _ReverseMember(tile, links.previous)
        before = self._reverse[before_key]
        if type(before) is not _ReverseLinks:
            raise ValueError("completed-result previous link is corrupt")
        self._reverse[before_key] = _ReverseLinks(
            before.previous,
            links.following,
        )
    if links.following is not None:
        after_key = _ReverseMember(tile, links.following)
        after = self._reverse[after_key]
        if type(after) is not _ReverseLinks:
            raise ValueError("completed-result following link is corrupt")
        self._reverse[after_key] = _ReverseLinks(
            links.previous,
            after.following,
        )
    self.ledger.release(self._reverse_owner, entries=removed)
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
        referenced = arena._tiles_for(key, value)
    reservations = (
        (arena._memo_owner, 1, retained_nodes),
        (arena._reverse_owner, arena._index_entries(referenced), 0),
    )
    reverse_snapshot = arena._reverse_snapshot(referenced, key)
    arena.ledger.reserve_many(reservations)
    try:
        arena._memo[key] = value
        for tile in referenced:
            arena._add_membership(tile, key)
    except BaseException:
        arena._memo.pop(key, None)
        arena._restore_reverse(reverse_snapshot)
        for owner, entries, nodes in reservations:
            arena.ledger.release(owner, entries, nodes)
        raise


def restore_variant_publication(
    arena: CompletedResultArena,
    key: _ExecutionKey,
    reverse_snapshot: tuple[tuple[_ReverseKey, object], ...],
    variant_key: _ResultVariantKey | _FusedVariantKey,
    old_variants: int,
) -> None:
    """Restore only stores mutated by publication, before caller releases credits."""
    arena._memo.pop(key, None)
    arena._restore_reverse(reverse_snapshot)
    if old_variants:
        arena._variants[variant_key] = old_variants
    else:
        arena._variants.pop(variant_key, None)

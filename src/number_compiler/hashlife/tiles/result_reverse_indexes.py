"""Result reference indexing owned by the completed-result arena."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.tiles.tile_result_records import (
    _ReverseHead,
    _ReverseLinks,
    _ReverseMember,
)
from number_compiler.hashlife.tiles.tile_results import (
    _MISSING,
)
from number_compiler.hashlife.tiles.tiles import TileID

if TYPE_CHECKING:
    from number_compiler.hashlife.tiles.tile_result_types import (
        ExecutionKey as _ExecutionKey,
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
    from number_compiler.hashlife.tiles.tile_results import _is_execution_key

    head_key = _ReverseHead(tile)
    previous = self._reverse.get(head_key)
    if previous is not None and not _is_execution_key(previous):
        raise ValueError("completed-result reverse head is corrupt")
    member_key = _ReverseMember(tile, key)
    if member_key in self._reverse:
        raise ValueError("completed-result reverse membership is duplicated")
    self._write_reverse(member_key, _ReverseLinks(None, previous))
    if _is_execution_key(previous):
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
    from number_compiler.hashlife.tiles.tile_results import _is_execution_key

    touched: list[_ReverseKey] = []
    for tile in tiles:
        head_key = _ReverseHead(tile)
        member_key = _ReverseMember(tile, key)
        touched.extend((head_key, member_key))
        previous = self._reverse.get(head_key)
        if _is_execution_key(previous):
            touched.append(_ReverseMember(tile, previous))
    return tuple(
        (item, self._reverse[item] if item in self._reverse else _MISSING)
        for item in dict.fromkeys(touched)
    )


def _restore_reverse(
    self: CompletedResultArena,
    snapshot: tuple[tuple[_ReverseKey, object], ...],
) -> None:
    for key, value in snapshot:
        if value is _MISSING:
            self._reverse.pop(key, None)
        else:
            self._reverse[key] = value  # type: ignore[assignment]


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
    self.ledger.bump("completed_result_reverse_index_removals", removed)

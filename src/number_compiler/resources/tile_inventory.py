"""Independent content and reference accounting for canonical future tiles."""

from __future__ import annotations

from collections.abc import Mapping

from number_compiler.hashlife.tiles.tiles import (
    TileAlphabet,
    TileAlphabetID,
    TileArena,
    TileID,
    TileRecord,
)


def audit_tiles(
    arena: TileArena,
    containers: Mapping[int, object],
) -> tuple[set[int], set[tuple[int, int]]]:
    """Read retained records without executing the tile compiler or observer."""
    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    stores = (
        (arena._alphabet_owner, arena._alphabets),
        (arena._alphabet_key_owner, arena._alphabet_keys),
        (arena._node_owner, arena._nodes),
        (arena._key_owner, arena._keys),
        (arena._ref_owner, arena._refs),
        (arena._edge_owner, arena._edges),
        (arena._lease_owner, arena._leases),
    )
    valid_owner = all(containers.get(owner) is store for owner, store in stores)
    from number_compiler.hashlife.tiles.tile_results import CompletedResultArena

    if arena._results is not None and (
        type(arena._results) is not CompletedResultArena
        or arena._results.tiles is not arena
        or arena._results.ledger is not arena.ledger
    ):
        invalid.add((arena._node_owner, id(arena._results)))
        valid_owner = False
    if any(
        type(value) is not int or value < 0
        for value in (
            arena._next_tile,
            arena._next_alphabet,
            arena._next_lease,
        )
    ):
        return approved, {(arena._node_owner, id(arena))}
    expected_refs = dict.fromkeys(arena._nodes, 0)
    expected_edges: set[tuple[int, int, int]] = set()
    expected_keys: dict[tuple[int, int, int, int, int], int] = {}

    def valid_tile(handle: object) -> bool:
        return (
            type(handle) is TileID
            and handle.owner is arena.owner
            and type(handle.kind) is str
            and handle.kind == "canonical-tile"
            and type(handle.local_id) is int
            and handle.local_id in arena._nodes
            and 0 <= handle.local_id < arena._next_tile
        )

    def exact_mirror(source: int, target: int) -> bool:
        pending = [(source, target)]
        seen: set[tuple[int, int]] = set()
        while pending:
            pair = pending.pop()
            if pair in seen:
                continue
            seen.add(pair)
            before = arena._nodes.get(pair[0])
            after = arena._nodes.get(pair[1])
            if (
                before is None
                or after is None
                or (before.alphabet != after.alphabet or before.level != after.level)
            ):
                return False
            if before.level == 0:
                if before.symbol != after.symbol:
                    return False
                continue
            if (
                before.left is None
                or before.right is None
                or after.left is None
                or after.right is None
            ):
                return False
            pending.extend(
                (
                    (before.left.local_id, after.right.local_id),
                    (before.right.local_id, after.left.local_id),
                )
            )
        return True

    for index, alphabet in arena._alphabets.items():
        valid = valid_owner and type(index) is int and 0 <= index < arena._next_alphabet
        try:
            valid &= type(alphabet) is TileAlphabet
            alphabet.__post_init__()
            valid &= arena._alphabet_keys.get(alphabet) == index
        except (TypeError, ValueError, AttributeError):
            valid = False
        if valid:
            approved.add(id(alphabet))
        else:
            invalid.add((arena._alphabet_owner, id(alphabet)))
    for alphabet_key, index in arena._alphabet_keys.items():
        if (
            type(index) is int
            and type(alphabet_key) is TileAlphabet
            and arena._alphabets.get(index) == alphabet_key
        ):
            approved.add(id(alphabet_key))
        else:
            invalid.add((arena._alphabet_key_owner, id(alphabet_key)))

    for index, record in arena._nodes.items():
        valid = valid_owner and type(index) is int and 0 <= index < arena._next_tile
        try:
            valid &= (
                type(record) is TileRecord
                and type(record.level) is int
                and record.level >= 0
            )
            alphabet_id = record.alphabet
            valid &= (
                type(alphabet_id) is TileAlphabetID
                and alphabet_id.owner is arena.owner
                and type(alphabet_id.kind) is str
                and alphabet_id.kind == "tile-alphabet"
                and type(alphabet_id.local_id) is int
            )
            alphabet = arena._alphabets[alphabet_id.local_id]
            if record.level == 0:
                if type(record.symbol) is not int:
                    raise TypeError("leaf symbol is not an exact integer")
                valid &= (
                    type(record.symbol) is int
                    and 0 <= record.symbol < alphabet.symbol_count
                    and record.left is None
                    and record.right is None
                )
                first = last = None if record.symbol == alphabet.blank else 0
                content_key = (alphabet_id.local_id, 0, record.symbol, -1, -1)
            else:
                valid &= (
                    record.symbol is None
                    and valid_tile(record.left)
                    and valid_tile(record.right)
                )
                if not valid or record.left is None or record.right is None:
                    raise ValueError("malformed child reference")
                left, right = (
                    arena._nodes[record.left.local_id],
                    arena._nodes[record.right.local_id],
                )
                valid &= (
                    left.level == record.level - 1
                    and right.level == record.level - 1
                    and left.alphabet == alphabet_id
                    and right.alphabet == alphabet_id
                )
                offset = 1 << (record.level - 1)
                first = left.first_active
                if first is None and right.first_active is not None:
                    first = offset + right.first_active
                last = left.last_active
                if right.last_active is not None:
                    last = offset + right.last_active
                content_key = (
                    alphabet_id.local_id,
                    record.level,
                    -1,
                    record.left.local_id,
                    record.right.local_id,
                )
                for side, child in enumerate((record.left, record.right)):
                    expected_refs[child.local_id] += 1
                    expected_edges.add((child.local_id, index, side))
            valid &= (
                (record.first_active is None or type(record.first_active) is int)
                and (record.last_active is None or type(record.last_active) is int)
                and record.first_active == first
                and record.last_active == last
            )
            if record.symbol is not None and type(record.symbol) is not int:
                valid = False
            if content_key in expected_keys:
                valid = False
            expected_keys[content_key] = index
        except (KeyError, TypeError, ValueError, AttributeError, OverflowError):
            valid = False
        if valid:
            approved.update((id(record), id(record.alphabet)))
            for optional_child in (record.left, record.right):
                if optional_child is not None:
                    approved.add(id(optional_child))
        else:
            invalid.add((arena._node_owner, id(record)))
    observed_content: dict[tuple[int, int, int, int, int], int] = {}
    for key, index in arena._keys.items():
        valid_key = (
            type(key) is tuple
            and len(key) == 5
            and all(type(value) is int for value in key)
            and type(index) is int
        )
        if valid_key and key == arena._mirror_key(key[1]):
            source = key[1]
            valid_key &= (
                source in arena._nodes
                and index in arena._nodes
                and arena._keys.get(arena._mirror_key(index)) == source
                and exact_mirror(source, index)
            )
        elif valid_key:
            valid_key &= expected_keys.get(key) == index
            if valid_key:
                observed_content[key] = index
        if valid_key:
            approved.add(id(key))
        else:
            invalid.add((arena._key_owner, id(key)))
    for lease_id, tile in arena._leases.items():
        if (
            type(lease_id) is int
            and 0 <= lease_id < arena._next_lease
            and valid_tile(tile)
        ):
            expected_refs[tile.local_id] += 1
            approved.add(id(tile))
        else:
            invalid.add((arena._lease_owner, id(tile)))
    for index, count in arena._refs.items():
        if (
            type(index) is not int
            or type(count) is not int
            or count < 1
            or expected_refs.get(index) != count
        ):
            invalid.add((arena._ref_owner, id(index)))
    for edge, value in arena._edges.items():
        if (
            type(edge) is tuple
            and len(edge) == 3
            and all(type(item) is int for item in edge)
            and edge in expected_edges
            and value is None
        ):
            approved.add(id(edge))
        else:
            invalid.add((arena._edge_owner, id(edge)))
    if (
        set(arena._refs) != set(expected_refs)
        or set(arena._edges) != expected_edges
        or observed_content != expected_keys
    ):
        invalid.add((arena._node_owner, id(arena._nodes)))
    if not invalid:
        approved.add(id(arena))
        approved.update(id(store) for _, store in stores)
    return approved, invalid


__all__ = ["audit_tiles"]

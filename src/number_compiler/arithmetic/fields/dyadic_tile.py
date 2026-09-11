"""Canonical coordinate-aligned dyadic tiles for HashLife projection.

The old projection carrier was a run-balanced RLE word.  Long uniform regions
were represented by ``(symbol, length)`` leaves and recursively split only as a
transient evaluation detail; concatenation then merged those children back into
one length-bearing run.  That destroys the permanent power-of-two hierarchy
HashLife relies on.

This module owns the projection-only spatial carrier.  A tile of level ``k``
always represents exactly ``2**k`` cells and is interned solely by its semantic
children (or leaf symbol).  Absolute origin, logical number width, generation,
and run length are never part of tile identity.  Exact finite words are small
forests of globally aligned tiles; geometry lives in :class:`DyadicChunk`, not
in the canonical tile key.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import count
from typing import Iterator, Sequence
from weakref import ReferenceType, WeakKeyDictionary, WeakValueDictionary, ref

from number_compiler.arithmetic.contracts.exact_tree_context import (
    exact_constructor,
    require_exact_construction,
)

_IDS = count(1)


@dataclass(frozen=True, slots=True, weakref_slot=True, eq=False)
class DyadicTile:
    node_id: int
    level: int
    symbol: int | None = None
    left: "DyadicTile | None" = None
    right: "DyadicTile | None" = None

    def __post_init__(self) -> None:
        require_exact_construction()

    @property
    def width(self) -> int:
        return 1 << self.level


@dataclass(frozen=True, slots=True)
class DyadicChunk:
    """One globally aligned tile occurrence.

    ``start`` is geometry only.  It deliberately does not participate in the
    canonical tile identity and is never used by action-cache keys.
    """

    start: int
    tile: DyadicTile

    def __post_init__(self) -> None:
        require_exact_construction()

    @property
    def end(self) -> int:
        return self.start + self.tile.width


@dataclass(frozen=True, slots=True)
class DyadicSpan:
    start: int
    length: int
    chunks: tuple[DyadicChunk, ...]

    def __post_init__(self) -> None:
        require_exact_construction()

    @property
    def end(self) -> int:
        return self.start + self.length

    @property
    def tile_ids(self) -> tuple[int, ...]:
        return tuple(chunk.tile.node_id for chunk in self.chunks)


# Immutable exact nodes are structurally shared without ownership. Live roots
# (original sources or explicitly lowered endpoints) pin their children; weak
# interning cannot keep a discarded field alive. IDs are monotone and never
# recycled, so collection cannot alias a stale integer identity.
_LEAVES: WeakValueDictionary[int, DyadicTile] = WeakValueDictionary()
_NODES: WeakValueDictionary[tuple[int, int], DyadicTile] = WeakValueDictionary()
_UNIFORM: WeakValueDictionary[tuple[int, int], DyadicTile] = WeakValueDictionary()
_MIRRORS: WeakKeyDictionary[DyadicTile, ReferenceType[DyadicTile]] = WeakKeyDictionary()


def _mirror_lookup(tile: DyadicTile) -> DyadicTile | None:
    found = _MIRRORS.get(tile)
    return None if found is None else found()


_TILE_INTERN_HITS = 0
_TILE_INTERN_MISSES = 0
_MIRROR_HITS = 0
_MIRROR_MISSES = 0


def tile_arena_metrics() -> dict[str, int]:
    nodes = tuple(_LEAVES.values()) + tuple(_NODES.values())
    node_ids = [int(node.node_id) for node in nodes]
    node_id_collisions = len(node_ids) - len(set(node_ids))
    invalid_leaf_keys = sum(
        1
        for symbol, node in _LEAVES.items()
        if node.level != 0 or node.symbol != int(symbol)
    )
    invalid_internal_keys = 0
    for key, node in _NODES.items():
        if node.left is None or node.right is None:
            invalid_internal_keys += 1
            continue
        if key != (id(node.left), id(node.right)):
            invalid_internal_keys += 1
    mirror_involution_violations = sum(
        1
        for source, target_ref in tuple(_MIRRORS.items())
        if (target := target_ref()) is not None and _mirror_lookup(target) is not source
    )
    return {
        "canonical_nodes": len(_LEAVES) + len(_NODES),
        "leaf_nodes": len(_LEAVES),
        "internal_nodes": len(_NODES),
        "uniform_entries": len(_UNIFORM),
        "mirror_entries": len(_MIRRORS),
        "intern_hits": _TILE_INTERN_HITS,
        "intern_misses": _TILE_INTERN_MISSES,
        "mirror_hits": _MIRROR_HITS,
        "mirror_misses": _MIRROR_MISSES,
        "node_id_collisions": node_id_collisions,
        "invalid_intern_entries": invalid_leaf_keys + invalid_internal_keys,
        "mirror_involution_violations": mirror_involution_violations,
    }


@exact_constructor
def leaf(symbol: int) -> DyadicTile:
    global _TILE_INTERN_HITS, _TILE_INTERN_MISSES
    symbol = int(symbol)
    found = _LEAVES.get(symbol)
    if found is not None:
        _TILE_INTERN_HITS += 1
        return found
    _TILE_INTERN_MISSES += 1
    out = DyadicTile(next(_IDS), 0, symbol=symbol)
    _LEAVES[symbol] = out
    _UNIFORM[(symbol, 0)] = out
    return out


@exact_constructor
def join(left: DyadicTile, right: DyadicTile) -> DyadicTile:
    """Intern one aligned parent without collapsing equal children."""
    global _TILE_INTERN_HITS, _TILE_INTERN_MISSES
    if left.level != right.level:
        raise ValueError((left.level, right.level))
    key = (id(left), id(right))
    found = _NODES.get(key)
    if found is not None:
        _TILE_INTERN_HITS += 1
        return found
    _TILE_INTERN_MISSES += 1
    uniform_symbol = (
        int(left.symbol) if left is right and left.symbol is not None else None
    )
    out = DyadicTile(
        next(_IDS), left.level + 1, symbol=uniform_symbol, left=left, right=right
    )
    _NODES[key] = out
    if uniform_symbol is not None:
        _UNIFORM[(uniform_symbol, out.level)] = out
    return out


def existing_join(left: DyadicTile, right: DyadicTile) -> DyadicTile | None:
    """Return an already-interned exact parent without constructing a new tile."""
    if (
        type(left) is not DyadicTile
        or type(right) is not DyadicTile
        or left.level != right.level
    ):
        raise ValueError("existing parent lookup requires equal-level exact tiles")
    return _NODES.get((id(left), id(right)))


@exact_constructor
def uniform(symbol: int, level: int) -> DyadicTile:
    """Return the unique recursive ``symbol`` tile at ``level`` iteratively."""
    symbol, level = int(symbol), int(level)
    if level < 0:
        raise ValueError(level)
    found = _UNIFORM.get((symbol, level))
    if found is not None:
        return found
    current = leaf(symbol)
    current_level = 0
    while current_level < level:
        current_level += 1
        found = _UNIFORM.get((symbol, current_level))
        if found is not None:
            current = found
            continue
        current = join(current, current)
        _UNIFORM[(symbol, current_level)] = current
    return current


def _append_aligned(chunks: list[DyadicChunk], chunk: DyadicChunk) -> None:
    """Append a chunk and merge only true globally aligned siblings."""
    chunks.append(chunk)
    while len(chunks) >= 2:
        right = chunks[-1]
        left = chunks[-2]
        if left.tile.level != right.tile.level or left.end != right.start:
            return
        width = left.tile.width
        if left.start % (2 * width):
            return
        chunks.pop()
        chunks.pop()
        chunks.append(DyadicChunk(left.start, join(left.tile, right.tile)))


def _blank_chunks(start: int, end: int, symbol: int) -> tuple[DyadicChunk, ...]:
    """Cover ``[start,end)`` by the minimum aligned dyadic blank forest."""
    start, end, symbol = int(start), int(end), int(symbol)
    if start < 0 or end < start:
        raise ValueError((start, end))
    out: list[DyadicChunk] = []
    position = start
    while position < end:
        remaining = end - position
        max_level = remaining.bit_length() - 1
        if position:
            align_level = (position & -position).bit_length() - 1
            level = min(max_level, align_level)
        else:
            level = max_level
        _append_aligned(out, DyadicChunk(position, uniform(symbol, level)))
        position += 1 << level
    return tuple(out)


@exact_constructor
def source_span(
    values: Sequence[int], *, blank: int, logical_length: int
) -> DyadicSpan:
    """Build a finite source prefix plus canonical blank exterior inside its bound.

    ``logical_length`` is geometry, not tile state.  The blank suffix is covered
    by aligned power-of-two nodes rather than by a length-bearing run leaf.
    """
    values = tuple(map(int, values))
    blank = int(blank)
    logical_length = int(logical_length)
    if not values or logical_length < len(values):
        raise ValueError((len(values), logical_length))
    chunks: list[DyadicChunk] = []
    for position, value in enumerate(values):
        _append_aligned(chunks, DyadicChunk(position, leaf(value)))
    for chunk in _blank_chunks(len(values), logical_length, blank):
        _append_aligned(chunks, chunk)
    return DyadicSpan(0, logical_length, tuple(chunks))


@exact_constructor
def uniform_span(start: int, length: int, symbol: int) -> DyadicSpan:
    """Return an exact uniform interval using only aligned dyadic geometry.

    The represented length is geometry, never a leaf payload.  Construction
    creates at most ``2*bit_length(length)+1`` forest chunks and therefore does
    not materialize one cell per represented position.
    """
    start, length, symbol = int(start), int(length), int(symbol)
    if start < 0 or length < 0:
        raise ValueError((start, length))
    return DyadicSpan(start, length, _blank_chunks(start, start + length, symbol))


@exact_constructor
def prefix_domain_span(
    active_length: int,
    logical_length: int,
    *,
    active_symbol: int = 1,
    inactive_symbol: int = 0,
) -> DyadicSpan:
    """Canonical active-prefix geometry without a length-bearing cell state.

    ``[0, active_length)`` is represented by ``active_symbol`` and the padded
    exterior by ``inactive_symbol``.  Absolute extent is stored only in the
    :class:`DyadicSpan` geometry; every leaf remains drawn from the fixed two
    symbol alphabet.
    """
    active_length, logical_length = int(active_length), int(logical_length)
    active_symbol, inactive_symbol = int(active_symbol), int(inactive_symbol)
    if not 0 <= active_length <= logical_length:
        raise ValueError((active_length, logical_length))
    chunks: list[DyadicChunk] = []
    for chunk in _blank_chunks(0, active_length, active_symbol):
        _append_aligned(chunks, chunk)
    for chunk in _blank_chunks(active_length, logical_length, inactive_symbol):
        _append_aligned(chunks, chunk)
    return DyadicSpan(0, logical_length, tuple(chunks))


@exact_constructor
def rebase(span: DyadicSpan, start: int = 0) -> DyadicSpan:
    """Translate occurrence geometry while retaining every canonical tile ID."""
    start = int(start)
    delta = start - span.start
    return DyadicSpan(
        start,
        span.length,
        tuple(DyadicChunk(chunk.start + delta, chunk.tile) for chunk in span.chunks),
    )


@exact_constructor
def concat(left: DyadicSpan, right: DyadicSpan) -> DyadicSpan:
    """Concatenate contiguous spans and preserve aligned canonical merging."""
    if left.end != right.start:
        raise ValueError((left.end, right.start))
    chunks: list[DyadicChunk] = []
    for chunk in (*left.chunks, *right.chunks):
        _append_aligned(chunks, chunk)
    return DyadicSpan(left.start, left.length + right.length, tuple(chunks))


@exact_constructor
def append_symbol(span: DyadicSpan, symbol: int) -> DyadicSpan:
    """Append one cell as geometry; canonical parents are merged when aligned."""
    return concat(
        span,
        DyadicSpan(span.end, 1, (DyadicChunk(span.end, leaf(int(symbol))),)),
    )


@exact_constructor
def slice_span(
    span: DyadicSpan, start: int, end: int, *, rebase_to_zero: bool = False
) -> DyadicSpan:
    """Return ``[start,end)`` without expanding canonical tiles."""
    start, end = int(start), int(end)
    if not span.start <= start <= end <= span.end:
        raise IndexError((start, end, span.start, span.end))
    _before, tail = split(span, start)
    middle, _after = split(tail, end)
    return rebase(middle, 0) if rebase_to_zero else middle


def first_symbol(tile: DyadicTile) -> int:
    """Return the least-significant/leftmost symbol in O(level) time."""
    current = tile
    while current.level:
        if current.left is None:
            raise AssertionError(current)
        current = current.left
    if current.symbol is None:
        raise AssertionError(current)
    return int(current.symbol)


def last_symbol(tile: DyadicTile) -> int:
    """Return the most-significant/rightmost symbol in O(level) time."""
    current = tile
    while current.level:
        if current.right is None:
            raise AssertionError(current)
        current = current.right
    if current.symbol is None:
        raise AssertionError(current)
    return int(current.symbol)


@exact_constructor
def mirror_tile(tile: DyadicTile) -> DyadicTile:
    """Return the exact left/right reflection of one canonical tile.

    Reflection is itself a canonical quadtree action.  Cache it at the tile
    layer so repeated RIGHT scans do not rebuild the same reflected subtree.
    """
    global _MIRROR_HITS, _MIRROR_MISSES
    found = _mirror_lookup(tile)
    if found is not None:
        _MIRROR_HITS += 1
        return found
    _MIRROR_MISSES += 1
    if tile.level == 0:
        _MIRRORS[tile] = ref(tile)
        return tile
    built: dict[DyadicTile, DyadicTile] = {}
    stack: list[tuple[DyadicTile, bool]] = [(tile, False)]
    while stack:
        node, ready = stack.pop()
        if node in built:
            continue
        if node.level == 0:
            built[node] = node
            continue
        if node.left is None or node.right is None:
            raise AssertionError(node)
        if not ready:
            stack.append((node, True))
            if node.left not in built:
                stack.append((node.left, False))
            if node.right not in built:
                stack.append((node.right, False))
            continue
        built[node] = join(built[node.right], built[node.left])
    out = built[tile]
    _MIRRORS[tile] = ref(out)
    _MIRRORS[out] = ref(tile)
    return out


def _place_tile_aligned(
    chunks: list[DyadicChunk], start: int, tile: DyadicTile
) -> None:
    """Place ``tile`` at ``start`` with iterative alignment splitting.

    A reflected forest can move a power-of-two tile to a start that is not
    globally aligned for that level.  Tile *content* remains canonical, but the
    occurrence must be split until every emitted chunk satisfies the global
    alignment invariant used by :func:`split`.
    """
    pending: list[tuple[int, DyadicTile]] = [(int(start), tile)]
    while pending:
        position, node = pending.pop()
        if position % node.width == 0:
            _append_aligned(chunks, DyadicChunk(position, node))
            continue
        if node.level == 0 or node.left is None or node.right is None:
            raise AssertionError((position, node))
        half = node.left.width
        # Stack is LIFO: push the higher/right occurrence first so emitted
        # chunks remain in increasing coordinate order.
        pending.append((position + half, node.right))
        pending.append((position, node.left))


@exact_constructor
def align_span(span: DyadicSpan, start: int = 0) -> DyadicSpan:
    """Repack a span at ``start`` into canonical globally aligned geometry.

    Cropping or translating a valid forest can move an existing tile to an
    occurrence that is not aligned for its level.  Semantic content is still
    exact, but using that inherited forest shape as a cache key would preserve
    coordinate provenance.  This operation splits only misaligned occurrences
    and then rejoins true aligned siblings, without flattening leaves.
    """
    start = int(start)
    if start < 0:
        raise ValueError(start)
    chunks: list[DyadicChunk] = []
    cursor = start
    for chunk in span.chunks:
        _place_tile_aligned(chunks, cursor, chunk.tile)
        cursor += chunk.tile.width
    if cursor != start + span.length:
        raise AssertionError((cursor, start, span.length))
    return DyadicSpan(start, span.length, tuple(chunks))


@exact_constructor
def mirror_span(span: DyadicSpan, *, rebase_to_zero: bool = False) -> DyadicSpan:
    """Reflect a finite span without materializing its leaf word.

    The reflected occurrence is repacked into globally aligned dyadic chunks;
    absolute length stays in geometry and no leaf receives a position/length
    tag.
    """
    out_start = 0 if rebase_to_zero else span.start
    chunks: list[DyadicChunk] = []
    cursor = out_start
    for chunk in reversed(span.chunks):
        reflected = mirror_tile(chunk.tile)
        _place_tile_aligned(chunks, cursor, reflected)
        cursor += reflected.width
    if cursor != out_start + span.length:
        raise AssertionError((cursor, out_start, span.length))
    return DyadicSpan(out_start, span.length, tuple(chunks))


def symbol_at(span: DyadicSpan, position: int) -> int:
    """Return one symbol in O(forest + level) time without splitting the span."""
    position = int(position)
    if not span.start <= position < span.end:
        raise IndexError(position)
    for chunk in span.chunks:
        if not chunk.start <= position < chunk.end:
            continue
        node = chunk.tile
        offset = position - chunk.start
        while node.level:
            if node.left is None or node.right is None:
                raise AssertionError(node)
            left, right = node.left, node.right
            half = left.width
            if offset < half:
                node = left
            else:
                offset -= half
                node = right
        if node.symbol is None:
            raise AssertionError(node)
        return int(node.symbol)
    raise AssertionError((span, position))


def tile_at(span: DyadicSpan, start: int, level: int) -> DyadicTile:
    """Return the canonical tile for one power-of-two subinterval iteratively.

    The requested interval need not coincide with the source forest's chunk
    boundaries.  A postorder stack splits only crossing intervals; leaves are
    never flattened into a positional vector.
    """
    start, level = int(start), int(level)
    if level < 0:
        raise ValueError(level)
    width = 1 << level
    if not span.start <= start or start + width > span.end:
        raise IndexError((start, level, span.start, span.end))

    exact = {(chunk.start, chunk.tile.level): chunk.tile for chunk in span.chunks}
    built: dict[tuple[int, int], DyadicTile] = {}
    tasks: list[tuple[int, int, bool]] = [(start, level, False)]
    while tasks:
        position, current_level, ready = tasks.pop()
        key = (position, current_level)
        if key in built:
            continue
        found = exact.get(key)
        if found is not None:
            built[key] = found
            continue
        if current_level == 0:
            built[key] = leaf(symbol_at(span, position))
            continue
        half = 1 << (current_level - 1)
        left_key = (position, current_level - 1)
        right_key = (position + half, current_level - 1)
        if not ready:
            tasks.append((position, current_level, True))
            if right_key not in built:
                tasks.append((right_key[0], right_key[1], False))
            if left_key not in built:
                tasks.append((left_key[0], left_key[1], False))
            continue
        left = built.get(left_key)
        right = built.get(right_key)
        if left is None or right is None:
            raise AssertionError((key, left_key, right_key))
        built[key] = join(left, right)
    return built[(start, level)]


@exact_constructor
def retile_like(reference: DyadicSpan, source: DyadicSpan) -> DyadicSpan:
    """Represent ``source`` using exactly ``reference`` occurrence geometry."""
    if (reference.start, reference.length) != (source.start, source.length):
        raise ValueError(
            (reference.start, reference.length, source.start, source.length)
        )
    return DyadicSpan(
        reference.start,
        reference.length,
        tuple(
            DyadicChunk(chunk.start, tile_at(source, chunk.start, chunk.tile.level))
            for chunk in reference.chunks
        ),
    )


@exact_constructor
def prepend_symbol(span: DyadicSpan, symbol: int) -> DyadicSpan:
    """Prepend one cell while preserving canonical geometry."""
    shifted = rebase(span, span.start + 1)
    head = DyadicSpan(span.start, 1, (DyadicChunk(span.start, leaf(int(symbol))),))
    return concat(head, shifted)


@exact_constructor
def empty_span(position: int) -> DyadicSpan:
    position = int(position)
    return DyadicSpan(position, 0, ())


def _split_chunk(
    chunk: DyadicChunk, position: int
) -> tuple[list[DyadicChunk], list[DyadicChunk]]:
    """Split one aligned chunk at an interior absolute position iteratively."""
    position = int(position)
    if not chunk.start < position < chunk.end:
        raise ValueError((chunk.start, position, chunk.end))
    left_parts: list[DyadicChunk] = []
    right_parts: list[DyadicChunk] = []
    current = chunk
    while current.tile.level:
        tile = current.tile
        if tile.left is None or tile.right is None:
            raise AssertionError(tile)
        half = tile.left.width
        middle = current.start + half
        left_chunk = DyadicChunk(current.start, tile.left)
        right_chunk = DyadicChunk(middle, tile.right)
        if position < middle:
            right_parts.append(right_chunk)
            current = left_chunk
        elif position > middle:
            left_parts.append(left_chunk)
            current = right_chunk
        else:
            left_parts.append(left_chunk)
            right_parts.append(right_chunk)
            break
    else:
        raise AssertionError("interior split reached a leaf")
    left_parts.sort(key=lambda item: item.start)
    right_parts.sort(key=lambda item: item.start)
    return left_parts, right_parts


@exact_constructor
def split(span: DyadicSpan, position: int) -> tuple[DyadicSpan, DyadicSpan]:
    """Split a span at an absolute position while preserving global alignment."""
    position = int(position)
    if not span.start <= position <= span.end:
        raise IndexError(position)
    if position == span.start:
        return empty_span(span.start), span
    if position == span.end:
        return span, empty_span(span.end)
    left: list[DyadicChunk] = []
    right: list[DyadicChunk] = []
    for chunk in span.chunks:
        if chunk.end <= position:
            left.append(chunk)
        elif chunk.start >= position:
            right.append(chunk)
        else:
            a, b = _split_chunk(chunk, position)
            left.extend(a)
            right.extend(b)
    left_span = DyadicSpan(span.start, position - span.start, tuple(left))
    right_span = DyadicSpan(position, span.end - position, tuple(right))
    if sum(chunk.tile.width for chunk in left_span.chunks) != left_span.length:
        raise AssertionError(left_span)
    if sum(chunk.tile.width for chunk in right_span.chunks) != right_span.length:
        raise AssertionError(right_span)
    return left_span, right_span


def one_symbol(span: DyadicSpan) -> int:
    if span.length != 1 or len(span.chunks) != 1:
        raise ValueError((span.length, len(span.chunks)))
    tile = span.chunks[0].tile
    if tile.level != 0 or tile.symbol is None:
        raise AssertionError(tile)
    return int(tile.symbol)


def iter_symbols(span: DyadicSpan) -> Iterator[int]:
    """Stream a span left-to-right without recursive calls."""
    stack = [chunk.tile for chunk in reversed(span.chunks)]
    while stack:
        tile = stack.pop()
        if tile.level == 0:
            if tile.symbol is None:
                raise AssertionError(tile)
            yield int(tile.symbol)
            continue
        if tile.left is None or tile.right is None:
            raise AssertionError(tile)
        stack.append(tile.right)
        stack.append(tile.left)


def tile_metrics(span: DyadicSpan) -> dict[str, int]:
    seen: set[DyadicTile] = set()
    stack = [chunk.tile for chunk in span.chunks]
    max_level = 0
    while stack:
        tile = stack.pop()
        if tile in seen:
            continue
        seen.add(tile)
        max_level = max(max_level, tile.level)
        if tile.left is not None:
            stack.append(tile.left)
        if tile.right is not None:
            stack.append(tile.right)
    return {
        "logical_length": span.length,
        "forest_chunks": len(span.chunks),
        "unique_tiles": len(seen),
        "max_level": max_level,
    }


__all__ = [
    "DyadicTile",
    "DyadicChunk",
    "DyadicSpan",
    "leaf",
    "join",
    "uniform",
    "source_span",
    "uniform_span",
    "prefix_domain_span",
    "rebase",
    "concat",
    "append_symbol",
    "slice_span",
    "first_symbol",
    "last_symbol",
    "mirror_tile",
    "align_span",
    "mirror_span",
    "symbol_at",
    "tile_at",
    "retile_like",
    "prepend_symbol",
    "empty_span",
    "split",
    "one_symbol",
    "iter_symbols",
    "tile_metrics",
]

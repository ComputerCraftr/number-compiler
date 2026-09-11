"""Ledger-owned references to weakly shared immutable source geometry."""

from __future__ import annotations

from collections.abc import MutableMapping, MutableSequence, Sequence

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.exact_tree_context import (
    OriginalSourceConstruction,
    exact_constructor,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ArenaHandle,
    ArenaToken,
    ExactSource,
)
from number_compiler.arithmetic.fields.dyadic_tile import (
    DyadicChunk,
    DyadicSpan,
    DyadicTile,
    join,
    leaf,
)
from number_compiler.resources.ledger import ResourceLedger


class SourceGeometry:
    """Only caller supplied symbols and their blank exterior enter this arena."""

    def __init__(
        self,
        ledger: ResourceLedger,
        source: ExactSource,
        construction: OriginalSourceConstruction | None = None,
    ) -> None:
        if type(source) is not ExactSource:
            raise TypeError("source geometry requires an immutable exact source")
        source.__post_init__()
        if construction is not None:
            OriginalSourceConstruction.validate_source(construction, source)
        self._construction = (
            OriginalSourceConstruction(source) if construction is None else construction
        )
        self.ledger = ledger
        ledger.register_execution_root(self)
        self.token = ArenaToken("source-geometry")
        prefix = f"source-geometry-{len(ledger.inventory())}"
        self.owner = ledger.register(prefix + "-nodes", "exact_source", "INDEX_OWNED")
        self.nodes: MutableMapping[tuple[int, ...], DyadicTile] = ledger.make_dict(
            self.owner, nodes_per_entry=1
        )
        self.source_owner = ledger.register(
            prefix + "-source-record", "exact_source", "INDEX_OWNED"
        )
        self._sources: MutableSequence[ExactSource] = ledger.make_list(
            self.source_owner
        )
        ledger.reserve(self.source_owner, entries=1, nodes=1)
        self._sources.append(self._construction.source)
        self._read_root: DyadicSpan | None = None

    @exact_constructor
    def _leaf(self, symbol: int) -> DyadicTile:
        if type(symbol) is not int or symbol < 0:
            raise ValueError("source symbol must be a nonnegative integer")
        self.ledger.bump("source_leaf_interner_requests")
        key = (symbol,)
        found = self.nodes.get(key)
        if found is not None:
            self.ledger.bump("source_leaf_interner_hits")
            return found
        self.ledger.bump("source_leaf_interner_evaluations")
        try:
            self.ledger.reserve(self.owner, entries=1, nodes=1)
        except BlockContextBudgetExceeded:
            self.ledger.bump("source_leaf_publication_rejections")
            raise
        node = leaf(symbol)
        self.nodes[key] = node
        return node

    @exact_constructor
    def _join(self, left: DyadicTile, right: DyadicTile) -> DyadicTile:
        if (
            type(left) is not DyadicTile
            or type(right) is not DyadicTile
            or left.level != right.level
        ):
            raise ValueError("source parents require equally sized source tiles")
        self.ledger.bump("source_parent_interner_requests")
        key = (left.node_id, right.node_id)
        found = self.nodes.get(key)
        if found is not None:
            self.ledger.bump("source_parent_interner_hits")
            return found
        self.ledger.bump("source_parent_interner_evaluations")
        try:
            self.ledger.reserve(self.owner, entries=1, nodes=1)
        except BlockContextBudgetExceeded:
            self.ledger.bump("source_parent_publication_rejections")
            raise
        node = join(left, right)
        self.nodes[key] = node
        return node

    def _append(self, chunks: list[DyadicChunk], start: int, tile: DyadicTile) -> None:
        chunks.append(DyadicChunk(start, tile))
        while len(chunks) >= 2:
            left, right = chunks[-2:]
            if (
                left.end != right.start
                or left.tile.level != right.tile.level
                or left.start % (left.tile.width * 2)
            ):
                break
            parent = self._join(left.tile, right.tile)
            chunks[-2:] = [DyadicChunk(left.start, parent)]

    def span(self, source: Sequence[int], blank: int, length: int) -> DyadicSpan:
        values = tuple(source)
        result = self._construction.construct(self, values, blank, length)
        self._read_root = result
        return result

    def tile_at(self, start: int, level: int) -> DyadicTile | None:
        """Find an existing source subtree; never construct a query tile."""
        if type(start) is not int or type(level) is not int:
            raise TypeError("source tile coordinates must be integers")
        if level < 0 or start < 0:
            return None
        root = self._read_root
        if root is None or start >= root.end:
            return None
        # Bound the exponent using existing geometry before constructing its
        # power of two. Even a rejected query must not allocate a huge integer.
        if level >= (root.end - start).bit_length():
            return None
        width = 1 << level
        if start % width:
            return None
        self.ledger.bump("source_tile_lookup_requests")
        for chunk in root.chunks:
            self.ledger.bump("source_chunk_visits")
            if not chunk.start <= start < chunk.end:
                continue
            node, origin = chunk.tile, chunk.start
            if node.level < level or start + width > chunk.end:
                return None
            while node.level > level:
                self.ledger.bump("source_tile_node_visits")
                left, right = node.left, node.right
                if left is None or right is None:
                    raise AssertionError("source parent has no children")
                middle = origin + left.width
                if start < middle:
                    node = left
                else:
                    node, origin = right, middle
            self.ledger.bump("source_tile_lookup_hits")
            return node
        return None

    def range_tiles(self, start: int, end: int) -> tuple[DyadicTile, ...]:
        """Return a left-to-right dyadic cover using only existing source nodes."""
        if any(type(value) is not int for value in (start, end)):
            raise TypeError("source range coordinates must be integers")
        root = self._read_root
        if root is None or not 0 <= start <= end <= root.end:
            raise ValueError("source range is outside retained geometry")
        out: list[DyadicTile] = []
        position = start
        while position < end:
            remaining = end - position
            level = remaining.bit_length() - 1
            if position:
                level = min(level, (position & -position).bit_length() - 1)
            tile = self.tile_at(position, level)
            while tile is None and level:
                level -= 1
                tile = self.tile_at(position, level)
            if tile is None:
                raise AssertionError((position, level))
            out.append(tile)
            position += tile.width
        return tuple(out)

    def read(self, position: int) -> int:
        """Read one original symbol through the retained spatial DAG."""
        node = self.tile_at(position, 0)
        if node is None or node.symbol is None:
            raise IndexError(position)
        self.ledger.bump("source_leaf_reads")
        return node.symbol

    def existing_parent(
        self, left_id: int, right_id: int
    ) -> tuple[int, DyadicTile] | None:
        """Find an original parent by child identity, independent of occurrence.

        Shared child tiles may each have an earlier representative at unrelated
        coordinates. Search the existing source DAG for a parent occurrence;
        neither this lookup nor its geometry traversal constructs an exact tile.
        """
        if any(type(value) is not int or value < 0 for value in (left_id, right_id)):
            raise ValueError("original child identities must be nonnegative integers")
        self.ledger.bump("source_parent_lookup_requests")
        parent = self.nodes.get((left_id, right_id))
        root = self._read_root
        if parent is None or root is None:
            return None
        pending = [(chunk.start, chunk.tile) for chunk in reversed(root.chunks)]
        seen: set[int] = set()
        while pending:
            peak = self.ledger.counters.get("source_origin_stack_peak", 0)
            self.ledger.bump("source_origin_stack_peak", max(0, len(pending) - peak))
            workspace = len(pending) + len(seen)
            peak = self.ledger.counters.get("source_origin_workspace_peak", 0)
            self.ledger.bump("source_origin_workspace_peak", max(0, workspace - peak))
            start, tile = pending.pop()
            self.ledger.bump("source_origin_frame_visits")
            if tile.node_id in seen:
                continue
            seen.add(tile.node_id)
            self.ledger.bump("source_origin_node_visits")
            if tile.node_id == parent.node_id:
                return start, tile
            if tile.level <= parent.level:
                continue
            left, right = tile.left, tile.right
            if left is None or right is None:
                raise AssertionError("source parent has no children")
            pending.extend(((start + left.width, right), (start, left)))
        return None

    def require_source(self, source: Sequence[int], blank: int) -> None:
        """Reject a same-ledger tree belonging to a different original input."""
        original = self._construction.source
        values = tuple(source)
        if type(blank) is not int or any(type(value) is not int for value in values):
            raise TypeError("source symbols and blank must be integers")
        if (
            values != original.digits
            or blank != original.blank
            or self._read_root is None
        ):
            raise ValueError("source geometry does not describe this original input")

    @exact_constructor
    def _source_span(
        self, source: Sequence[int], blank: int, length: int
    ) -> DyadicSpan:
        if not source or length < len(source):
            raise ValueError("invalid source extent")
        chunks: list[DyadicChunk] = []
        for position, symbol in enumerate(source):
            self._append(chunks, position, self._leaf(symbol))
        position = len(source)
        while position < length:
            level = min(
                (length - position).bit_length() - 1,
                (position & -position).bit_length() - 1,
            )
            tile = self._leaf(blank)
            for _ in range(level):
                tile = self._join(tile, tile)
            self._append(chunks, position, tile)
            position += 1 << level
        for chunk in chunks:
            self.ledger.register_root(
                self.owner, ArenaHandle(self.token, "source-tile", chunk.tile.node_id)
            )
        return DyadicSpan(0, length, tuple(chunks))

"""Constant-size exact boundary operands for canonical tile execution."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.hashlife.tiles.tiles import (
    TileAlphabetID,
    TileArena,
    TileID,
    TileLease,
)
from number_compiler.resources.metric_keys import (
    hashlife_tiles as _tiles_keys,
)


@dataclass(frozen=True, slots=True)
class BoundaryTileView:
    """One oriented exact tile view with relative occurrence metadata."""

    tile: TileID
    relative_origin: int = 0
    relative_extent: int = 0
    orientation: int = 0
    source_offset: int = 0

    def __post_init__(self) -> None:
        if type(self.tile) is not TileID:
            raise TypeError("boundary view requires a scoped tile ID")
        if type(self.relative_origin) is not int:
            raise TypeError("boundary origin requires an exact integer")
        if type(self.relative_extent) is not int:
            raise TypeError("boundary extent requires an exact integer")
        if self.relative_extent < 0:
            raise ValueError("boundary extent cannot be negative")
        if type(self.orientation) is not int or self.orientation not in (0, 1):
            raise ValueError("boundary orientation must be zero or one")
        if type(self.source_offset) is not int:
            raise TypeError("boundary source offset requires an exact integer")
        if self.source_offset < 0:
            raise ValueError("boundary source offset cannot be negative")


@dataclass(frozen=True, slots=True)
class BoundaryTileOperands:
    """The fixed left/right exact operands of one bounded interface."""

    left: BoundaryTileView | None = None
    right: BoundaryTileView | None = None

    def __post_init__(self) -> None:
        for value in (self.left, self.right):
            if value is not None and type(value) is not BoundaryTileView:
                raise TypeError("boundary operands require exact boundary views")
            if value is not None:
                value.__post_init__()

    def tile_ids(self) -> tuple[TileID, ...]:
        """Return referenced tiles in deterministic side order."""
        return tuple(
            value.tile for value in (self.left, self.right) if value is not None
        )


EMPTY_BOUNDARY_TILES = BoundaryTileOperands()


def validate_boundary_shape(value: BoundaryTileOperands) -> None:
    """Validate the constant-size operand shape before any arena lookup."""
    if type(value) is not BoundaryTileOperands:
        raise TypeError("boundary operands require an exact fixed pair")
    value.__post_init__()


def boundary_dyadic_pieces(
    tiles: TileArena,
    view: BoundaryTileView,
) -> tuple[BoundaryTileView, ...]:
    """Cover a clipped view by maximal canonical children in logical order.

    This is spatial scheduler workspace, with at most two pieces per tree
    level. It neither emits symbols nor turns backing padding into input.
    The caller must keep the original view leased while using these children.
    """
    from number_compiler.hashlife.tiles.tile_result_validation import (
        validate_boundary_operands,
    )

    validate_boundary_operands(tiles, BoundaryTileOperands(view))
    start, stop = view.source_offset, view.source_offset + view.relative_extent
    pending = [(view.tile, 0)]
    pieces: list[BoundaryTileView] = []
    while pending:
        current, origin = pending.pop()
        node = tiles.resolve(current)
        end = origin + node.width
        tiles.ledger.bump(_tiles_keys.TILE_BOUNDARY_COVER_FRAMES)
        if end <= start or origin >= stop:
            continue
        if start <= origin and end <= stop:
            logical = stop - end if view.orientation else origin - start
            pieces.append(
                BoundaryTileView(
                    current,
                    view.relative_origin + logical,
                    node.width,
                    view.orientation,
                )
            )
            continue
        if node.left is None or node.right is None:
            raise ValueError("clipped causal view has a malformed parent")
        left, right = (node.left, origin), (node.right, origin + node.width // 2)
        pending.extend((left, right) if view.orientation else (right, left))
    return tuple(pieces)


def normalize_boundary_view(
    tiles: TileArena,
    view: BoundaryTileView,
) -> tuple[BoundaryTileView, TileLease]:
    """Return one canonical forward tile for the exact logical view.

    The normalized view has no dependence on the larger tile that happened to
    back the clip.  This makes two equal causal regions use the same transient
    task identity before a scheduler memo probe.  Construction stays spatial:
    maximal canonical children are joined without emitting a flat boundary
    word, and the returned lease owns the resulting exact tile.
    """
    from number_compiler.hashlife.tiles.tile_result_validation import (
        validate_boundary_operands,
    )

    validate_boundary_operands(tiles, BoundaryTileOperands(view))
    source = tiles.resolve(view.tile)
    if view.relative_extent == source.width and not view.source_offset:
        result = (
            tiles.mirror(view.tile) if view.orientation else tiles.retain(view.tile)
        )
        normalized = BoundaryTileView(
            result.tile,
            view.relative_origin,
            view.relative_extent,
        )
        tiles.ledger.bump(_tiles_keys.TILE_BOUNDARY_REGION_NORMALIZATION_REQUESTS)
        if normalized != view:
            tiles.ledger.bump(_tiles_keys.TILE_BOUNDARY_REGION_NORMALIZATION_ALIASES)
        return normalized, result
    pieces = boundary_dyadic_pieces(tiles, view)
    if not pieces:
        raise ValueError("causal boundary normalization requires a nonempty view")
    current: BoundaryTileView | None = None
    current_lease: TileLease | None = None
    try:
        for piece in pieces:
            piece_lease = (
                tiles.mirror(piece.tile)
                if piece.orientation
                else tiles.retain(piece.tile)
            )
            try:
                node = tiles.resolve(piece_lease.tile)
                merged, merged_lease = concat_boundary_views(
                    tiles,
                    node.alphabet,
                    current,
                    BoundaryTileView(piece_lease.tile, 0, node.width),
                )
            finally:
                piece_lease.close()
            if merged is None or merged_lease is None:
                raise AssertionError("causal boundary normalization lost its content")
            if current_lease is not None:
                current_lease.close()
            current, current_lease = merged, merged_lease
        if current is None or current_lease is None:
            raise AssertionError("causal boundary normalization produced no content")
        normalized = BoundaryTileView(
            current.tile,
            view.relative_origin,
            view.relative_extent,
            0,
            0,
        )
        result = current_lease
        current_lease = None
        tiles.ledger.bump(_tiles_keys.TILE_BOUNDARY_REGION_NORMALIZATION_REQUESTS)
        if normalized != view:
            tiles.ledger.bump(_tiles_keys.TILE_BOUNDARY_REGION_NORMALIZATION_ALIASES)
        return normalized, result
    finally:
        if current_lease is not None:
            current_lease.close()


def _extend_in_backing(
    tiles: TileArena,
    first: BoundaryTileView,
    second: BoundaryTileView,
) -> BoundaryTileView | None:
    """Reuse an already present adjacent child without rebuilding a prefix.

    Spatial descent compares canonical child IDs, never symbols.  Restricting
    this rule to aligned complete children makes both the proof and failed
    probe logarithmic.  Existing input/output content is retained, not emitted.
    """
    if (
        first.orientation
        or second.orientation
        or first.source_offset
        or second.source_offset
    ):
        return None
    parent = tiles.resolve(first.tile)
    suffix = tiles.resolve(second.tile)
    offset = first.relative_extent
    if (
        suffix.width != second.relative_extent
        or offset % suffix.width
        or offset + suffix.width > parent.width
    ):
        return None
    current = first.tile
    while parent.level > suffix.level:
        if parent.left is None or parent.right is None:
            raise ValueError("malformed causal prefix backing")
        half = parent.width // 2
        current = parent.right if offset >= half else parent.left
        if offset >= half:
            offset -= half
        parent = tiles.resolve(current)
        tiles.ledger.bump(_tiles_keys.TILE_BOUNDARY_CONCAT_CHILD_VISITS)
    if current != second.tile:
        return None
    return BoundaryTileView(
        first.tile, 0, first.relative_extent + second.relative_extent
    )


def concat_boundary_views(
    tiles: TileArena,
    alphabet: TileAlphabetID,
    first: BoundaryTileView | None,
    second: BoundaryTileView | None,
) -> tuple[BoundaryTileView | None, TileLease | None]:
    """Concatenate exact causal operands by reusing covered canonical children.

    Only the returned view's logical extent is consumed by a transfer. The
    dyadic backing's uncovered suffix is shared alphabet padding, not computed
    future output. No symbols are copied into a word or a boundary history.
    """
    from number_compiler.hashlife.tiles.tile_result_validation import (
        validate_boundary_operands,
    )

    validate_boundary_operands(
        tiles,
        BoundaryTileOperands(first, second),
        expected_alphabet=alphabet,
    )
    views = tuple(
        view for view in (first, second) if view is not None and view.relative_extent
    )
    if not views:
        return None, None
    tiles.ledger.bump(_tiles_keys.TILE_BOUNDARY_CONCAT_REQUESTS)
    if len(views) == 1:
        view = views[0]
        return view, tiles.retain(view.tile)
    a, b = views
    total = a.relative_extent + b.relative_extent
    if (
        a.tile == b.tile
        and a.orientation == b.orientation
        and (
            (
                not a.orientation
                and a.source_offset + a.relative_extent == b.source_offset
            )
            or (
                a.orientation and b.source_offset + b.relative_extent == a.source_offset
            )
        )
    ):
        tiles.ledger.bump(_tiles_keys.TILE_BOUNDARY_CONCAT_VIEW_HITS)
        return BoundaryTileView(
            a.tile,
            0,
            total,
            a.orientation,
            min(a.source_offset, b.source_offset),
        ), tiles.retain(a.tile)

    extended = _extend_in_backing(tiles, a, b)
    if extended is not None:
        tiles.ledger.bump(_tiles_keys.TILE_BOUNDARY_CONCAT_BACKING_HITS)
        return extended, tiles.retain(extended.tile)

    pending = [(0, (total - 1).bit_length(), False)]
    values: list[TileLease] = []
    padding: list[TileLease] = []
    blank = tiles.alphabet(alphabet).blank
    try:
        while pending:
            origin, level, ready = pending.pop()
            tiles.ledger.bump(_tiles_keys.TILE_BOUNDARY_CONCAT_FRAMES)
            if ready:
                right, left = values.pop(), values.pop()
                try:
                    values.append(tiles.join(left.tile, right.tile))
                finally:
                    left.close()
                    right.close()
                continue
            width = 1 << level
            if origin >= total:
                if not padding:
                    padding.append(tiles.leaf(alphabet, blank))
                while len(padding) <= level:
                    padding.append(tiles.join(padding[-1].tile, padding[-1].tile))
                values.append(tiles.retain(padding[level].tile))
                continue
            view, offset = (
                (a, origin)
                if origin < a.relative_extent
                else (b, origin - a.relative_extent)
            )
            if offset + width <= view.relative_extent:
                source_offset = view.source_offset + (
                    view.relative_extent - offset - width
                    if view.orientation
                    else offset
                )
                if source_offset % width == 0:
                    current = view.tile
                    node = tiles.resolve(current)
                    cursor = source_offset
                    while node.level > level:
                        if node.left is None or node.right is None:
                            raise ValueError("malformed causal operand parent")
                        half = node.width // 2
                        current = node.right if cursor >= half else node.left
                        if cursor >= half:
                            cursor -= half
                        node = tiles.resolve(current)
                        tiles.ledger.bump(_tiles_keys.TILE_BOUNDARY_CONCAT_CHILD_VISITS)
                    values.append(
                        tiles.mirror(current)
                        if view.orientation
                        else tiles.retain(current)
                    )
                    continue
            if not level:
                raise AssertionError("causal concatenation lost a covered source leaf")
            half = width // 2
            pending.extend(
                (
                    (origin, level, True),
                    (origin + half, level - 1, False),
                    (origin, level - 1, False),
                )
            )
            peak = len(pending) + len(values) + len(padding)
            previous = tiles.ledger.counters.get(
                _tiles_keys.TILE_BOUNDARY_CONCAT_WORKSPACE_PEAK, 0
            )
            if peak > previous:
                tiles.ledger.bump(
                    _tiles_keys.TILE_BOUNDARY_CONCAT_WORKSPACE_PEAK,
                    peak - previous,
                )
        if len(values) != 1:
            raise AssertionError("causal concatenation produced another result arity")
        result = values.pop()
        return BoundaryTileView(result.tile, 0, total), result
    finally:
        for lease in (*values, *padding):
            lease.close()


__all__ = [
    "EMPTY_BOUNDARY_TILES",
    "BoundaryTileOperands",
    "BoundaryTileView",
    "boundary_dyadic_pieces",
    "concat_boundary_views",
    "normalize_boundary_view",
    "validate_boundary_shape",
]

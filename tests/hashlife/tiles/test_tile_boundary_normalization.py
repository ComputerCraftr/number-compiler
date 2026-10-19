"""Canonical clipped-region identity for causal scheduler requests."""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileView,
    normalize_boundary_view,
)
from number_compiler.hashlife.tiles.tiles import TileID
from tests.support.tile_kernel import make_tile_from_symbols, make_tile_runtime

if TYPE_CHECKING:
    from number_compiler.hashlife.tiles.tiles import (
        TileArena,
        TileLease,
        TileRecord,
    )


def _retained_state(
    tiles: TileArena,
) -> tuple[
    int,
    int,
    dict[int, TileRecord],
    dict[tuple[int, int, int, int, int], int],
    dict[int, int],
    dict[tuple[int, int, int], None],
    dict[int, TileID],
]:
    return (
        tiles.ledger.entries,
        tiles.ledger.nodes,
        dict(tiles._nodes),
        dict(tiles._keys),
        dict(tiles._refs),
        dict(tiles._edges),
        dict(tiles._leases),
    )


def test_equal_clips_with_different_backing_and_orientation_share_content() -> None:
    _ledger, tiles, adapter, primitive, _scheduler = make_tile_runtime(
        BaseBlockEffect(3)
    )
    with (
        make_tile_from_symbols(
            tiles, adapter, primitive, (4, 0, 1, 2, 4, 4, 4, 4)
        ) as forward,
        make_tile_from_symbols(
            tiles, adapter, primitive, (4, 4, 2, 1, 0, 3, 3, 3)
        ) as reverse,
    ):
        first, first_lease = normalize_boundary_view(
            tiles,
            BoundaryTileView(forward.tile, 11, 3, 0, 1),
        )
        second, second_lease = normalize_boundary_view(
            tiles,
            BoundaryTileView(reverse.tile, 11, 3, 1, 2),
        )
        try:
            assert first == second
            assert first.source_offset == 0
            assert first.orientation == 0
            assert tuple(tiles.point(first.tile, index) for index in range(3)) == (
                0,
                1,
                2,
            )
        finally:
            first_lease.close()
            second_lease.close()


def test_normalization_rejects_empty_and_foreign_views_before_retained_mutation() -> (
    None
):
    _ledger, tiles, adapter, primitive, _scheduler = make_tile_runtime(
        BaseBlockEffect(3)
    )
    with make_tile_from_symbols(tiles, adapter, primitive, (0, 1, 2, 3)) as source:
        before = _retained_state(tiles)
        with pytest.raises(ValueError, match="nonempty"):
            normalize_boundary_view(
                tiles,
                BoundaryTileView(source.tile, 0, 0, 0, 2),
            )
        assert _retained_state(tiles) == before

        foreign = TileID(ArenaToken("foreign"), "canonical-tile", 0)
        with pytest.raises(ValueError, match="different arena"):
            normalize_boundary_view(tiles, BoundaryTileView(foreign, 0, 1))
        assert _retained_state(tiles) == before


def test_normalization_failure_releases_intermediate_leases(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _ledger, tiles, adapter, primitive, _scheduler = make_tile_runtime(
        BaseBlockEffect(3)
    )
    with make_tile_from_symbols(
        tiles, adapter, primitive, (0, 1, 2, 3, 4, 0, 1, 2)
    ) as source:
        before = _retained_state(tiles)
        join = tiles.join
        calls = 0

        def fail_on_second_join(left: TileID, right: TileID) -> TileLease:
            nonlocal calls
            calls += 1
            if calls == 2:
                raise RuntimeError("normalization join failed")
            return join(left, right)

        monkeypatch.setattr(tiles, "join", fail_on_second_join)
        with pytest.raises(RuntimeError, match="normalization join failed"):
            normalize_boundary_view(
                tiles,
                BoundaryTileView(source.tile, 0, 5, 0, 1),
            )
        assert _retained_state(tiles) == before

"""Finite powered consumer and shared-tile polynomial laws."""

from __future__ import annotations

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.polynomials.twisted_observer import (
    TwistedCylinderProjection,
    first_mirror_obstruction,
)
from number_compiler.hashlife.execution.tile_scheduler import TileApplication
from number_compiler.hashlife.observation.tile_cylinder import _sheet
from number_compiler.hashlife.observation.tile_projection import LazyProjection
from number_compiler.hashlife.tiles.tiles import TileAlphabet, TileArena
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


@pytest.mark.parametrize("seed", (196, 89, 99, 121))
def test_powered_mirror_consumes_tiles_without_point_queries(
    seed: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    expected = seed
    for _ in range(3):
        expected += int(str(expected)[::-1])
    digits = tuple(int(x) for x in reversed(str(expected)))
    reference = first_mirror_obstruction(len(digits), digits.__getitem__)
    term = ReverseAddPoweredTerm(seed, 3)

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("powered cylinder replayed scalar point queries")

    monkeypatch.setattr(ReverseAddPoweredTerm, "digit", forbidden)
    assert term.mirror_obstruction() == reference
    counters = term._ledger.counters
    assert counters["tile_cylinder_node_evaluations"] > 0
    assert counters.get("point_response_requests", 0) == 0
    for account in term._ledger.inventory():
        if account.name.startswith("tile-cylinder-"):
            assert account.entries == account.nodes == 0
            assert account.observed_entries == account.observed_nodes == 0
    assert term.metrics().resource_audit_complete == 1
    assert term.metrics().forbidden_future_payloads == 0
    owners = len(term._ledger.inventory())
    assert term.mirror_obstruction(first_width=2) == first_mirror_obstruction(
        len(digits), digits.__getitem__, first_width=2
    )
    assert len(term._ledger.inventory()) == owners


@pytest.mark.parametrize("width,sign", ((1, 1), (2, -1), (3, -1), (4, 1)))
def test_sheet_append_matches_independent_concatenation(width: int, sign: int) -> None:
    for left in ((), (3,), (2, 5, 1), (0, 1, 8, 9)):
        for right in ((), (7,), (4, 0, 6)):
            a = TwistedCylinderProjection.observe(left, width=width, sign=sign)
            b = TwistedCylinderProjection.observe(right, width=width, sign=sign)
            assert a.append(b, span=len(left)) == TwistedCylinderProjection.observe(
                left + right, width=width, sign=sign
            )


def test_cylinder_workspace_disposes_if_application_close_fails(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = ReverseAddPoweredTerm(196, 1)
    term.mirror_obstruction()
    projection = term._point_index()._lazy_application
    assert isinstance(projection, LazyProjection)
    close = TileApplication.close

    def fail_close(self: TileApplication) -> Never:
        raise ValueError("corrupt application")

    monkeypatch.setattr(TileApplication, "close", fail_close)
    with pytest.raises(ValueError, match="corrupt application"):
        projection.close()
    accounts = [
        a for a in term._ledger.inventory() if a.name.startswith("tile-cylinder-")
    ]
    assert len(accounts) == 2
    assert all(a.disposed and a.entries == a.nodes == 0 for a in accounts)
    monkeypatch.setattr(TileApplication, "close", close)
    projection.close()


def test_tile_fold_shares_uniform_subtrees_and_clips_partial_prefix() -> None:
    ledger = ResourceLedger()
    tiles = TileArena(ledger)
    alphabet = tiles.intern_alphabet(
        TileAlphabet(
            11,
            10,
            10,
            4,
            "unsigned-radix-cell-with-explicit-blank",
            "canonical-tile-alphabet-v1",
        )
    )
    root = tiles.leaf(alphabet, 7)
    for _ in range(16):
        parent = tiles.join(root.tile, root.tile)
        root.close()
        root = parent
    try:
        assert not _sheet(tiles, root.tile, 65536, 3, -1).nonzero
        assert ledger.counters["tile_cylinder_node_evaluations"] == 17
        assert ledger.counters["tile_cylinder_leaf_reads"] == 1
        assert ledger.counters["tile_cylinder_cache_hits"] == 16
        assert not _sheet(tiles, root.tile, 12345, 5, -1).nonzero
    finally:
        root.close()


def test_tile_fold_preserves_nonpalindromic_clipped_boundary_and_budget_cleanup() -> (
    None
):
    ledger = ResourceLedger()
    tiles = TileArena(ledger)
    alphabet = tiles.intern_alphabet(
        TileAlphabet(
            11,
            10,
            10,
            4,
            "unsigned-radix-cell-with-explicit-blank",
            "canonical-tile-alphabet-v1",
        )
    )
    with (
        tiles.leaf(alphabet, 3) as a,
        tiles.leaf(alphabet, 8) as b,
        tiles.join(a.tile, b.tile) as pair,
        tiles.join(pair.tile, pair.tile) as root,
    ):
        result = _sheet(tiles, root.tile, 3, 2, -1)
        expected = first_mirror_obstruction(3, (3, 8, 3).__getitem__, first_width=2)
        assert not result.nonzero and expected is None
        result = _sheet(tiles, root.tile, 2, 2, -1)
        assert result.coefficients == (-5, 5)
        old = ledger.max_nodes
        ledger.max_nodes = ledger.nodes + 1
        try:
            with pytest.raises(BlockContextBudgetExceeded):
                _sheet(tiles, root.tile, 4, 2, -1)
        finally:
            ledger.max_nodes = old
        assert all(
            account.entries == account.nodes == 0
            for account in ledger.inventory()
            if account.name.startswith("tile-cylinder-")
        )
    with (
        tiles.leaf(alphabet, 10) as padding,
        pytest.raises(ValueError, match="interior padding"),
    ):
        _sheet(tiles, padding.tile, 1, 1, 1)
    assert all(
        account.entries == account.nodes == 0
        for account in ledger.inventory()
        if account.name.startswith("tile-cylinder-")
    )

"""Canonical future content is permitted; provenance and trajectories are not."""

from __future__ import annotations

from tests.support.assertions import assert_rejected_atomically

from collections.abc import Callable, Hashable
from dataclasses import replace
from typing import TYPE_CHECKING, Never, TypeVar, cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from number_compiler.hashlife.tiles.tiles import (
    TileAlphabet,
    TileArena,
    TileID,
    _TileKey,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict

if TYPE_CHECKING:
    from number_compiler.hashlife.tiles.tiles import TileAlphabetID


def _arena() -> tuple[ResourceLedger, TileArena, TileAlphabetID]:
    ledger = ResourceLedger()
    arena = TileArena(ledger)
    alphabet = arena.intern_alphabet(TileAlphabet(3, 2, 2, 2, "binary", "1"))
    return ledger, arena, alphabet


def _reconciled(ledger: ResourceLedger) -> None:
    assert all(row.accounting_delta == 0 for row in ledger.inventory())
    assert ledger.entries == sum(
        _observed(row.observed_entries) for row in ledger.inventory()
    )
    assert ledger.nodes == sum(
        _observed(row.observed_nodes) for row in ledger.inventory()
    )


def test_sources_and_future_content_share_live_tiles_and_derived_summaries() -> None:
    ledger, arena, alphabet = _arena()
    with (
        arena.leaf(alphabet, 0) as zero,
        arena.leaf(alphabet, 1) as one,
        arena.join(zero.tile, one.tile) as source,
        arena.join(zero.tile, one.tile) as future,
    ):
        assert source.tile == future.tile
        record = arena.resolve(future.tile)
        assert (
            record.level,
            record.first_active,
            record.last_active,
            record.extent,
        ) == (1, 0, 1, 2)
        assert [arena.point(future.tile, i) for i in (0, 1)] == [0, 1]
        assert ledger.counters["tile_intern_early_hits"] == 1
    assert not arena._nodes and not arena._keys and not arena._edges
    _reconciled(ledger)


def test_alphabet_blank_and_interpretation_are_part_of_identity() -> None:
    ledger, arena, original = _arena()
    changed_blank = arena.intern_alphabet(TileAlphabet(3, 0, 2, 2, "binary", "1"))
    changed_domain = arena.intern_alphabet(TileAlphabet(3, 2, 2, 2, "pair", "1"))
    assert arena.intern_alphabet(arena.alphabet(original)) == original
    with (
        arena.leaf(original, 0) as a,
        arena.leaf(changed_blank, 0) as b,
        arena.leaf(changed_domain, 0) as c,
    ):
        assert len({a.tile, b.tile, c.tile}) == 3
        assert arena.resolve(a.tile).extent == 1
        assert arena.resolve(b.tile).extent == 0
        assert_rejected_atomically(
            ledger, lambda: arena.join(a.tile, c.tile), ValueError
        )


def test_parent_retains_children_and_retirement_never_recycles_ids() -> None:
    ledger, arena, alphabet = _arena()
    leaf = arena.leaf(alphabet, 1)
    old_child = leaf.tile
    parent = arena.join(old_child, old_child)
    old_parent = parent.tile
    leaf.close()
    assert arena.point(old_parent, 1) == 1
    parent.close()
    for stale in (old_child, old_parent):
        with pytest.raises(ValueError):
            arena.resolve(stale)
    with arena.leaf(alphabet, 1) as replacement:
        assert replacement.tile.local_id > old_parent.local_id
    _reconciled(ledger)


def test_deep_shared_tree_retires_iteratively() -> None:
    ledger, arena, alphabet = _arena()
    current = arena.leaf(alphabet, 1)
    for _ in range(1200):
        parent = arena.join(current.tile, current.tile)
        current.close()
        current = parent
    assert len(arena._nodes) == 1201
    assert arena.point(current.tile, (1 << 1199) + 1) == 1
    current.close()
    assert not arena._nodes and not arena._refs and not arena._edges
    _reconciled(ledger)


@pytest.mark.parametrize("alias", (True, 1.0, "1"))
def test_numeric_aliases_reject_before_warm_lookup_or_retirement(
    alias: bool | float | str,
) -> None:
    ledger, arena, alphabet = _arena()
    with arena.leaf(alphabet, 1) as first, arena.leaf(alphabet, 0) as _second:
        handle = object.__new__(TileID)
        object.__setattr__(handle, "owner", arena.owner)
        object.__setattr__(handle, "kind", "canonical-tile")
        object.__setattr__(handle, "local_id", alias)
        before = ledger.snapshot()
        operations: tuple[Callable[[], object], ...] = (
            lambda: arena.resolve(handle),
            lambda: arena.retain(handle),
            lambda: arena._release_lease(cast("int", alias)),
            lambda: arena.leaf(alphabet, cast("int", alias)),
            lambda: arena.point(first.tile, cast("int", alias)),
        )
        for operation in operations:
            with pytest.raises((ValueError, TypeError)):
                operation()
            assert ledger.snapshot() == before


def test_foreign_ids_forged_summaries_and_child_levels_reject_before_mutation() -> None:
    ledger, arena, alphabet = _arena()
    with arena.leaf(alphabet, 1) as leaf, arena.join(leaf.tile, leaf.tile) as parent:
        before = ledger.snapshot()
        invalid = replace(leaf.tile, owner=ArenaToken("canonical-tiles"))
        operations: tuple[Callable[[], object], ...] = (
            lambda: arena.join(invalid, leaf.tile),
            lambda: arena.join(leaf.tile, parent.tile),
            lambda: arena._intern(replace(arena.resolve(parent.tile), last_active=0)),
            lambda: arena._intern(replace(arena.resolve(parent.tile), level=0)),
        )
        for operation in operations:
            with pytest.raises((ValueError, TypeError)):
                operation()
            assert ledger.snapshot() == before


def test_budget_failure_reserves_no_child_references_or_result_entries() -> None:
    ledger, arena, alphabet = _arena()
    with arena.leaf(alphabet, 1) as leaf:
        ledger.max_cache_entries = ledger.entries + 5
        before = ledger.snapshot()
        refs = dict(arena._refs)
        with pytest.raises(BlockContextBudgetExceeded):
            arena.join(leaf.tile, leaf.tile)
        assert (ledger.entries, ledger.nodes) == (before.entries, before.nodes)
        assert dict(arena._refs) == refs
        _reconciled(ledger)


def test_failed_publication_rolls_back_child_retains_and_all_reservations(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, arena, alphabet = _arena()
    with arena.leaf(alphabet, 1) as leaf:
        before = ledger.snapshot()
        old_refs = dict(arena._refs)
        original = LedgerDict.__setitem__
        writes = 0

        def fail_second_edge(
            store: LedgerDict[KeyT, ValueT], key: KeyT, value: ValueT
        ) -> None:
            nonlocal writes
            if store is arena._edges:
                writes += 1
                if writes == 2:
                    raise RuntimeError("injected second-child failure")
            return original(store, key, value)

        monkeypatch.setattr(LedgerDict, "__setitem__", fail_second_edge)
        with pytest.raises(RuntimeError, match="second-child"):
            arena.join(leaf.tile, leaf.tile)
        assert (ledger.entries, ledger.nodes) == (before.entries, before.nodes)
        assert dict(arena._refs) == old_refs
        assert not arena._edges
        assert len(arena._nodes) == len(arena._keys) == len(arena._leases) == 1
        _reconciled(ledger)


def test_zero_budget_rejects_first_required_allocation() -> None:
    ledger = ResourceLedger(max_cache_entries=0)
    arena = TileArena(ledger)
    with pytest.raises(BlockContextBudgetExceeded):
        arena.intern_alphabet(TileAlphabet(3, 2, 2, 2, "binary", "1"))
    assert ledger.entries == ledger.nodes == 0
    assert not arena._alphabets and not arena._alphabet_keys


@pytest.mark.parametrize("alias", (True, 1.0, -1, 100))
def test_corrupt_alphabet_interner_rejects_before_warm_return(
    alias: bool | float,
) -> None:
    ledger, arena, alphabet = _arena()
    definition = arena.alphabet(alphabet)
    arena._alphabet_keys[definition] = cast("int", alias)
    assert_rejected_atomically(
        ledger, lambda: arena.intern_alphabet(definition), (ValueError, TypeError)
    )


def test_independent_inventory_accepts_future_tiles_without_executing_queries(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.resources.metric_collection import collect_ledger_metrics
    from number_compiler.resources.tile_inventory import audit_tiles

    ledger, arena, alphabet = _arena()
    with arena.leaf(alphabet, 1) as leaf, arena.join(leaf.tile, leaf.tile) as parent:

        def forbidden(*args: object, **kwargs: object) -> Never:
            raise AssertionError("inventory attempted execution")

        monkeypatch.setattr(TileArena, "point", forbidden)
        monkeypatch.setattr(TileArena, "leaf", forbidden)
        monkeypatch.setattr(TileArena, "join", forbidden)
        before = ledger.snapshot()
        approved, invalid = audit_tiles(arena, dict(ledger.iter_containers()))
        assert id(arena.resolve(parent.tile)) in approved
        assert not invalid
        metrics = collect_ledger_metrics(ledger)
        assert metrics.canonical_tile_nodes == 2
        assert metrics.tile_alphabet_nodes == 1
        assert metrics.tile_root_leases == 2
        assert metrics.tile_child_reverse_index_entries == 2
        assert metrics.representation_boundary_complete == 1
        assert metrics.resource_audit_complete == 1
        assert metrics.forbidden_future_payloads == 0
        assert metrics.tile_publications == 2
        assert ledger.snapshot() == before


@pytest.mark.parametrize(
    "corruption",
    ("summary", "references", "edges", "lease", "highwater", "mirror"),
)
def test_independent_tile_audit_detects_corrupted_content_and_ownership(
    corruption: str,
) -> None:
    from number_compiler.resources.tile_inventory import audit_tiles

    ledger, arena, alphabet = _arena()
    leaf = arena.leaf(alphabet, 1)
    parent = arena.join(leaf.tile, leaf.tile)
    if corruption == "summary":
        arena._nodes[parent.tile.local_id] = replace(
            arena.resolve(parent.tile), last_active=0
        )
    elif corruption == "references":
        arena._refs[leaf.tile.local_id] += 1
    elif corruption == "edges":
        del arena._edges[leaf.tile.local_id, parent.tile.local_id, 0]
    elif corruption == "lease":
        arena._leases[leaf._id] = replace(leaf.tile, local_id=1000)
    elif corruption == "mirror":
        with arena.mirror(parent.tile):
            pass
        arena._keys[arena._mirror_key(parent.tile.local_id)] = leaf.tile.local_id
    else:
        arena._next_tile = True
    _, invalid = audit_tiles(arena, dict(ledger.iter_containers()))
    assert invalid


def test_clipped_extent_does_not_invent_activity_in_padding_or_gaps() -> None:
    ledger, tiles, alphabet = _arena()
    with (
        tiles.leaf(alphabet, 1) as one,
        tiles.leaf(alphabet, 2) as blank,
        tiles.join(one.tile, blank.tile) as low,
        tiles.join(blank.tile, one.tile) as high,
        tiles.join(low.tile, high.tile) as root,
    ):
        assert [tiles.active_width(root.tile, stop) for stop in range(5)] == [
            0,
            1,
            1,
            1,
            4,
        ]
        before = ledger.snapshot()
        for bad in (True, 1.0, -1, 5):
            with pytest.raises((ValueError, TypeError)):
                tiles.active_width(root.tile, cast("int | None", bad))
            assert ledger.snapshot() == before


def test_tile_retirement_cannot_install_an_arbitrary_callback_owner() -> None:
    from types import SimpleNamespace

    ledger, arena, _ = _arena()
    callback = SimpleNamespace(
        tiles=arena, ledger=ledger, retire_tile=lambda _tile: None
    )
    assert_rejected_atomically(
        ledger,
        lambda: arena.bind_results(cast("CompletedResultArena", callback)),
        TypeError,
        match="canonical result memo owner",
    )
    assert arena._results is None


def test_exact_tile_mirror_is_iterative_involutive_and_warm(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.resources.metric_collection import collect_ledger_metrics

    ledger, arena, alphabet = _arena()
    with (
        arena.leaf(alphabet, 0) as zero,
        arena.leaf(alphabet, 1) as one,
        arena.leaf(alphabet, 2) as blank,
        arena.join(zero.tile, one.tile) as low,
        arena.join(blank.tile, zero.tile) as high,
        arena.join(low.tile, high.tile) as source,
    ):
        mirrored = arena.mirror(source.tile)
        assert [arena.point(mirrored.tile, i) for i in range(4)] == [0, 2, 1, 0]
        with arena.mirror(mirrored.tile) as restored:
            assert restored.tile == source.tile
        before = ledger.snapshot()

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("warm mirror rebuilt exact children")

        monkeypatch.setattr(TileArena, "join", forbidden)
        monkeypatch.setattr(TileArena, "_publish_mirror", forbidden)
        with arena.mirror(source.tile) as warm:
            assert warm.tile == mirrored.tile
        assert ledger.counters["tile_mirror_early_hits"] >= 2
        metrics = collect_ledger_metrics(ledger)
        assert metrics.tile_mirror_relation_entries > 0
        assert ledger.entries == before.entries
        mirrored.close()
    assert not arena._nodes and not arena._keys
    _reconciled(ledger)


def test_tile_mirror_relation_publication_failure_is_atomic(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, arena, alphabet = _arena()
    with arena.leaf(alphabet, 1) as leaf:
        before = ledger.snapshot()

        def fail_write(*_args: object, **_kwargs: object) -> Never:
            raise RuntimeError("injected mirror-index failure")

        monkeypatch.setattr(TileArena, "_write_mirror", fail_write)
        with pytest.raises(RuntimeError, match="mirror-index"):
            arena.mirror(leaf.tile)
        assert (ledger.entries, ledger.nodes, ledger.inventory()) == (
            before.entries,
            before.nodes,
            before.inventory,
        )
        assert arena._mirror_target(leaf.tile) is None


def test_two_way_mirror_index_rolls_back_if_second_write_fails(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, arena, alphabet = _arena()
    with (
        arena.leaf(alphabet, 0) as zero,
        arena.leaf(alphabet, 1) as one,
        arena.mirror(zero.tile),
        arena.mirror(one.tile),
        arena.join(zero.tile, one.tile) as source,
        arena.join(one.tile, zero.tile) as reflected,
    ):
        before = ledger.snapshot()
        writes = 0
        original = TileArena._write_mirror

        def fail_second(self: TileArena, key: _TileKey, local_id: int) -> None:
            nonlocal writes
            writes += 1
            if writes == 2:
                raise RuntimeError("injected mirror reverse-index failure")
            original(self, key, local_id)

        monkeypatch.setattr(TileArena, "_write_mirror", fail_second)
        with pytest.raises(RuntimeError, match="reverse-index"):
            arena._publish_mirror(source.tile, reflected.tile)
        assert (ledger.entries, ledger.nodes, ledger.inventory()) == (
            before.entries,
            before.nodes,
            before.inventory,
        )
        assert arena._mirror_target(source.tile) is None
        assert arena._mirror_target(reflected.tile) is None


def test_tile_mirror_budget_failure_precedes_relation_mutation() -> None:
    ledger, arena, alphabet = _arena()
    with arena.leaf(alphabet, 1) as leaf:
        ledger.tighten_limits(None, ledger.entries)
        before = ledger.snapshot()
        with pytest.raises(BlockContextBudgetExceeded):
            arena.mirror(leaf.tile)
        assert (ledger.entries, ledger.nodes, ledger.inventory()) == (
            before.entries,
            before.nodes,
            before.inventory,
        )
        assert arena._mirror_target(leaf.tile) is None


KeyT = TypeVar("KeyT", bound=Hashable)
ValueT = TypeVar("ValueT")


def _observed(value: int | None) -> int:
    assert value is not None
    return value

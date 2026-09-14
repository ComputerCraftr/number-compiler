"""Cross-observation reuse for canonical clipped causal regions."""

from __future__ import annotations

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.tile_causal_tasks import (
    CausalPrefix,
    append_prefix,
)
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.hashlife.tiles.tile_boundary_concat_memo import (
    concat_cached_boundary_views,
    lookup_boundary_concat,
)
from number_compiler.hashlife.tiles.tile_region_memo import (
    lookup_normalized_region,
    normalize_cached_region,
)
from number_compiler.hashlife.tiles.tile_result_records import (
    BoundaryConcatKey,
    NormalizedRegionKey,
    NormalizedRegionResult,
)
from number_compiler.hashlife.tiles.tiles import TileID, TileLease
from tests.arithmetic.contracts.test_tile_kernel import _runtime, _tile


def test_clipped_mirror_scan_reuses_region_before_decomposition(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.hashlife.tiles.tile_region_memo as region_memo
    from number_compiler.hashlife.execution.tile_causal_tasks import scan_view

    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    with _tile(tiles, adapter, primitive, (0, 1, 2, 3)) as source:
        leases: list[TileLease] = []
        try:
            first = scan_view(
                tiles,
                leases,
                BoundaryTileView(source.tile, 99, 3, 1, 1),
                results=scheduler.results,
            )
            assert tuple(tiles.point(first.tile, i) for i in range(3)) == (3, 2, 1)
            before = ledger.counters.get("tile_boundary_concat_frames", 0)

            def forbidden(*_args: object, **_kwargs: object) -> Never:
                raise AssertionError("warm clipped scan reconstructed its region")

            monkeypatch.setattr(region_memo, "normalize_boundary_view", forbidden)
            second = scan_view(
                tiles,
                leases,
                BoundaryTileView(source.tile, 7, 3, 1, 1),
                results=scheduler.results,
            )
            assert second == first
            assert first.relative_origin == 0
            assert ledger.counters.get("tile_boundary_concat_frames", 0) == before
        finally:
            for lease in reversed(leases):
                lease.close()


def test_prefix_concat_reuses_exact_content_across_actions(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.hashlife.tiles.tile_boundary_concat_memo as concat_memo

    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    square = adapter.power(primitive, 2)
    with _tile(tiles, adapter, primitive, (0, 1)) as source:
        node = tiles.resolve(source.tile)
        assert node.left is not None and node.right is not None
        left = BoundaryTileView(node.left, 0, 1)
        right = BoundaryTileView(node.right, 0, 1)
        leases: list[TileLease] = []
        try:
            first = append_prefix(
                adapter,
                tiles,
                leases,
                CausalPrefix(primitive, 0, 0, 0, left),
                right,
                results=scheduler.results,
            )

            def forbidden(*_args: object, **_kwargs: object) -> Never:
                raise AssertionError("warm boundary concat traversed its operands")

            monkeypatch.setattr(concat_memo, "concat_boundary_views", forbidden)
            second = append_prefix(
                adapter,
                tiles,
                leases,
                CausalPrefix(square, 0, 1, 1, left),
                right,
                results=scheduler.results,
            )
            assert first.view is not None and second.view is not None
            assert first.view.tile == second.view.tile == source.tile
            assert ledger.counters["tile_boundary_concat_cache_early_hits"] == 1
        finally:
            for lease in reversed(leases):
                lease.close()


def test_prefix_extension_reuses_existing_canonical_child_before_join(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    with _tile(tiles, adapter, primitive, (0, 1, 2, 3, 4, 0, 1, 2)) as source:
        node = tiles.resolve(source.tile)
        assert node.left is not None
        left = tiles.resolve(node.left)
        assert left.right is not None
        first = BoundaryTileView(source.tile, 0, 2)
        second = BoundaryTileView(left.right, 0, 2)

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("existing prefix content was reconstructed")

        monkeypatch.setattr(tiles, "join", forbidden)
        observed, lease = concat_cached_boundary_views(
            scheduler.results, node.alphabet, first, second
        )
        try:
            assert observed == BoundaryTileView(source.tile, 0, 4)
            assert ledger.counters["tile_boundary_concat_backing_hits"] == 1
            assert ledger.counters.get("tile_boundary_concat_frames", 0) == 0
        finally:
            lease.close()


def test_prefix_extension_does_not_alias_a_different_adjacent_child() -> None:
    _, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    with (
        _tile(tiles, adapter, primitive, (0, 1, 2, 3, 4, 0, 1, 2)) as source,
        _tile(tiles, adapter, primitive, (4, 4)) as different,
    ):
        node = tiles.resolve(source.tile)
        observed, lease = concat_cached_boundary_views(
            scheduler.results,
            node.alphabet,
            BoundaryTileView(source.tile, 0, 2),
            BoundaryTileView(different.tile, 0, 2),
        )
        try:
            assert tuple(tiles.point(observed.tile, i) for i in range(4)) == (
                0,
                1,
                4,
                4,
            )
        finally:
            lease.close()


def test_boundary_concat_retirement_removes_nonowning_binding() -> None:
    _, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    with (
        _tile(tiles, adapter, primitive, (0,)) as left,
        _tile(tiles, adapter, primitive, (1,)) as right,
    ):
        alphabet = adapter.alphabet(primitive)
        first = BoundaryTileView(left.tile, 0, 1)
        second = BoundaryTileView(right.tile, 0, 1)
        key = BoundaryConcatKey(alphabet, first, second)
        _view, lease = concat_cached_boundary_views(
            scheduler.results,
            alphabet,
            first,
            second,
        )
        lease.close()
        assert lookup_boundary_concat(scheduler.results, key) is None


def test_adjacent_clipped_and_mirrored_concat_remain_constant_time_views(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.hashlife.tiles.tile_boundary_concat_memo as concat_memo

    _, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    with _tile(tiles, adapter, primitive, (0, 1, 2, 3)) as source:
        alphabet = adapter.alphabet(primitive)

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("adjacent concat constructed exact future children")

        monkeypatch.setattr(concat_memo, "normalize_boundary_view", forbidden)
        monkeypatch.setattr(tiles, "join", forbidden)
        forward, forward_lease = concat_cached_boundary_views(
            scheduler.results,
            alphabet,
            BoundaryTileView(source.tile, 11, 2, 0, 0),
            BoundaryTileView(source.tile, 13, 2, 0, 2),
        )
        mirrored, mirrored_lease = concat_cached_boundary_views(
            scheduler.results,
            alphabet,
            BoundaryTileView(source.tile, -9, 2, 1, 2),
            BoundaryTileView(source.tile, -7, 2, 1, 0),
        )
        try:
            assert forward == BoundaryTileView(source.tile, 0, 4)
            assert mirrored == BoundaryTileView(source.tile, 0, 4, 1)
            assert tuple(
                tiles.point(mirrored.tile, 3 - index) for index in range(4)
            ) == (3, 2, 1, 0)
            assert mirrored.relative_origin == 0
            assert mirrored.relative_extent == 4
            assert mirrored.orientation == 1
            assert mirrored.source_offset == 0
        finally:
            mirrored_lease.close()
            forward_lease.close()


def test_foreign_boundary_concat_rejects_before_lookup_or_mutation() -> None:
    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    _, foreign_tiles, foreign_adapter, foreign_primitive, _ = _runtime(
        BaseBlockEffect(3)
    )
    with (
        _tile(tiles, adapter, primitive, (0,)) as local,
        _tile(foreign_tiles, foreign_adapter, foreign_primitive, (1,)) as foreign,
    ):
        before_memo = tuple(scheduler.results._memo.items())
        before_counters = dict(ledger.counters)
        with pytest.raises(ValueError, match="different arena"):
            concat_cached_boundary_views(
                scheduler.results,
                adapter.alphabet(primitive),
                BoundaryTileView(local.tile, 0, 1),
                BoundaryTileView(foreign.tile, 0, 1),
            )
        assert tuple(scheduler.results._memo.items()) == before_memo
        assert dict(ledger.counters) == before_counters


def test_boundary_concat_budget_failure_rolls_back_memo_and_reverse_index() -> None:
    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    with (
        _tile(tiles, adapter, primitive, (0,)) as left,
        _tile(tiles, adapter, primitive, (1,)) as right,
        tiles.join(left.tile, right.tile) as _prebuilt,
    ):
        alphabet = adapter.alphabet(primitive)
        first = BoundaryTileView(left.tile, 0, 1)
        second = BoundaryTileView(right.tile, 0, 1)
        memo_before = tuple(scheduler.results._memo.items())
        reverse_before = tuple(scheduler.results._reverse.items())
        ledger.max_cache_entries = ledger.entries
        with pytest.raises(BlockContextBudgetExceeded):
            concat_cached_boundary_views(
                scheduler.results,
                alphabet,
                first,
                second,
            )
        assert tuple(scheduler.results._memo.items()) == memo_before
        assert tuple(scheduler.results._reverse.items()) == reverse_before


def test_application_pins_clipped_normalization_across_observations(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.hashlife.tiles.tile_region_memo as region_memo

    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    action = adapter.power(primitive, 4)
    with _tile(tiles, adapter, primitive, (4, 0, 1, 2, 3, 4, 4, 4)) as source:
        raw = BoundaryTileView(source.tile, -11, 3, 0, 1)
        key = NormalizedRegionKey(raw)
        with scheduler.application(
            action,
            source.tile,
            adapter.initial_ports(action),
            adapter.wiring(action),
        ) as application:
            validation_before = ledger.counters.get(
                "tile_region_application_validation_visits",
                0,
            )
            first, lease = normalize_cached_region(
                scheduler.results,
                raw,
                dependencies=scheduler._causal_dependencies,
                application=application.identity,
            )
            first_tile = first.tile
            lease.close()
            assert lookup_normalized_region(scheduler.results, key) is not None

            def forbidden(*_args: object, **_kwargs: object) -> Never:
                raise AssertionError("warm clipped region rebuilt exact content")

            monkeypatch.setattr(region_memo, "normalize_boundary_view", forbidden)
            monkeypatch.setattr(tiles, "join", forbidden)
            second, second_lease = normalize_cached_region(
                scheduler.results,
                raw,
                dependencies=scheduler._causal_dependencies,
                application=application.identity,
            )
            try:
                assert second.tile == first_tile
                assert second.relative_origin == -11
                assert second.relative_extent == 3
            finally:
                second_lease.close()
            assert ledger.counters["tile_region_normalization_early_hits"] >= 2
            assert ledger.counters["tile_region_application_validation_visits"] == (
                validation_before + 2
            )

        # The memo cannot keep a normalized future tile alive after its sole
        # application owner releases it.  Retirement removes both reverse links.
        assert lookup_normalized_region(scheduler.results, key) is None


def test_different_backings_share_content_but_keep_occurrence_bindings() -> None:
    from number_compiler.resources.tile_result_inventory import audit_tile_results

    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    first_symbols = (4, 4, 0, 1, 2, 4, 4, 4)
    second_symbols = (4, 0, 1, 2, 4, 3, 3, 3)
    with (
        _tile(tiles, adapter, primitive, first_symbols) as first,
        _tile(tiles, adapter, primitive, second_symbols) as second,
    ):
        first_raw = BoundaryTileView(first.tile, -7, 3, 0, 2)
        second_raw = BoundaryTileView(second.tile, -7, 3, 0, 1)
        left, left_lease = normalize_cached_region(scheduler.results, first_raw)
        right, right_lease = normalize_cached_region(scheduler.results, second_raw)
        try:
            assert left.tile == right.tile
            assert NormalizedRegionKey(first_raw) != NormalizedRegionKey(second_raw)
            first_record = scheduler.results._memo[NormalizedRegionKey(first_raw)]
            second_record = scheduler.results._memo[NormalizedRegionKey(second_raw)]
            assert isinstance(first_record, NormalizedRegionResult)
            assert isinstance(second_record, NormalizedRegionResult)
            assert first_record.view == left
            assert second_record.view == right
            counters = dict(ledger.counters)
            _, invalid = audit_tile_results(
                scheduler.results,
                dict(ledger.iter_containers()),
            )
            assert not invalid
            assert dict(ledger.counters) == counters
        finally:
            right_lease.close()
            left_lease.close()


def test_foreign_region_rejects_before_memo_lookup_or_mutation() -> None:
    _, tiles, _adapter, _primitive, scheduler = _runtime(BaseBlockEffect(3))
    _, foreign_tiles, foreign_adapter, foreign_primitive, _ = _runtime(
        BaseBlockEffect(3),
    )
    with _tile(
        foreign_tiles,
        foreign_adapter,
        foreign_primitive,
        (0, 1),
    ) as foreign:
        before = tuple(scheduler.results._memo.items())
        records_before = tuple(tiles._nodes.items())
        with pytest.raises(ValueError, match="different arena"):
            normalize_cached_region(
                scheduler.results,
                BoundaryTileView(foreign.tile, 0, 1),
            )
        assert tuple(scheduler.results._memo.items()) == before
        assert tuple(tiles._nodes.items()) == records_before


def test_region_publication_failure_rolls_back_index_and_application_pins(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    action = adapter.power(primitive, 4)
    with _tile(tiles, adapter, primitive, (4, 0, 1, 2, 3, 4, 4, 4)) as source:
        raw = BoundaryTileView(source.tile, 0, 3, 0, 1)
        with scheduler.application(
            action,
            source.tile,
            adapter.initial_ports(action),
            adapter.wiring(action),
        ) as application:
            memo_before = tuple(scheduler.results._memo.items())
            reverse_before = tuple(scheduler.results._reverse.items())
            dependencies_before = tuple(scheduler._causal_dependencies.records.items())

            def fail_reverse(*_args: object, **_kwargs: object) -> Never:
                raise RuntimeError("injected region reverse-index failure")

            monkeypatch.setattr(scheduler.results, "_write_reverse", fail_reverse)
            with pytest.raises(RuntimeError, match="injected region"):
                normalize_cached_region(
                    scheduler.results,
                    raw,
                    dependencies=scheduler._causal_dependencies,
                    application=application.identity,
                )
            assert tuple(scheduler.results._memo.items()) == memo_before
            assert tuple(scheduler.results._reverse.items()) == reverse_before
            assert tuple(scheduler._causal_dependencies.records.items()) == (
                dependencies_before
            )


def test_stale_application_rejects_before_region_lookup() -> None:
    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    action = adapter.power(primitive, 4)
    with _tile(tiles, adapter, primitive, (4, 0, 1, 2)) as source:
        with scheduler.application(
            action,
            source.tile,
            adapter.initial_ports(action),
            adapter.wiring(action),
        ) as application:
            stale = application.identity
        before = dict(ledger.counters)
        with pytest.raises(ValueError, match="stale or unpublished"):
            normalize_cached_region(
                scheduler.results,
                BoundaryTileView(source.tile, 0, 2, 0, 1),
                dependencies=scheduler._causal_dependencies,
                application=stale,
            )
        after = dict(ledger.counters)
        assert after.pop("tile_region_application_validation_visits") == (
            before.pop("tile_region_application_validation_visits", 0) + 1
        )
        assert after == before


@pytest.mark.parametrize(
    ("field", "invalid", "message"),
    (
        ("relative_extent", True, "extent"),
        ("orientation", 0.0, "orientation"),
    ),
)
def test_forged_region_scalars_reject_before_memo_or_counter_mutation(
    field: str,
    invalid: object,
    message: str,
) -> None:
    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    with _tile(tiles, adapter, primitive, (0, 1)) as source:
        view = BoundaryTileView(source.tile, 0, 1)
        object.__setattr__(view, field, invalid)
        before_memo = tuple(scheduler.results._memo.items())
        before_counters = dict(ledger.counters)
        with pytest.raises((TypeError, ValueError), match=message):
            normalize_cached_region(scheduler.results, view)
        assert tuple(scheduler.results._memo.items()) == before_memo
        assert dict(ledger.counters) == before_counters


def test_region_hit_metrics_forward_from_one_read_only_snapshot() -> None:
    from number_compiler.resources.metric_collection import collect_ledger_metrics

    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    action = adapter.power(primitive, 4)
    with (
        _tile(tiles, adapter, primitive, (4, 0, 1, 2)) as source,
        (
            scheduler.application(
                action,
                source.tile,
                adapter.initial_ports(action),
                adapter.wiring(action),
            )
        ) as application,
    ):
        raw = BoundaryTileView(source.tile, 0, 3, 0, 1)
        _, first = normalize_cached_region(
            scheduler.results,
            raw,
            dependencies=scheduler._causal_dependencies,
            application=application.identity,
        )
        _, second = normalize_cached_region(
            scheduler.results,
            raw,
            dependencies=scheduler._causal_dependencies,
            application=application.identity,
        )
        try:
            snapshot = ledger.snapshot()
            report = collect_ledger_metrics(ledger)
            after = ledger.snapshot()
            assert report.tile_region_normalization_requests == 2
            assert report.tile_region_normalization_misses == 1
            assert report.tile_region_normalization_early_hits == 1
            assert report.tile_region_normalization_publications == 1
            assert report.tile_region_normalization_publication_requests == 1
            assert report.tile_region_application_validation_visits > 0
            # This is the region-result cache level, independent of whatever
            # exact-content interning aliases normalization happened to use.
            assert (
                report.tile_region_normalization_early_hits
                == ledger.counters["tile_region_normalization_early_hits"]
            )
            assert after.counters == snapshot.counters
            assert after.inventory == snapshot.inventory
        finally:
            second.close()
            first.close()


def test_forged_boolean_tile_id_rejects_before_region_lookup() -> None:
    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    with _tile(tiles, adapter, primitive, (0, 1)) as source:
        forged = TileID(source.tile.owner, source.tile.kind, source.tile.local_id)
        object.__setattr__(forged, "local_id", False)
        view = BoundaryTileView(forged, 0, 1)
        before = dict(ledger.counters)
        with pytest.raises((TypeError, ValueError), match="malformed scoped handle"):
            normalize_cached_region(scheduler.results, view)
        assert not scheduler.results._memo
        assert dict(ledger.counters) == before


def test_published_region_detaches_caller_key_and_returned_view() -> None:
    from number_compiler.resources.tile_result_inventory import audit_tile_results

    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    with _tile(tiles, adapter, primitive, (4, 0, 1, 2)) as source:
        raw = BoundaryTileView(source.tile, -3, 3, 0, 1)
        original = BoundaryTileView(source.tile, -3, 3, 0, 1)
        normalized, lease = normalize_cached_region(scheduler.results, raw)
        try:
            object.__setattr__(raw, "relative_extent", 2)
            object.__setattr__(normalized, "relative_origin", 99)
            found = lookup_normalized_region(
                scheduler.results,
                NormalizedRegionKey(original),
            )
            assert found is not None
            assert found.view.relative_origin == -3
            assert found.view.relative_extent == 3
            _, invalid = audit_tile_results(
                scheduler.results,
                dict(ledger.iter_containers()),
            )
            assert not invalid
        finally:
            lease.close()

"""Canonical reverse threshold summaries in the shared tile result owner."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.observation.tile_projection import build_tile_projection
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileOperands
from number_compiler.hashlife.tiles.tile_result_records import (
    ReverseThresholdSummaryKey,
)
from number_compiler.hashlife.tiles.tiles import TileID
from number_compiler.resources.ledger import ResourceLedger
from tests.support.diamond_runtime import oracle


@pytest.mark.parametrize(
    ("pair", "growth", "width"),
    (
        ((4, 2, 4), 1, 4),
        ((0, 2, 0), 0, 3),
        ((2, 2, 2), 0, 3),
    ),
)
def test_reverse_width_consumes_current_threshold_summary(
    pair: tuple[int, ...],
    growth: int,
    width: int,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    source = ExactSource(pair, 3, blank=5, extent=4, alphabet_size=5)
    with build_tile_projection(
        BaseBlockEffect(3),
        SourceGeometry(ledger, source),
    ) as projection:
        application = projection._application
        summary = projection.scheduler.results.reverse_threshold_summary(
            application.source,
            3,
        )
        assert int(summary.last_reset_sign > 0) == growth

        def forbidden_point(*_args: object, **_kwargs: object) -> int:
            raise AssertionError("current growth scanned an exact output position")

        monkeypatch.setattr(projection.scheduler.tiles, "point", forbidden_point)
        assert projection.active_width() == width
        assert ledger.counters["reverse_current_growth_width_shortcuts"] == 1
        assert ledger.counters["reverse_threshold_summary_early_hits"] > 0


def test_reverse_interface_uses_closed_arithmetic_without_boolean_mask_rewrite() -> (
    None
):
    ledger = ResourceLedger()
    source = ExactSource((4, 2, 4), 3, blank=5, extent=4, alphabet_size=5)
    with build_tile_projection(
        BaseBlockEffect(3), SourceGeometry(ledger, source)
    ) as projection:
        projection._application.interface()
        assert ledger.counters.get("quotient_arithmetic_normalizations", 0) > 0
        assert ledger.counters.get("quotient_atomic_mask_elisions", 0) == 0
        assert ledger.counters.get("quotient_atomic_mask_validation_nodes", 0) == 0


def test_reverse_threshold_summary_is_radix_scoped_before_lookup() -> None:
    ledger = ResourceLedger()
    source = ExactSource((4, 2, 4), 3, blank=5, extent=4, alphabet_size=5)
    with build_tile_projection(
        BaseBlockEffect(3),
        SourceGeometry(ledger, source),
    ) as projection:
        results = projection.scheduler.results
        tile = projection._application.source
        before = ledger.counters.get("reverse_threshold_summary_requests", 0)
        with pytest.raises(ValueError, match="canonical reverse pair"):
            results.reverse_threshold_summary(tile, 4)
        assert ledger.counters.get("reverse_threshold_summary_requests", 0) == before
        results.reverse_threshold_summary(tile, 3)
        assert any(type(key) is ReverseThresholdSummaryKey for key in results._memo)
    assert not any(type(key) is ReverseThresholdSummaryKey for key in results._memo)


def test_reverse_threshold_summary_elides_only_proved_missing_reprobes() -> None:
    ledger = ResourceLedger()
    source = ExactSource((0, 1, 2, 3), 3, blank=5, extent=4, alphabet_size=5)
    with build_tile_projection(
        BaseBlockEffect(3),
        SourceGeometry(ledger, source),
    ) as projection:
        results = projection.scheduler.results
        tile = projection._application.source
        pending = [tile]
        seen: set[TileID] = set()
        active_internal_nodes = 0
        while pending:
            current = pending.pop()
            if current in seen:
                continue
            seen.add(current)
            node = projection.scheduler.tiles.resolve(current)
            if node.first_active is None or not node.level:
                continue
            assert node.left is not None and node.right is not None
            active_internal_nodes += 1
            pending.extend((node.left, node.right))
        first = results.reverse_threshold_summary(tile, 3)
        assert first.length == 4
        assert (
            ledger.counters["reverse_threshold_summary_known_missing_probe_elisions"]
            == active_internal_nodes + 1
        )
        requests = ledger.counters["reverse_threshold_summary_requests"]
        hits = ledger.counters["reverse_threshold_summary_early_hits"]
        elisions = ledger.counters[
            "reverse_threshold_summary_known_missing_probe_elisions"
        ]

        second = results.reverse_threshold_summary(tile, 3)
        assert second is first
        assert ledger.counters["reverse_threshold_summary_requests"] == requests + 1
        assert ledger.counters["reverse_threshold_summary_early_hits"] == hits + 1
        assert (
            ledger.counters["reverse_threshold_summary_known_missing_probe_elisions"]
            == elisions
        )


@pytest.mark.parametrize(
    "pair",
    (
        (5, 5, 5, 5),
        (5, 4),
        (4, 5, 4),
    ),
)
def test_reverse_growth_shortcut_declines_noncontiguous_active_prefixes(
    pair: tuple[int, ...],
) -> None:
    ledger = ResourceLedger()
    source = ExactSource(pair, 3, blank=5, extent=4, alphabet_size=6)
    with build_tile_projection(
        BaseBlockEffect(3),
        SourceGeometry(ledger, source),
    ) as projection:
        application = projection._application
        before = ledger.counters.get("reverse_current_growth_width_shortcuts", 0)
        adapter = projection.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter
        assert (
            adapter.current_growth(
                application.action,
                application.source,
                application.ports,
                application.wiring,
                BoundaryTileOperands(),
            )
            is None
        )
        assert (
            ledger.counters.get("reverse_current_growth_width_shortcuts", 0) == before
        )
        assert not any(
            type(key) is ReverseThresholdSummaryKey and key.input == application.source
            for key in projection.scheduler.results._memo
        )
        expected = oracle(BaseBlockEffect(3), pair, 4, 1)
        assert projection.active_width() == max(
            (position + 1 for position, symbol in enumerate(expected) if symbol != 5),
            default=0,
        )
        assert tuple(projection.point(position) for position in range(4)) == tuple(
            expected
        )

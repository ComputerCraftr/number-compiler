"""Prime observations consume admitted images without reconstructing their counts."""

from __future__ import annotations

from dataclasses import replace
from math import gcd
from typing import Never, cast

import pytest

from number_compiler.hashlife.execution.source_bound_images import SourceImageDemand
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG
from number_compiler.sequences.prime.successor_action import (
    PrimeSuccessorActionArena,
    PrimeSuccessorImageAdapter,
    PrimeSuccessorImagePayload,
    PrimeSuccessorPortEffect,
    PrimeSuccessorSource,
)


def _forbidden(*args: object, **kwargs: object) -> Never:
    raise AssertionError("admitted endpoint projection reconstructed its count")


@pytest.mark.parametrize("width", [0, 1, 11, 30, 41])
@pytest.mark.parametrize("phase", [0, 1, 4])
@pytest.mark.parametrize("forbidden", [(0,), (0, 2)])
def test_endpoint_and_effect_use_admitted_support(
    monkeypatch: pytest.MonkeyPatch,
    width: int,
    phase: int,
    forbidden: tuple[int, ...],
) -> None:
    dag = CoprimeRankDAG((2, 3), max_states=20_000, max_work=200_000)
    arena = PrimeSuccessorActionArena(dag, 5, forbidden_residues=forbidden)
    adapter = PrimeSuccessorImageAdapter(arena)
    scheduler = TileScheduler.source_only(dag.ledger)
    scheduler.register_source_image_adapter(adapter)
    try:
        action = arena.prefix(width)
        source = PrimeSuccessorSource(arena.descriptor_id, phase)
        image = scheduler.source_image_demanded(
            adapter, source, action, SourceImageDemand("rank-before", (width,))
        )
        parent = sum(gcd(n, 6) == 1 for n in range(1, width + 1))
        survivors = sum(
            gcd(n, 6) == 1 and (n + phase) % 5 not in forbidden
            for n in range(1, width + 1)
        )
        expected = PrimeSuccessorPortEffect(
            phase, (phase + width) % 5, parent, parent - survivors, survivors
        )
        for name in ("rank_before", "port_effect", "_interval_effect"):
            monkeypatch.setattr(arena, name, _forbidden)
        monkeypatch.setattr(dag, "count", _forbidden)
        monkeypatch.setattr(dag, "count_progression", _forbidden)
        assert (
            scheduler.source_projection(
                adapter, image, SourceImageDemand("effect")
            ).value
            == expected
        )
        assert (
            scheduler.source_projection(
                adapter, image, SourceImageDemand("rank-before", (width,))
            ).value
            == survivors
        )
        assert (
            scheduler.source_projection(
                adapter, image, SourceImageDemand("rank-before", (0,))
            ).value
            == 0
        )
        if width > 1:
            before = dag.ledger.entries, dag.ledger.nodes
            with pytest.raises(AssertionError, match="reconstructed"):
                scheduler.source_projection(
                    adapter, image, SourceImageDemand("rank-before", (width - 1,))
                )
            assert (dag.ledger.entries, dag.ledger.nodes) == before
        assert dag.ledger.counters["prime_successor_image_effect_projections"] == 1
    finally:
        scheduler.dispose_source_images()
        arena.close()
        dag.close()
    assert dag.ledger.entries == dag.ledger.nodes == 0


@pytest.mark.parametrize("warm", [False, True])
def test_endpoint_projection_rejects_changed_published_counts(warm: bool) -> None:
    dag = CoprimeRankDAG((2, 3), max_states=20_000, max_work=200_000)
    arena = PrimeSuccessorActionArena(dag, 5)
    adapter = PrimeSuccessorImageAdapter(arena)
    scheduler = TileScheduler.source_only(dag.ledger)
    scheduler.register_source_image_adapter(adapter)
    try:
        image = scheduler.source_image_demanded(
            adapter,
            PrimeSuccessorSource(arena.descriptor_id, 0),
            arena.prefix(41),
            SourceImageDemand("rank-before", (41,)),
        )
        demand = SourceImageDemand("rank-before", (41,))
        if warm:
            scheduler.source_projection(adapter, image, demand)
        payload = cast(
            PrimeSuccessorImagePayload,
            scheduler._source_image_core().view(image).payload,
        )
        original = payload.surviving_values, payload.deleted_survivors
        try:
            object.__setattr__(payload, "surviving_values", original[0] - 1)
            object.__setattr__(payload, "deleted_survivors", original[1] + 1)
            with pytest.raises(ValueError, match="altered"):
                scheduler.source_projection(adapter, image, demand)
        finally:
            object.__setattr__(payload, "surviving_values", original[0])
            object.__setattr__(payload, "deleted_survivors", original[1])
    finally:
        scheduler.dispose_source_images()
        arena.close()
        dag.close()


def test_payload_rejects_boolean_counts_and_wrong_phase() -> None:
    dag = CoprimeRankDAG((2, 3), max_states=20_000, max_work=200_000)
    arena = PrimeSuccessorActionArena(dag, 5)
    adapter = PrimeSuccessorImageAdapter(arena)
    try:
        payload = PrimeSuccessorImagePayload(
            arena.descriptor_id, arena.prefix(1), 0, 1, 1, 0, 1
        )
        adapter.validate_payload(payload)
        for invalid in (
            replace(payload, surviving_values=True),
            replace(payload, entering_phase=False),
            replace(payload, outgoing_phase=2),
            replace(payload, parent_survivors=2, surviving_values=2),
        ):
            with pytest.raises(
                ValueError, match="invalid prime successor image payload"
            ):
                adapter.validate_payload(invalid)
    finally:
        arena.close()
        dag.close()


@pytest.mark.parametrize("nested", [False, True])
@pytest.mark.parametrize("phase", range(5))
@pytest.mark.parametrize("forbidden", [(0,), (0, 2)])
def test_whole_period_extent_keeps_internal_parent_seams(
    nested: bool, phase: int, forbidden: tuple[int, ...]
) -> None:
    dag = CoprimeRankDAG((2, 3), max_states=20_000, max_work=500_000)
    arena = PrimeSuccessorActionArena(dag, 5, forbidden_residues=forbidden)
    try:
        # Prefix 24 splits 8+16, not on W=6. A 6+24 parent is aligned at
        # its own split but still contains that unaligned descendant.
        action = (
            arena.compose(arena.base, arena.prefix(24)) if nested else arena.prefix(30)
        )
        expected = [
            n - 1
            for n in range(1, 31)
            if gcd(n, 6) == 1 and (n + phase) % 5 not in forbidden
        ]
        assert arena.port_effect(action, phase).surviving_values == len(expected)
        for stop in range(31):
            assert arena.rank_before(action, phase, stop) == sum(
                offset < stop for offset in expected
            )
        assert [
            arena.select(action, phase, k) for k in range(len(expected))
        ] == expected
    finally:
        arena.close()
        dag.close()


@pytest.mark.parametrize("phase", range(5))
@pytest.mark.parametrize("forbidden", [(0,), (0, 2)])
def test_period_action_after_partial_prefix_transports_parent_offset(
    phase: int, forbidden: tuple[int, ...]
) -> None:
    dag = CoprimeRankDAG((2, 3), max_states=20_000, max_work=500_000)
    arena = PrimeSuccessorActionArena(dag, 5, forbidden_residues=forbidden)
    adapter = PrimeSuccessorImageAdapter(arena)
    scheduler = TileScheduler.source_only(dag.ledger)
    scheduler.register_source_image_adapter(adapter)
    try:
        action = arena.compose(arena.prefix(1), arena.base)
        image = scheduler.source_image_demanded(
            adapter,
            PrimeSuccessorSource(arena.descriptor_id, phase),
            action,
            SourceImageDemand("effect"),
        )
        expected = sum(
            gcd(n, 6) == 1 and (n + phase) % 5 not in forbidden for n in range(1, 8)
        )
        assert (
            scheduler.source_projection(
                adapter, image, SourceImageDemand("rank-before", (7,))
            ).value
            == expected
        )
    finally:
        scheduler.dispose_source_images()
        arena.close()
        dag.close()

"""Public scheduler demand must enter the arbitrary-depth causal recurrence."""

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.tiles.tile_results import ResultLease
from number_compiler.hashlife.tiles.tiles import TileLease
from tests.support.tile_kernel import (
    make_tile_from_symbols,
    make_tile_runtime,
    make_tile_runtime_source,
)


@pytest.mark.parametrize(
    "exponent,expected",
    (
        (4, (2, 0, 0, 4)),
        (8, (2, 4, 0, 2)),
    ),
)
def test_scheduler_deep_point_uses_causal_tiles_without_complete_midpoint(
    monkeypatch: pytest.MonkeyPatch,
    exponent: int,
    expected: tuple[int, int, int, int],
) -> None:
    ledger, _unused_tiles_binding, adapter, primitive, scheduler, source = (
        make_tile_runtime_source(BaseBlockEffect(3), (0, 0, 0, 1))
    )
    action = adapter.power(primitive, exponent)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("deep point requested a compulsory midpoint or final root")

    with (
        source,
        scheduler.application(
            action,
            source.tile,
            adapter.initial_ports(action),
            adapter.wiring(action),
        ) as application,
    ):
        monkeypatch.setattr(scheduler, "complete", forbidden)
        monkeypatch.setattr(adapter, "temporal_before_context", forbidden)
        monkeypatch.setattr(adapter, "temporal_after_context", forbidden)
        monkeypatch.setattr(CausalTileEngine, "output", forbidden)
        assert tuple(application.point(i) for i in range(4)) == expected
        assert application.audit_snapshot().root_lease is None
        assert ledger.counters["powered_absorption_max_span"] == exponent
        assert ledger.counters["powered_absorption_successes"] == 4
        assert ledger.counters["tile_causal_frames"] > 0
        assert ledger.counters.get("tile_temporal_complete_frames", 0) == 0


@pytest.mark.parametrize("exponent", (4, 8))
def test_causal_completed_parent_agrees_with_independent_midpoint_semantics(
    exponent: int,
) -> None:
    from number_compiler.hashlife.interfaces.semantic_structures import (
        COMPONENT_ROLES,
    )
    from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey

    runtimes = [make_tile_runtime(BaseBlockEffect(3)) for _ in range(2)]
    sources: list[TileLease] = []
    leases: list[TileLease | ResultLease] = []
    try:
        results: list[tuple[object, ...]] = []
        for index, (_ledger, tiles, adapter, primitive, scheduler) in enumerate(
            runtimes
        ):
            source = make_tile_from_symbols(tiles, adapter, primitive, (0, 0, 0, 1))
            sources.append(source)
            action = adapter.power(primitive, exponent)
            key = PoweredResultKey(
                action,
                source.tile,
                adapter.initial_ports(action),
                adapter.wiring(action),
            )
            if not index:
                output = CausalTileEngine(scheduler).output(action, source.tile)
                leases.append(output)
                result = scheduler.results.lookup(key)
                assert result is not None, "completed causal parent was not memoized"
            else:
                from number_compiler.hashlife.execution.tile_temporal import (
                    complete_temporal,
                )

                result = complete_temporal(scheduler, key)
            leases.append(result)
            value = result.result
            channels = tuple(
                adapter.observe(value.outgoing, name, (left, right))
                for left in range(adapter.primitive_law(primitive).left_count)
                for right in range(adapter.primitive_law(primitive).right_count)
                for name in COMPONENT_ROLES
            )
            results.append(
                (
                    tuple(tiles.point(value.output, i) for i in range(4)),
                    value.outgoing_ports,
                    value.physical_ticks,
                    value.event_weight,
                    value.frame_shift,
                    value.relative_origin,
                    value.relative_extent,
                    channels,
                )
            )
        assert results[0] == results[1]
    finally:
        for lease in reversed(leases):
            lease.close()
        for source in sources:
            source.close()


@pytest.mark.parametrize("exponent", (4, 8))
def test_scheduler_deep_explicit_edges_preserve_noninitial_consumer(
    monkeypatch: pytest.MonkeyPatch, exponent: int
) -> None:
    from number_compiler.hashlife.tiles.tile_ports import (
        BoundPorts,
        FusedBoundaryContract,
    )
    from tests.arithmetic.contracts.test_tile_causal_private import scan

    _ledger, tiles, adapter, primitive, scheduler = make_tile_runtime(
        BaseBlockEffect(3)
    )
    symbols = (2, 0, 0, 4)
    source = make_tile_from_symbols(tiles, adapter, primitive, symbols)
    action = adapter.power(primitive, exponent)
    wiring = adapter.wiring(action)
    producer, consumer = (0, 0), (0, 1)
    contract = FusedBoundaryContract(
        BoundPorts(producer, wiring), BoundPorts(consumer, wiring)
    )
    expected: tuple[int, ...] = symbols
    for stage in range(exponent):
        ports = (
            producer
            if stage == exponent // 2 - 1
            else (
                consumer if stage == exponent - 1 else adapter.initial_ports(primitive)
            )
        )
        expected = scan(adapter.primitive_law(primitive), expected, ports)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("explicit causal edge reset through a midpoint executor")

    with source:
        monkeypatch.setattr(scheduler, "complete", forbidden)
        monkeypatch.setattr(adapter, "temporal_before_context", forbidden)
        monkeypatch.setattr(adapter, "temporal_after_context", forbidden)
        assert (
            tuple(
                scheduler.point(
                    action,
                    source.tile,
                    consumer,
                    wiring,
                    coordinate,
                    fusion=contract,
                )
                for coordinate in range(4)
            )
            == expected
        )


@pytest.mark.parametrize("exponent", (4, 8))
def test_warm_causal_parent_reads_exact_result_without_execution(
    monkeypatch: pytest.MonkeyPatch, exponent: int
) -> None:
    from number_compiler.hashlife.interfaces import (
        tile_reverse_functions as reverse_ports,
    )

    _ledger, tiles, adapter, primitive, scheduler, source = make_tile_runtime_source(
        BaseBlockEffect(3), (0, 0, 0, 1)
    )
    action = adapter.power(primitive, exponent)
    with (
        source,
        scheduler.application(
            action,
            source.tile,
            adapter.initial_ports(action),
            adapter.wiring(action),
        ) as application,
    ):
        result = application.complete()
        expected = tuple(tiles.point(result.output, i) for i in range(4))
        expected_width = tiles.active_width(result.output)

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("warm causal parent executed a descendant")

        monkeypatch.setattr(CausalTileEngine, "_run", forbidden)
        monkeypatch.setattr(reverse_ports, "reverse_leaf_components", forbidden)
        monkeypatch.setattr(adapter, "leaf_components", forbidden)
        monkeypatch.setattr(adapter, "parent_components", forbidden)
        monkeypatch.setattr(tiles, "leaf", forbidden)
        monkeypatch.setattr(tiles, "join", forbidden)
        assert tuple(application.point(i) for i in range(4)) == expected
        assert application.width() == expected_width


@pytest.mark.parametrize("exponent", (4, 8))
def test_scheduler_deep_width_uses_activity_tasks_without_endpoint(
    monkeypatch: pytest.MonkeyPatch, exponent: int
) -> None:
    from tests.arithmetic.contracts.test_tile_causal_private import scan

    ledger, tiles, adapter, primitive, scheduler = make_tile_runtime(BaseBlockEffect(3))
    values = (0, 0, 1, 5)
    expected: tuple[int, ...] = values
    for _ in range(exponent):
        expected = scan(
            adapter.primitive_law(primitive), expected, adapter.initial_ports(primitive)
        )
    action = adapter.power(primitive, exponent)
    with (
        make_tile_from_symbols(tiles, adapter, primitive, values) as source,
        scheduler.application(
            action,
            source.tile,
            adapter.initial_ports(action),
            adapter.wiring(action),
        ) as application,
    ):

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError(
                "causal width requested a point scan or complete endpoint"
            )

        monkeypatch.setattr(scheduler, "complete", forbidden)
        monkeypatch.setattr(scheduler, "point", forbidden)
        monkeypatch.setattr(CausalTileEngine, "output", forbidden)
        monkeypatch.setattr(adapter, "temporal_before_context", forbidden)
        for limit in range(5):
            width = max((i + 1 for i in range(limit) if expected[i] != 5), default=0)
            assert application.width(limit) == width
        assert application.audit_snapshot().root_lease is None
        assert ledger.counters["powered_absorption_max_span"] == exponent

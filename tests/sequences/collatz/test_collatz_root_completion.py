"""Complete-result gates for the certified first Collatz root event."""

from __future__ import annotations

from itertools import product
from typing import Any

import pytest

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.tile_causal_entry import causal_complete
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.interfaces.diamond_quotient import COMPONENT_ROLES
from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
from number_compiler.hashlife.tiles.tiles import TileID
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from number_compiler.sequences.collatz.tile_root_completion import complete_collatz_root
from tests.support.tile_kernel import _runtime, _tile


def _request(
    adapter: PrimitiveTileKernelAdapter, action: FieldCellActionID, tile: TileID
) -> PoweredResultKey:
    return PoweredResultKey(
        action, tile, adapter.initial_ports(action), adapter.wiring(action)
    )


def _case(valuation: int, ticks: int) -> tuple[Any, ...]:
    ledger, tiles, adapter, primitive, scheduler = _runtime(
        CollatzPhysicalBlockEffect()
    )
    seed = ((1 << valuation) - 1) // 3
    width = 1 << (valuation + 2).bit_length()
    digits = tuple(
        (seed >> coordinate) & 1 if coordinate < seed.bit_length() else 2
        for coordinate in range(width)
    )
    return ledger, tiles, adapter, primitive, scheduler, digits


def _snapshot(
    tiles: Any,
    adapter: Any,
    primitive: Any,
    result: Any,
) -> tuple[object, ...]:
    value = result.result
    node = tiles.resolve(value.output)
    output = tuple(
        tiles.point(value.output, coordinate) for coordinate in range(node.width)
    )
    boundaries = tuple(
        None
        if view is None
        else (
            tuple(
                tiles.point(view.tile, coordinate)
                for coordinate in range(tiles.resolve(view.tile).width)
            ),
            view.relative_origin,
            view.relative_extent,
            view.orientation,
            view.source_offset,
        )
        for view in (value.outgoing_boundaries.left, value.outgoing_boundaries.right)
    )
    law = adapter.primitive_law(primitive)
    interface = tuple(
        (
            ports,
            tuple(
                adapter._observe(value.outgoing, channel, ports)
                for channel in COMPONENT_ROLES
            ),
        )
        for ports in product(range(law.left_count), range(law.right_count))
    )
    return (
        output,
        interface,
        value.outgoing_ports,
        value.physical_ticks,
        value.event_weight,
        value.frame_shift,
        value.relative_origin,
        value.relative_extent,
        boundaries,
        value.fusion,
        value.observed_input_ports,
    )


@pytest.mark.parametrize("ticks", (3, 4, 5))
def test_initial_root_completion_matches_full_causal_result(ticks: int) -> None:
    oracle_runtime = _case(4, ticks)
    _, oracle_tiles, oracle_adapter, oracle_primitive, oracle_scheduler, digits = (
        oracle_runtime
    )
    with _tile(oracle_tiles, oracle_adapter, oracle_primitive, digits) as source:
        action = oracle_adapter.power(oracle_primitive, ticks)
        key = PoweredResultKey(
            action,
            source.tile,
            oracle_adapter.initial_ports(action),
            oracle_adapter.wiring(action),
        )
        oracle = causal_complete(oracle_scheduler, key)
        assert oracle is not None
        try:
            expected = _snapshot(oracle_tiles, oracle_adapter, oracle_primitive, oracle)
        finally:
            oracle.close()

    runtime = _case(4, ticks)
    ledger, tiles, adapter, primitive, scheduler, digits = runtime
    with _tile(tiles, adapter, primitive, digits) as source:
        action = adapter.power(primitive, ticks)
        key = _request(adapter, action, source.tile)
        actual = complete_collatz_root(scheduler, key)
        assert actual is not None
        try:
            assert _snapshot(tiles, adapter, primitive, actual) == expected
        finally:
            actual.close()
        assert ledger.counters["tile_collatz_initial_root_completions"] == 1
        assert ledger.counters["collatz_initial_root_structural_shifts"] == 1
        assert ledger.counters["collatz_initial_root_skipped_ticks"] == ticks - 2


def test_initial_root_completion_executes_two_primitive_fields(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.hashlife.execution.tile_causal_entry as entry

    _, tiles, adapter, primitive, scheduler, digits = _case(8, 8)
    calls: list[object] = []
    original = entry.causal_complete

    def primitive_only(local_scheduler: Any, key: PoweredResultKey) -> Any:
        calls.append(key.action)
        assert key.action == primitive, "root completion replayed a temporal power"
        return original(local_scheduler, key)

    monkeypatch.setattr(entry, "causal_complete", primitive_only)
    with _tile(tiles, adapter, primitive, digits) as source:
        action = adapter.power(primitive, 8)
        key = _request(adapter, action, source.tile)
        result = complete_collatz_root(scheduler, key)
        assert result is not None
        result.close()
    assert calls == [primitive, primitive]


@pytest.mark.parametrize("valuation", (6, 9, 32, 128))
@pytest.mark.parametrize("phase", ("early", "middle", "complete"))
def test_scheduler_completes_varied_root_cylinders_with_two_primitive_scans(
    monkeypatch: pytest.MonkeyPatch,
    valuation: int,
    phase: str,
) -> None:
    import number_compiler.hashlife.execution.tile_causal_entry as entry

    angular = 7 if valuation % 2 == 0 else 5
    ticks = {
        "early": 3,
        "middle": 1 + valuation // 2,
        "complete": valuation + 1,
    }[phase]
    seed = (angular * (1 << valuation) - 1) // 3
    width = 1 << (seed.bit_length() + 3).bit_length()
    digits = tuple(
        (seed >> coordinate) & 1 if coordinate < seed.bit_length() else 2
        for coordinate in range(width)
    )
    ledger, tiles, adapter, primitive, scheduler = _runtime(
        CollatzPhysicalBlockEffect()
    )
    calls: list[object] = []
    original = entry.causal_complete

    def primitive_only(local_scheduler: Any, request: PoweredResultKey) -> Any:
        calls.append(request.action)
        assert request.action == primitive, "scheduler replayed the temporal root run"
        return original(local_scheduler, request)

    monkeypatch.setattr(entry, "causal_complete", primitive_only)
    with _tile(tiles, adapter, primitive, digits) as source:
        action = adapter.power(primitive, ticks)
        result = scheduler.complete(
            action,
            source.tile,
            adapter.initial_ports(action),
            adapter.wiring(action),
        )
        try:
            value = result.result
            expected = (3 * seed + 1) >> (ticks - 1)
            node = tiles.resolve(value.output)
            assert tuple(
                tiles.point(value.output, coordinate)
                for coordinate in range(node.width)
            ) == tuple(
                (expected >> coordinate) & 1
                if coordinate < expected.bit_length()
                else 2
                for coordinate in range(node.width)
            )
            assert (value.physical_ticks, value.event_weight, value.frame_shift) == (
                ticks,
                1,
                0,
            )
        finally:
            result.close()
    assert calls == [primitive, primitive]
    assert ledger.counters["tile_collatz_initial_root_completions"] == 1


def test_scheduler_root_result_hits_cache_and_has_balanced_inventory() -> None:
    ledger, tiles, adapter, primitive, scheduler, digits = _case(6, 5)
    with _tile(tiles, adapter, primitive, digits) as source:
        action = adapter.power(primitive, 5)
        ports, wiring = adapter.initial_ports(action), adapter.wiring(action)
        first = scheduler.complete(action, source.tile, ports, wiring)
        second = scheduler.complete(action, source.tile, ports, wiring)
        try:
            assert second.result == first.result
            with scheduler.application(
                action, source.tile, ports, wiring
            ) as application:
                before = ledger.counters.get("tile_collatz_initial_root_completions", 0)
                first_payload = application.interface()
                assert application.interface() == first_payload
                assert (
                    ledger.counters.get("tile_collatz_initial_root_completions", 0)
                    == before
                )
        finally:
            second.close()
            first.close()
    assert ledger.counters["tile_scheduler_parent_early_hits"] > 0
    assert all(row.accounting_delta in (None, 0) for row in ledger.inventory())


def test_initial_root_completion_declines_after_first_event() -> None:
    _, tiles, adapter, primitive, scheduler = _runtime(CollatzPhysicalBlockEffect())
    with _tile(tiles, adapter, primitive, (1, 1, 2, 2, 2, 2, 2, 2)) as source:
        action = adapter.power(primitive, 8)
        key = _request(adapter, action, source.tile)
        assert complete_collatz_root(scheduler, key) is None

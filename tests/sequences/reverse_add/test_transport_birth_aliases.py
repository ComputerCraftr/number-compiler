"""Transport/carry cancellation shares exact successors and their future work."""

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from tests.support.tile_kernel import make_tile_from_symbols, make_tile_runtime


@pytest.mark.parametrize(
    ("first", "second", "successor"),
    (
        ((10, 0, 0, 10), (10, 9, 9, 10), (1, 1, 0, 1, 1)),
        (
            (0, 9, 9, 10, 10, 9, 9, 0),
            (0, 14, 14, 0, 0, 14, 14, 0),
            (1, 9, 9, 1, 1, 9, 9, 1),
        ),
    ),
)
def test_distinct_carry_geometries_share_successor_and_completed_consumer(
    monkeypatch: pytest.MonkeyPatch,
    first: tuple[int, ...],
    second: tuple[int, ...],
    successor: tuple[int, ...],
) -> None:
    ledger, tiles, adapter, primitive, scheduler = make_tile_runtime(
        BaseBlockEffect(10)
    )
    # Active zeroes are part of the declared pair field, unlike blank padding.
    # Fixed equal extents make exact content sharing independent of provenance.
    blank, extent = 19, 16
    ports, wiring = adapter.initial_ports(primitive), adapter.wiring(primitive)
    later = adapter.power(primitive, 2)
    with (
        make_tile_from_symbols(
            tiles, adapter, primitive, first + (blank,) * (extent - len(first))
        ) as a,
        make_tile_from_symbols(
            tiles, adapter, primitive, second + (blank,) * (extent - len(second))
        ) as b,
        scheduler.complete(primitive, a.tile, ports, wiring) as output_a,
        scheduler.complete(primitive, b.tile, ports, wiring) as output_b,
    ):
        assert a.tile != b.tile
        expected = successor + (blank,) * (extent - len(successor))
        assert tuple(tiles.point(output_a.output, i) for i in range(extent)) == expected
        assert output_a.output == output_b.output
        with scheduler.complete(
            later,
            output_a.output,
            adapter.initial_ports(later),
            adapter.wiring(later),
        ) as advanced:
            hits = ledger.counters.get("tile_scheduler_parent_early_hits", 0)

            def forbidden(*_args: object, **_kwargs: object) -> Never:
                raise AssertionError(
                    "equivalent successor replayed its producing field"
                )

            monkeypatch.setattr(adapter, "leaf_interface_symbol", forbidden)
            monkeypatch.setattr(adapter, "child_context", forbidden)
            monkeypatch.setattr(scheduler, "_complete_direct", forbidden)
            with scheduler.complete(
                later,
                output_b.output,
                adapter.initial_ports(later),
                adapter.wiring(later),
            ) as reused:
                assert reused.result == advanced.result
                assert ledger.counters["tile_scheduler_parent_early_hits"] == hits + 1

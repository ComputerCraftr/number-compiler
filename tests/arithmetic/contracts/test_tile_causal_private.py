"""First executable arbitrary-depth causal absorption gate."""

from __future__ import annotations

from typing import TYPE_CHECKING, Never

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from tests.support.tile_kernel import (
    _runtime,
    _runtime_source,
    _symbols,
    _tile,
    powered_runtime_source,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.diamond_kernel import PrimitiveKernel


def test_causal_macro_recurrence_p4_p8_without_temporal_midpoint(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    effect = BaseBlockEffect(3)
    ledger, tiles, adapter, primitive, scheduler, source = _runtime_source(
        effect, (0, 0, 0, 1)
    )

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError(
            "causal recurrence entered the completed-midpoint executor"
        )

    monkeypatch.setattr(scheduler, "complete", forbidden)
    monkeypatch.setattr(adapter, "temporal_before_context", forbidden)
    monkeypatch.setattr(adapter, "temporal_after_context", forbidden)
    try:
        engine = CausalTileEngine(scheduler)
        for exponent, expected in (
            (4, (2, 0, 0, 4)),
            (8, (2, 4, 0, 2)),
        ):
            action = adapter.power(primitive, exponent)
            with (
                scheduler.application(
                    action,
                    source.tile,
                    adapter.initial_ports(action),
                    adapter.wiring(action),
                ) as application,
                monkeypatch.context() as point_poison,
            ):
                point_poison.setattr(engine, "output", forbidden)
                assert (
                    tuple(
                        engine.point(
                            action,
                            source.tile,
                            i,
                            application=application.identity,
                        )
                        for i in range(4)
                    )
                    == expected
                )
            with engine.output(action, source.tile) as output:
                assert _symbols(tiles, output.tile) == expected
        assert ledger.counters.get("tile_causal_frames", 0) > 0
        assert ledger.counters.get("tile_causal_result_hits", 0) > 0
        assert ledger.counters.get("tile_temporal_complete_frames", 0) == 0
    finally:
        source.close()


def _scan(
    kernel: PrimitiveKernel,
    symbols: tuple[int, ...],
    ports: tuple[int, int],
) -> tuple[int, ...]:
    from number_compiler.arithmetic.contracts.block_effect import BoundarySide

    left, right = ports
    left_states, right_states = [], []
    for symbol in symbols:
        left_states.append(left)
        left = kernel.advance(BoundarySide.LEFT, left, symbol)
    for symbol in reversed(symbols):
        right_states.append(right)
        right = kernel.advance(BoundarySide.RIGHT, right, symbol)
    return tuple(
        kernel.emit(a, symbol, b)
        for a, symbol, b in zip(
            left_states,
            symbols,
            reversed(right_states),
            strict=True,
        )
    )


def test_causal_p4_p8_explicit_noninitial_edge_contract() -> None:
    from number_compiler.hashlife.tiles.tile_ports import (
        BoundPorts,
        FusedBoundaryContract,
    )

    effect = BaseBlockEffect(3)
    _ledger, tiles, adapter, primitive, scheduler = _runtime(effect)
    source_symbols = (0, 0, 0, 1)
    source = _tile(tiles, adapter, primitive, source_symbols)
    producer, consumer = (1, 0), (0, 1)
    try:
        engine = CausalTileEngine(scheduler)
        for exponent in (4, 8):
            action = adapter.power(primitive, exponent)
            wiring = adapter.wiring(action)
            contract = FusedBoundaryContract(
                BoundPorts(producer, wiring),
                BoundPorts(consumer, wiring),
            )
            expected: tuple[int, ...] = source_symbols
            for stage in range(exponent):
                ports = (
                    producer
                    if stage == exponent // 2 - 1
                    else consumer
                    if stage == exponent - 1
                    else adapter.initial_ports(primitive)
                )
                expected = _scan(adapter.primitive_law(primitive), expected, ports)
            assert (
                tuple(
                    engine.point_bound(action, source.tile, i, contract)
                    for i in range(4)
                )
                == expected
            )
    finally:
        source.close()


def test_repeated_point_reuses_completed_causal_leaf(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    effect = BaseBlockEffect(3)
    ledger, _unused_tiles_binding, adapter, primitive, scheduler, source = (
        _runtime_source(effect, (0, 0, 0, 1))
    )
    action = adapter.power(primitive, 8)
    with (
        source,
        scheduler.application(
            action,
            source.tile,
            adapter.initial_ports(action),
            adapter.wiring(action),
        ) as application,
    ):
        assert application.point(2) == 0
        emits = ledger.counters.get("tile_causal_primitive_emits", 0)

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("warm causal point replayed a primitive evaluator")

        monkeypatch.setattr(adapter, "leaf_interface", forbidden)
        monkeypatch.setattr(adapter, "primitive_law", forbidden)
        assert application.point(2) == 0
        assert ledger.counters.get("tile_causal_primitive_emits", 0) == emits
        assert ledger.counters.get("tile_causal_result_hits", 0) > 0


def test_causal_output_consumes_an_already_completed_midpoint() -> None:
    effect = BaseBlockEffect(3)
    ledger, tiles, adapter, primitive, scheduler, source = _runtime_source(
        effect, (0, 0, 0, 1)
    )
    square = adapter.power(primitive, 2)
    fourth = adapter.power(primitive, 4)
    try:
        engine = CausalTileEngine(scheduler)
        with engine.output(square, source.tile) as midpoint:
            assert _symbols(tiles, midpoint.tile) == (0, 0, 0, 4)
            before = ledger.counters.get("tile_causal_midpoint_reuse", 0)
            with engine.output(fourth, source.tile) as output:
                assert _symbols(tiles, output.tile) == (2, 0, 0, 4)
            assert ledger.counters.get("tile_causal_midpoint_reuse", 0) > before
    finally:
        source.close()


def test_causal_width_uses_interfaces_without_output_tiles(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    effect = BaseBlockEffect(3)
    _ledger, _unused_tiles_binding, adapter, primitive, scheduler, source = (
        _runtime_source(effect, (0, 0, 0, 1))
    )
    engine = CausalTileEngine(scheduler)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("causal width constructed a future output tile")

    monkeypatch.setattr(engine, "output", forbidden)
    monkeypatch.setattr(engine, "point", forbidden)
    try:
        assert engine.width(adapter.power(primitive, 4), source.tile, limit=4) == 4
        assert engine.width(adapter.power(primitive, 8), source.tile, limit=4) == 4
    finally:
        source.close()


def test_causal_width_probes_completed_parent_before_interface_children(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    (
        ledger,
        _unused_tiles_binding,
        adapter,
        _unused_primitive_binding,
        scheduler,
        source,
        action,
    ) = powered_runtime_source(BaseBlockEffect(3), (0, 0, 0, 1), 4)
    engine = CausalTileEngine(scheduler)
    try:
        with engine.output(action, source.tile):
            before = ledger.counters.get("tile_causal_interface_parent_hits", 0)

            def forbidden(*_args: object, **_kwargs: object) -> Never:
                raise AssertionError("warm width rebuilt a leaf interface")

            monkeypatch.setattr(adapter, "leaf_interface_symbol", forbidden)
            assert engine.width(action, source.tile, limit=4) == 4
            assert ledger.counters.get("tile_causal_interface_parent_hits", 0) > before
    finally:
        source.close()


def test_causal_width_preserves_noninitial_two_sided_edge() -> None:
    from number_compiler.hashlife.tiles.tile_ports import (
        BoundPorts,
        FusedBoundaryContract,
    )

    (
        _ledger,
        _unused_tiles_binding,
        adapter,
        _unused_primitive_binding,
        scheduler,
        source,
        action,
    ) = powered_runtime_source(BaseBlockEffect(3), (0, 0, 0, 1), 4)
    wiring = adapter.wiring(action)
    contract = FusedBoundaryContract(
        BoundPorts((1, 0), wiring),
        BoundPorts((0, 1), wiring),
    )
    try:
        assert (
            CausalTileEngine(scheduler).width(
                action,
                source.tile,
                limit=4,
                contract=contract,
            )
            == 4
        )
    finally:
        source.close()

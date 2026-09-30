"""Output morphisms determine next carry responses before exact successors."""

from itertools import product

import pytest
from tests.support.assertions import assert_clean_payloads

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
    BoundarySide,
)
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.hashlife.execution.reverse_morphism_transfer import (
    ReverseMorphismTransferArena,
)
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.execution.tile_causal_tasks import (
    CausalFrame,
    CausalPrefix,
)
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.reverse_add.primitive_output_morphism import (
    LEFT,
    RIGHT,
    ReversePrimitiveOutputMorphism,
)
from tests.support.tile_kernel import _runtime, _tile


def test_decimal_output_morphism_all_kernel_ports() -> None:
    _ledger, _tiles, adapter, action, _scheduler = _runtime(BaseBlockEffect(10))
    kernel = adapter.primitive_law(action)
    arena = ReversePrimitiveOutputMorphism(adapter.bits, kernel)
    for symbol in range(20):
        function = arena.leaf(symbol)
        for left, right in product(range(43), range(5)):
            assert adapter.bits.evaluate(
                function, {LEFT.variable: left, RIGHT.variable: right}
            ) == kernel.emit(left, symbol, right)


@pytest.mark.parametrize("side", (0, 1))
@pytest.mark.parametrize("width", (3, 4))
def test_live_causal_edge_uses_morphism_before_fused_or_exact_outputs(
    monkeypatch: pytest.MonkeyPatch,
    side: int,
    width: int,
) -> None:
    from number_compiler.hashlife.execution import tile_causal_pair_transfer
    from tests.arithmetic.contracts.test_tile_causal_private import _scan

    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(10))
    action = adapter.compose(primitive, primitive)
    law = adapter.primitive_law(primitive)
    symbols = (0, 9, 10, 19)
    ports = (31, 3)
    produced = _scan(law, symbols[:width], ports)
    expected = 0
    for s in reversed(produced) if side else produced:
        expected = law.advance(BoundarySide(side), expected, s)
    with (
        _tile(tiles, adapter, primitive, symbols) as source,
        tiles.mirror(source.tile) as _mirrored_source,
    ):
        prefix = CausalPrefix(
            action, side, ports[side], 0, BoundaryTileView(source.tile, 0, width, side)
        )

        def forbidden(*_args: object, **_kwargs: object) -> None:
            pytest.fail("live carry edge rebuilt a fused interface or exact output")

        monkeypatch.setattr(tile_causal_pair_transfer, "fused_interface", forbidden)
        monkeypatch.setattr(adapter, "wiring", forbidden)
        monkeypatch.setattr(adapter, "initial_ports", forbidden)
        monkeypatch.setattr(scheduler, "_complete_direct", forbidden)
        monkeypatch.setattr(scheduler, "complete", forbidden)
        monkeypatch.setattr(tiles, "leaf", forbidden)
        monkeypatch.setattr(tiles, "join", forbidden)
        engine = CausalTileEngine(scheduler)
        result = engine._run(
            CausalFrame("residual", (action, side, prefix, ports[1 - side])),
            tile_result=False,
        )
        # Audits independently validate retained transfer metadata, including
        # wiring. Poison only execution, not the subsequent verifier.
        monkeypatch.undo()
        assert result == expected
        morphisms = adapter._reverse_morphism_transfer
        assert morphisms is not None
        assert not morphisms._bound and not morphisms._sources
        assert ledger.counters["reverse_morphism_transfer_observations"] == (
            2 if width == 3 else 1
        )
        assert ledger.counters.get("completed_result_publications", 0) == 0
        assert_clean_payloads(ledger)


def test_morphism_budget_failure_cleans_traversal_and_stale_sources_are_rejected() -> (
    None
):
    ledger, tiles, adapter, action, _scheduler = _runtime(BaseBlockEffect(10))
    arena = ReverseMorphismTransferArena(
        tiles, adapter.bits, adapter.primitive_law(action)
    )
    with _tile(tiles, adapter, action, (10, 0)) as source:
        ledger.max_cache_entries = ledger.entries
        before = ledger.snapshot()
        with pytest.raises(BlockContextBudgetExceeded):
            arena.consume(source.tile, (0, 0), 0, 0)
        assert (ledger.entries, ledger.nodes) == (before.entries, before.nodes)
        assert not arena._workspace.frames and not arena._workspace.values
        ledger.max_cache_entries = None
        arena.consume(source.tile, (0, 0), 0, 0)
        stale = source.tile
    with pytest.raises(ValueError, match="stale"):
        arena.consume(stale, (0, 0), 0, 0)
    arena.clear_bindings()
    assert not arena._bound and not arena._sources


def test_cancellation_and_carry_distinctions_survive_the_connected_projection() -> None:
    ledger, tiles, adapter, primitive, _scheduler = _runtime(BaseBlockEffect(10))
    arena = ReverseMorphismTransferArena(
        tiles, adapter.bits, adapter.primitive_law(primitive)
    )
    with (
        _tile(tiles, adapter, primitive, (10, 0, 0, 10, 19, 19, 19, 19)) as first,
        _tile(tiles, adapter, primitive, (10, 9, 9, 10, 19, 19, 19, 19)) as second,
        _tile(tiles, adapter, primitive, (4, 4)) as four,
        _tile(tiles, adapter, primitive, (9, 9)) as nine,
    ):
        assert first.tile != second.tile
        assert arena.compile_bound(first.tile, (0, 0)) == arena.compile_bound(
            second.tile, (0, 0)
        )
        assert arena.compile_bound(four.tile, (0, 0)) != arena.compile_bound(
            nine.tile, (0, 0)
        )
        payload = audit_registered_payloads(ledger)
        assert (payload.forbidden_future_payloads, payload.unknown_payloads) == (0, 0)
        # An issued but incorrect carry function must not pass the independent
        # audit merely because its Python type is recognized.
        key = next(iter(arena._compositions))
        original = arena._compositions[key]
        arena._compositions[key] = ReverseBoundOutput.leaf(10, 7)
        assert audit_registered_payloads(ledger).forbidden_future_payloads > 0
        arena._compositions[key] = original
        arena.clear_bindings()


@pytest.mark.parametrize("symbols", [(10, 0, 0, 10), (10, 9, 9, 10), (9, 19, 10, 19)])
def test_next_carry_is_parametric_and_never_constructs_successor(
    symbols: tuple[int, ...],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _ledger, tiles, adapter, action, scheduler = _runtime(BaseBlockEffect(10))
    arena = ReverseMorphismTransferArena(
        tiles, adapter.bits, adapter.primitive_law(action)
    )
    law = adapter.primitive_law(action)
    expected: dict[tuple[int, int, int, int], int] = {}
    for left, right in product((0, 1, 10, 11, 20, 31, 41, 42), range(5)):
        forward = [left]
        for symbol in symbols:
            forward.append(law.advance(BoundarySide.LEFT, forward[-1], symbol))
        backward = [right]
        for symbol in reversed(symbols):
            backward.append(law.advance(BoundarySide.RIGHT, backward[-1], symbol))
        backward.reverse()
        output = tuple(
            law.emit(forward[i], s, backward[i + 1]) for i, s in enumerate(symbols)
        )
        for side, count in ((0, 43), (1, 5)):
            for incoming in range(count):
                state = incoming
                for value in reversed(output) if side else output:
                    state = law.advance(BoundarySide(side), state, value)
                expected[left, right, side, incoming] = state
    with _tile(tiles, adapter, action, symbols) as source:

        def forbidden(*_args: object, **_kwargs: object) -> None:
            pytest.fail("carry morphism constructed an exact successor")

        monkeypatch.setattr(tiles, "leaf", forbidden)
        monkeypatch.setattr(tiles, "join", forbidden)
        monkeypatch.setattr(scheduler, "_complete_direct", forbidden)
        monkeypatch.setattr(scheduler, "complete", forbidden)
        for (left, right, side, incoming), result in expected.items():
            assert arena.consume(source.tile, (left, right), side, incoming) == result


def test_directional_future_consumer_drops_exact_pair_output(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.carry.reverse_port_functions import ReversePortCodec

    ledger, tiles, adapter, action, _scheduler = _runtime(BaseBlockEffect(10))
    arena = ReverseMorphismTransferArena(
        tiles, adapter.bits, adapter.primitive_law(action)
    )
    codec = ReversePortCodec(10)
    law = adapter.primitive_law(action)
    expected = {}
    for symbol, left, right in product(range(20), range(43), range(5)):
        output = law.emit(left, symbol, right)
        expected[symbol, left, right] = tuple(
            law.advance(BoundarySide.RIGHT, state, output) for state in range(5)
        )

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("directional consumer emitted/rebound an exact future pair")

    monkeypatch.setattr(ReversePrimitiveOutputMorphism, "bind", forbidden)
    monkeypatch.setattr(type(law), "emit", forbidden)
    for symbol in range(20):
        with _tile(tiles, adapter, action, (symbol,)) as source:
            for left, right in product(range(43), range(5)):
                transfer = arena.compile_right(source.tile, (left, right))
                assert (
                    tuple(
                        codec.encode_right(transfer.apply(codec.decode_right(state)))
                        for state in range(5)
                    )
                    == expected[symbol, left, right]
                )
            arena.clear_bindings()
    assert not arena._bound and not arena._compositions
    assert ledger.counters["reverse_morphism_directional_leaf_consumers"] == 20 * 43 * 5
    assert ledger.counters.get("reverse_morphism_leaf_bindings", 0) == 0


def test_directional_composition_merges_different_exact_edges() -> None:
    ledger, tiles, adapter, action, _scheduler = _runtime(BaseBlockEffect(10))
    arena = ReverseMorphismTransferArena(
        tiles, adapter.bits, adapter.primitive_law(action)
    )
    with (
        _tile(tiles, adapter, action, (1, 1)) as first,
        _tile(tiles, adapter, action, (2, 2)) as second,
    ):
        assert arena.compile_right(first.tile, (0, 0)) == arena.compile_right(
            second.tile, (0, 0)
        )
        assert len(arena._right_compositions) == 1
        assert not arena._compositions and not arena._bound
        assert audit_registered_payloads(ledger).forbidden_future_payloads == 0
        key = next(iter(arena._right_compositions))
        original = arena._right_compositions[key]
        from number_compiler.arithmetic.carry.reverse_port_functions import (
            ReverseRightTransfer,
        )

        arena._right_compositions[key] = ReverseRightTransfer.leaf(10, 10)
        assert audit_registered_payloads(ledger).forbidden_future_payloads > 0
        arena._right_compositions[key] = original
        arena.clear_bindings()


@pytest.mark.validation
@pytest.mark.parametrize("generation", (16, 32))
def test_public_reverse_uses_directional_future_quotient(generation: int) -> None:
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

    term = ReverseAddPoweredTerm(196, generation)
    expected = 196
    for _ in range(generation):
        expected += int(str(expected)[::-1])
    position = term.maximum_width // 3
    assert term.digit(position) == expected // 10**position % 10
    metrics = term.metrics()
    assert (
        metrics.resource_work_counters["reverse_morphism_directional_leaf_consumers"]
        > 0
    )
    assert metrics.sequential_generation_advances == 0
    assert metrics.resource_accounting_mismatch == 0
    assert metrics.forbidden_future_payloads == 0

"""Cold output-carry observations merge cancellation before exact successors exist."""

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.hashlife.execution.causal_frames import (
    ReverseInterfaceFrame,
)
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.execution.tile_causal_interfaces import (
    CausalInterfacePayload,
)
from number_compiler.hashlife.tiles.tiles import TileAlphabetID, TileLease
from tests.support.reference_arithmetic import carry_summary as _sectors
from tests.support.reverse_interface import reverse_interface_payload
from tests.support.tile_kernel import make_tile_from_symbols, make_tile_runtime


@pytest.mark.parametrize("exponent", (1, 2))
@pytest.mark.parametrize(
    ("first", "second"),
    (
        ((10, 0, 0, 10), (10, 9, 9, 10)),
        ((0, 9, 9, 10, 10, 9, 9, 0), (0, 14, 14, 0, 0, 14, 14, 0)),
    ),
)
def test_cold_cancellation_merges_bounded_consumer_without_exact_output(
    monkeypatch: pytest.MonkeyPatch,
    exponent: int,
    first: tuple[int, ...],
    second: tuple[int, ...],
) -> None:
    ledger, tiles, adapter, primitive, scheduler = make_tile_runtime(
        BaseBlockEffect(10)
    )
    action = adapter.power(primitive, exponent)
    assert _sectors(first) != _sectors(second)
    with (
        make_tile_from_symbols(
            tiles, adapter, primitive, first + (19,) * (16 - len(first))
        ) as a,
        make_tile_from_symbols(
            tiles, adapter, primitive, second + (19,) * (16 - len(second))
        ) as b,
        tiles.leaf(adapter.alphabet(primitive), 19) as padding,
    ):
        # Only original source interfaces are prepared. No producer executes.
        adapter.compile_interface(primitive, a.tile, adapter.wiring(primitive))
        adapter.compile_interface(primitive, b.tile, adapter.wiring(primitive))

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError(
                "cold carry observation constructed an exact successor"
            )

        def source_padding_only(alphabet: TileAlphabetID, symbol: int) -> TileLease:
            # Source-prefix clipping may retain the already existing blank
            # padding. It cannot construct a leaf of any successor.
            if alphabet == adapter.alphabet(primitive) and symbol == 19:
                return tiles.retain(padding.tile)
            forbidden()

        monkeypatch.setattr(scheduler, "complete", forbidden)
        monkeypatch.setattr(scheduler, "_complete_direct", forbidden)
        monkeypatch.setattr(tiles, "leaf", source_padding_only)
        before = ledger.counters.get("completed_result_publications", 0)
        observed = []
        for source in (a, b):
            engine = CausalTileEngine(scheduler)
            payload = reverse_interface_payload(engine, action, source.tile)
            observed.append(payload.bound_reverse_output)
        assert observed[0] == observed[1]
        assert ledger.counters.get("completed_result_publications", 0) == before
        assert ledger.counters.get("tile_causal_boundary_output_completions", 0) == 0
        # This proves a bounded primitive-carry observer, not arbitrary future
        # continuation closure. The latter still requires its own certificate.


def test_equal_sector_and_current_carry_projections_do_not_merge_next_carry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Difference (1-z**16)(1-z**15) vanishes in all four source sectors.
    # Every source cell resets its current carry to zero, but T doubles 5 to
    # 10 while doubling 4 to 8, which the next carry consumer distinguishes.
    first = (4,) * 32
    second = (5,) + (4,) * 14 + (3, 3) + (4,) * 14 + (5,)
    assert _sectors(first) == _sectors(second)
    _, tiles, adapter, primitive, scheduler = make_tile_runtime(BaseBlockEffect(10))
    with (
        make_tile_from_symbols(tiles, adapter, primitive, first) as a,
        make_tile_from_symbols(tiles, adapter, primitive, second) as b,
    ):

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("negative control constructed an exact successor")

        monkeypatch.setattr(scheduler, "complete", forbidden)
        monkeypatch.setattr(scheduler, "_complete_direct", forbidden)
        monkeypatch.setattr(tiles, "leaf", forbidden)
        outputs = []
        for source in (a, b):
            payload = CausalTileEngine(scheduler)._run(
                ReverseInterfaceFrame(
                    (primitive, source.tile, *adapter.initial_ports(primitive)),
                ),
                tile_result=False,
            )
            assert type(payload) is CausalInterfacePayload
            assert type(payload.bound_reverse_output) is ReverseBoundOutput
            outputs.append(payload.bound_reverse_output)
        assert outputs[0] != outputs[1]
        assert outputs[0].apply(0, 0) != outputs[1].apply(0, 0)

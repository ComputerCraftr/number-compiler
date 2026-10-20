"""A proven initial valuation run uses one primitive action plus geometry."""

from __future__ import annotations

from typing import cast

import pytest

from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.execution.tile_causal_entry import (
    causal_point,
    causal_width_query,
)
from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from tests.support.tile_kernel import make_tile_from_symbols, make_tile_runtime


@pytest.mark.parametrize("valuation", (4, 8, 16))
@pytest.mark.parametrize("complete_event", (False, True))
def test_initial_root_run_uses_only_primitive_observation(
    monkeypatch: pytest.MonkeyPatch, valuation: int, complete_event: bool
) -> None:
    ledger, tiles, adapter, primitive, scheduler = make_tile_runtime(
        CollatzPhysicalBlockEffect()
    )
    seed = ((1 << valuation) - 1) // 3
    width = 1 << (valuation + 2).bit_length()
    digits = tuple(
        (seed >> i) & 1 if i < seed.bit_length() else 2 for i in range(width)
    )
    original = CausalTileEngine.child_actions

    def primitive_only(self: CausalTileEngine, action: object) -> None:
        assert action == primitive, "valuation shortcut replayed a temporal action"
        assert original(self, primitive) is None

    with make_tile_from_symbols(tiles, adapter, primitive, digits) as source:
        action = adapter.power(primitive, valuation + int(complete_event))
        key = PoweredResultKey(
            action, source.tile, adapter.initial_ports(action), adapter.wiring(action)
        )
        monkeypatch.setattr(CausalTileEngine, "child_actions", primitive_only)
        assert causal_point(scheduler, key, 0) == int(complete_event)
        assert causal_point(scheduler, key, 1) == (2 if complete_event else 1)
        assert causal_width_query(scheduler, key, width) == (1 if complete_event else 2)
        assert ledger.counters["collatz_initial_root_point_skips"] == 2
        assert ledger.counters["collatz_initial_root_width_skips"] == 1
        assert ledger.counters["collatz_source_root_match_early_hits"] > 0


def test_initial_root_rule_declines_after_the_first_event() -> None:
    from number_compiler.sequences.collatz.tile_root import initial_event_shift

    ledger, tiles, adapter, primitive, scheduler = make_tile_runtime(
        CollatzPhysicalBlockEffect()
    )
    with make_tile_from_symbols(
        tiles, adapter, primitive, (1, 1, 2, 2, 2, 2, 2, 2)
    ) as source:
        action = adapter.power(primitive, 8)
        key = PoweredResultKey(
            action, source.tile, adapter.initial_ports(action), adapter.wiring(action)
        )
        assert initial_event_shift(scheduler, key) is None
        assert ledger.counters["collatz_initial_root_declines"] == 1


def test_root_skip_declines_when_primitive_growth_would_leave_the_tile() -> None:
    from number_compiler.sequences.collatz.tile_root import initial_event_shift

    _, tiles, adapter, primitive, scheduler = make_tile_runtime(
        CollatzPhysicalBlockEffect()
    )
    with make_tile_from_symbols(tiles, adapter, primitive, (1, 0, 1, 0)) as source:
        action = adapter.power(primitive, 5)
        key = PoweredResultKey(
            action, source.tile, adapter.initial_ports(action), adapter.wiring(action)
        )
        assert initial_event_shift(scheduler, key) is None


@pytest.mark.parametrize("invalid", (True, 1.0))
def test_root_shortcut_rejects_numeric_alias_before_summary_work(
    invalid: object,
) -> None:
    ledger, tiles, adapter, primitive, scheduler = make_tile_runtime(
        CollatzPhysicalBlockEffect()
    )
    with make_tile_from_symbols(
        tiles, adapter, primitive, (1, 0, 1, 2, 2, 2, 2, 2)
    ) as source:
        action = adapter.power(primitive, 4)
        key = PoweredResultKey(
            action, source.tile, adapter.initial_ports(action), adapter.wiring(action)
        )
        before = ledger.snapshot()
        with pytest.raises(TypeError):
            causal_point(scheduler, key, cast(int, invalid))
        with pytest.raises(TypeError):
            causal_width_query(scheduler, key, cast(int, invalid))
        assert ledger.snapshot() == before


def test_public_collatz_point_and_width_consume_source_root_summary() -> None:
    from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm

    term = PoweredCollatzTerm(((1 << 32) - 1) // 3, 16)
    assert term.digit(17) == 1
    assert term.width() == 18
    assert term.resource_ledger.counters["source_image_publications"] > 0
    assert term.resource_ledger.counters["source_image_projection_publications"] >= 1

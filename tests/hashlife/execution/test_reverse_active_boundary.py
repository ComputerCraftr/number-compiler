"""Active reverse boundaries discharge primitive consumers without exact output."""

from __future__ import annotations

from dataclasses import replace
from typing import Any, Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.execution.tile_causal_boundary_step import (
    boundary_step as execute_boundary_step,
)
from number_compiler.hashlife.execution.tile_causal_interfaces import (
    CausalInterfacePayload,
    _attach_bound_reverse_output,
)
from number_compiler.hashlife.execution.tile_causal_results import (
    PrimitiveCausalPorts,
    causal_result_key,
)
from number_compiler.hashlife.execution.tile_causal_tasks import (
    CausalFrame,
    CausalPrefix,
)
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.hashlife.tiles.tile_causal_interface_memo import (
    _bind_reverse_output_request,
    causal_interface_key,
    publish_causal_interface,
)
from number_compiler.hashlife.tiles.tile_result_records import (
    PoweredResultKey,
    ReverseBoundOutputKey,
)
from number_compiler.hashlife.tiles.tile_results import ResultLease
from number_compiler.hashlife.tiles.tile_reverse_bound_output_memo import (
    publish_reverse_bound_output_leaf,
    publish_reverse_bound_output_parent,
)
from number_compiler.hashlife.tiles.tiles import TileLease
from number_compiler.resources.causal_workspace import CausalResults
from number_compiler.resources.result_cache_kinds import (
    REVERSE_BOUND_OUTPUT_RETAINED_NODES,
)
from tests.arithmetic.contracts.test_tile_causal_private import _scan
from tests.arithmetic.contracts.test_tile_kernel import _runtime, _tile


@pytest.mark.parametrize("producer_exponent", (2, 4))
@pytest.mark.parametrize("side", (0, 1))
def test_active_producer_uses_bound_transfer_before_exact_boundary(
    monkeypatch: pytest.MonkeyPatch,
    producer_exponent: int,
    side: int,
) -> None:
    import number_compiler.hashlife.execution.tile_causal as causal

    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    producer = adapter.power(primitive, producer_exponent)
    action = adapter.compose(producer, primitive)
    law = adapter.primitive_law(primitive)
    symbols = (0, 0, 0, 1)
    producer_ports = adapter.initial_ports(producer)
    produced: tuple[int, ...] = symbols
    for _ in range(producer_exponent):
        produced = _scan(law, produced, producer_ports)
    consumer_state = adapter.initial_ports(primitive)[side]
    expected = consumer_state
    scan = reversed(produced) if side else produced
    for symbol in scan:
        expected = law.advance(BoundarySide(side), expected, symbol)

    with _tile(tiles, adapter, primitive, symbols) as source:
        prefix = CausalPrefix(
            action,
            side,
            producer_ports[side],
            consumer_state,
            BoundaryTileView(source.tile, 0, len(symbols), side),
        )
        engine = CausalTileEngine(scheduler)
        if producer_exponent == 4:
            prepared = engine._run(
                CausalFrame(
                    "reverse_boundary",
                    (
                        producer,
                        side,
                        prefix.view,
                        engine._initial(producer, side, prefix.producer_seed),
                        engine._initial(producer, 1 - side),
                    ),
                ),
                tile_result=False,
            )
            assert type(prepared) is ReverseBoundOutput

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("active transfer constructed an exact future boundary")

        def guarded_boundary_step(
            active_engine: Any,
            active_frame: CausalFrame,
            active_frames: Any,
            active_values: CausalResults,
        ) -> bool:
            if (
                active_frame.op == "output_boundary"
                and active_frame.args[0] == producer
            ):
                forbidden()
            return execute_boundary_step(
                active_engine, active_frame, active_frames, active_values
            )

        monkeypatch.setattr(causal, "boundary_step", guarded_boundary_step)
        complete_direct = scheduler._complete_direct

        def guarded_complete_direct(
            root: PoweredResultKey,
            *,
            checked_miss: bool = False,
        ) -> ResultLease:
            if root.action == producer:
                forbidden()
            return complete_direct(root, checked_miss=checked_miss)

        monkeypatch.setattr(scheduler, "_complete_direct", guarded_complete_direct)
        try:
            observed = engine._run(
                CausalFrame(
                    "residual",
                    (
                        action,
                        side,
                        prefix,
                        engine._initial(producer, 1 - side),
                    ),
                ),
                tile_result=False,
            )
            assert observed == expected
            assert ledger.counters["reverse_active_transfer_evaluations"] > 0
            assert ledger.counters["reverse_boundary_extent_discharged"] == len(symbols)
            exact_fallbacks = ledger.counters.get(
                "tile_causal_boundary_output_completions", 0
            )
            if producer_exponent == 2:
                assert exact_fallbacks == 0
            else:
                assert exact_fallbacks > 0
        finally:
            for lease in reversed(engine._leases):
                lease.close()
            engine._release_workspace()


def test_bound_output_cannot_be_replaced_on_an_issued_occurrence() -> None:
    _, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    with _tile(tiles, adapter, primitive, (0, 1)) as source:
        engine = CausalTileEngine(scheduler)
        observed = engine._run(
            CausalFrame(
                "reverse_interface",
                (
                    primitive,
                    source.tile,
                    *adapter.initial_ports(primitive),
                ),
            ),
            tile_result=False,
        )
        assert type(observed) is CausalInterfacePayload
        assert type(observed.bound_reverse_output) is ReverseBoundOutput
        with pytest.raises(ValueError, match="occurrence proof"):
            replace(
                observed,
                bound_reverse_output=ReverseBoundOutput.leaf(3, 4),
            )
        engine._release_workspace()


def test_bound_output_cannot_be_published_for_another_request() -> None:
    _, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    ports = adapter.initial_ports(primitive)
    wiring = adapter.wiring(primitive)
    with (
        _tile(tiles, adapter, primitive, (0, 1)) as source,
        _tile(tiles, adapter, primitive, (1, 0)) as other,
    ):
        engine = CausalTileEngine(scheduler)
        observed = engine._run(
            CausalFrame("reverse_interface", (primitive, source.tile, *ports)),
            tile_result=False,
        )
        assert type(observed) is CausalInterfacePayload
        other_result = causal_result_key(
            scheduler.results,
            primitive,
            other.tile,
            PrimitiveCausalPorts(*ports),
            wiring,
        )
        before = scheduler.ledger.snapshot()
        with pytest.raises(ValueError, match="belongs to another request"):
            publish_causal_interface(
                scheduler.results,
                causal_interface_key(
                    other_result,
                    observation="reverse-output-carry",
                ),
                observed,
            )
        after = scheduler.ledger.snapshot()
        assert (after.entries, after.nodes) == (before.entries, before.nodes)
        engine._release_workspace()


@pytest.mark.parametrize("warm", (False, True))
def test_bound_output_radix_must_match_its_producer_request(warm: bool) -> None:
    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    ports = adapter.initial_ports(primitive)
    with _tile(tiles, adapter, primitive, (0, 1)) as source:
        engine = CausalTileEngine(scheduler)
        observed = engine._run(
            CausalFrame(
                "reverse_interface" if warm else "interface",
                (primitive, source.tile, *ports),
            ),
            tile_result=False,
        )
        assert type(observed) is CausalInterfacePayload
        result_key = causal_result_key(
            scheduler.results,
            primitive,
            source.tile,
            PrimitiveCausalPorts(*ports),
            adapter.wiring(primitive),
        )
        key = causal_interface_key(result_key, observation="reverse-output-carry")
        plain = CausalInterfacePayload(
            observed.interface,
            observed.incoming_ports,
            observed.outgoing_ports,
            observed.level,
            observed.active,
            observed.physical_ticks,
            observed.event_weight,
            observed.frame_shift,
        )
        forged = _bind_reverse_output_request(
            key,
            _attach_bound_reverse_output(plain, ReverseBoundOutput.leaf(4, 1)),
        )
        before = ledger.entries, ledger.nodes, ledger.inventory()
        with pytest.raises(ValueError, match="another radix"):
            publish_causal_interface(scheduler.results, key, forged)
        assert (ledger.entries, ledger.nodes, ledger.inventory()) == before
        assert (scheduler.results._memo.get(key) is not None) is warm
        engine._release_workspace()


def test_completed_producer_builds_bound_summary_from_exact_tile(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.hashlife.execution import (
        tile_causal_interface_step as interface_step,
    )

    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    producer = adapter.power(primitive, 4)
    ports = adapter.initial_ports(producer)
    wiring = adapter.wiring(producer)
    with (
        _tile(tiles, adapter, primitive, (0, 0, 0, 1)) as source,
        scheduler.complete(producer, source.tile, ports, wiring),
    ):
        engine = CausalTileEngine(scheduler)

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("completed producer replayed temporal descendants")

        monkeypatch.setattr(interface_step, "_leaf", forbidden)
        monkeypatch.setattr(scheduler, "_complete_direct", forbidden)
        observed = engine._run(
            CausalFrame(
                "reverse_interface",
                (
                    producer,
                    source.tile,
                    engine._initial(producer, 0),
                    engine._initial(producer, 1),
                ),
            ),
            tile_result=False,
        )
        assert type(observed) is CausalInterfacePayload
        assert type(observed.bound_reverse_output) is ReverseBoundOutput
        assert ledger.counters["reverse_exact_output_summary_evaluations"] == 1
        assert (
            engine._run(
                CausalFrame(
                    "reverse_interface",
                    (
                        producer,
                        source.tile,
                        engine._initial(producer, 0),
                        engine._initial(producer, 1),
                    ),
                ),
                tile_result=False,
            )
            == observed
        )
        assert ledger.counters["reverse_exact_output_summary_evaluations"] == 1
        engine._release_workspace()


def test_exact_reverse_output_summary_reuses_canonical_tile_before_descent(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.hashlife.execution.tile_causal_interface_step as step

    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    with _tile(tiles, adapter, primitive, (0, 1, 2, 3)) as source:
        engine = CausalTileEngine(scheduler)
        request = CausalFrame("exact_reverse_output", (source.tile,))
        expected = engine._run(request, tile_result=False)
        assert type(expected) is ReverseBoundOutput
        evaluations = ledger.counters["reverse_bound_output_evaluations"]
        publications = ledger.counters["reverse_bound_output_publications"]
        assert publications > 1

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("warm exact summary visited canonical descendants")

        monkeypatch.setattr(step, "publish_reverse_bound_output_leaf", forbidden)
        monkeypatch.setattr(step, "publish_reverse_bound_output_parent", forbidden)
        actual = engine._run(
            CausalFrame("exact_reverse_output", (source.tile,)),
            tile_result=False,
        )
        assert actual == expected
        assert ledger.counters["reverse_bound_output_evaluations"] == evaluations
        assert ledger.counters["reverse_bound_output_publications"] == publications
        assert ledger.counters["reverse_bound_output_early_hits"] > 0
        assert ReverseBoundOutputKey(source.tile) in scheduler.results._memo


def test_reverse_output_summary_publication_is_atomic_and_inventoried() -> None:
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )
    from number_compiler.resources.metric_collection import collect_ledger_metrics

    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    with _tile(tiles, adapter, primitive, (1,)) as source:
        key = ReverseBoundOutputKey(source.tile)
        ledger.max_cache_entries = ledger.entries
        before = ledger.snapshot()
        with pytest.raises(BlockContextBudgetExceeded):
            publish_reverse_bound_output_leaf(scheduler.results, key)
        after = ledger.snapshot()
        assert (after.entries, after.nodes) == (before.entries, before.nodes)
        assert key not in scheduler.results._memo

        ledger.max_cache_entries = None
        publish_reverse_bound_output_leaf(scheduler.results, key)
        report = collect_ledger_metrics(ledger)
        row = next(
            item
            for item in report.resource_inventory
            if item.owner == scheduler.results._memo_owner
        )
        assert row.observed_entries == 1
        assert row.observed_nodes == REVERSE_BOUND_OUTPUT_RETAINED_NODES
        assert report.resource_accounting_mismatch == 0
        assert report.forbidden_future_payloads == 0


def test_reverse_output_snapshot_failure_releases_reserved_resources(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    with _tile(tiles, adapter, primitive, (1,)) as source:
        key = ReverseBoundOutputKey(source.tile)
        before = ledger.entries, ledger.nodes

        def fail_snapshot(*_args: object, **_kwargs: object) -> Never:
            raise RuntimeError("injected reverse snapshot failure")

        monkeypatch.setattr(scheduler.results, "_reverse_snapshot", fail_snapshot)
        with pytest.raises(RuntimeError, match="injected reverse snapshot failure"):
            publish_reverse_bound_output_leaf(scheduler.results, key)
        assert (ledger.entries, ledger.nodes) == before
        assert key not in scheduler.results._memo


def test_reverse_output_parent_rejects_a_forged_child_summary() -> None:
    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    with _tile(tiles, adapter, primitive, (0, 1)) as source:
        node = tiles.resolve(source.tile)
        assert node.left is not None and node.right is not None
        left = publish_reverse_bound_output_leaf(
            scheduler.results, ReverseBoundOutputKey(node.left)
        )
        right = publish_reverse_bound_output_leaf(
            scheduler.results, ReverseBoundOutputKey(node.right)
        )
        key = ReverseBoundOutputKey(source.tile)
        before = ledger.entries, ledger.nodes
        with pytest.raises(
            ValueError,
            match="reverse output parent differs from its completed children",
        ):
            publish_reverse_bound_output_parent(
                scheduler.results,
                key,
                ReverseBoundOutput.leaf(3, 2),
                right,
            )
        assert (ledger.entries, ledger.nodes) == before
        assert key not in scheduler.results._memo
        assert left == ReverseBoundOutput.leaf(3, 0)
        assert ledger.counters["reverse_bound_output_failures"] == 1


def test_reverse_output_summaries_are_non_owning_and_retire_with_tiles() -> None:
    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    with _tile(tiles, adapter, primitive, (0, 1, 2, 3)) as source:
        engine = CausalTileEngine(scheduler)
        output = engine._run(
            CausalFrame("exact_reverse_output", (source.tile,)),
            tile_result=False,
        )
        assert type(output) is ReverseBoundOutput
        keys = tuple(
            key for key in scheduler.results._memo if type(key) is ReverseBoundOutputKey
        )
        assert len(keys) == 7
        row = ledger.inventory()[scheduler.results._memo_owner]
        charged_nodes = row.nodes
        assert charged_nodes == len(keys) * REVERSE_BOUND_OUTPUT_RETAINED_NODES

    assert all(key not in scheduler.results._memo for key in keys)
    row = ledger.inventory()[scheduler.results._memo_owner]
    assert row.nodes == (
        charged_nodes - len(keys) * REVERSE_BOUND_OUTPUT_RETAINED_NODES
    )
    assert row.observed_nodes == row.nodes


def test_reverse_output_recreation_after_eviction_is_charged_as_unknown() -> None:
    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    with _tile(tiles, adapter, primitive, (0, 1, 2, 3)) as source:
        engine = CausalTileEngine(scheduler)
        request = CausalFrame("exact_reverse_output", (source.tile,))
        first = engine._run(request, tile_result=False)
        assert type(first) is ReverseBoundOutput
        first_publications = ledger.counters["reverse_bound_output_publications"]
        scheduler.results.clear()
        assert ReverseBoundOutputKey(source.tile) not in scheduler.results._memo
        assert ledger.counters["reverse_bound_output_evictions"] == first_publications

        second = engine._run(
            CausalFrame("exact_reverse_output", (source.tile,)),
            tile_result=False,
        )
        assert second == first
        assert (
            ledger.counters["reverse_bound_output_publications"]
            == 2 * first_publications
        )
        assert (
            ledger.counters[
                "reverse_bound_output_post_eviction_misses_attribution_unknown"
            ]
            > 0
        )


@pytest.mark.parametrize("side", (0, 1))
def test_composite_consumer_reuses_cached_causal_boundary(
    monkeypatch: pytest.MonkeyPatch,
    side: int,
) -> None:
    from number_compiler.hashlife.execution import (
        tile_causal_interface_step as interface_step,
    )

    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    pair = adapter.power(primitive, 2)
    action = adapter.compose(pair, pair)
    with _tile(tiles, adapter, primitive, (0, 0, 0, 1)) as source:
        engine = CausalTileEngine(scheduler)
        pair_ports = adapter.initial_ports(pair)
        prefix = CausalPrefix(
            action,
            side,
            pair_ports[side],
            pair_ports[side],
            BoundaryTileView(source.tile, 0, 4, side),
        )
        request = CausalFrame(
            "residual",
            (
                action,
                side,
                prefix,
                engine._initial(pair, 1 - side),
            ),
        )
        engine._hold_workspace = True
        expected_lease: TileLease | None = None
        try:
            expected = engine._run(request, tile_result=False)
            assert ledger.counters.get("tile_causal_boundary_output_evaluations", 0) > 0
            assert isinstance(expected, CausalPrefix)
            assert expected.view is not None
            expected_lease = tiles.retain(expected.view.tile)
            before_hits = ledger.counters.get("tile_causal_boundary_output_hits", 0)
            before_evaluations = ledger.counters[
                "tile_causal_boundary_output_evaluations"
            ]
            scheduler._causal_workspace.clear()
            scheduler._causal_tasks.clear()

            def forbidden(*_args: object, **_kwargs: object) -> Never:
                raise AssertionError("warm composite consumer replayed a causal child")

            monkeypatch.setattr(interface_step, "_leaf", forbidden)
            monkeypatch.setattr(scheduler, "_complete_direct", forbidden)
            observed = engine._run(
                CausalFrame(
                    "residual",
                    (
                        action,
                        side,
                        prefix,
                        engine._initial(pair, 1 - side),
                    ),
                ),
                tile_result=False,
            )
            assert observed == expected
            assert ledger.counters["tile_causal_boundary_output_hits"] > before_hits
            assert (
                ledger.counters["tile_causal_boundary_output_evaluations"]
                == before_evaluations
            )
        finally:
            if expected_lease is not None:
                expected_lease.close()
            engine._hold_workspace = False
            engine._release_workspace()

"""Executed producer/consumer contracts preserve both directional causal inputs."""

from __future__ import annotations

from collections.abc import Callable, Iterator, Sequence
from itertools import product
from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockEffect, BoundarySide
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.execution.tile_causal_tasks import bound_states
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.execution.tile_scheduler import (
    ChildContext,
    TileScheduler,
)
from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
from number_compiler.hashlife.interfaces.diamond_quotient import DiamondQuotientArena
from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileOperands,
    BoundaryTileView,
)
from number_compiler.hashlife.tiles.tile_causal_interface_memo import (
    causal_interface_key,
)
from number_compiler.hashlife.tiles.tile_ports import BoundPorts, FusedBoundaryContract
from number_compiler.hashlife.tiles.tile_results import (
    CompletedResultArena,
    ResultWiring,
)
from number_compiler.hashlife.tiles.tiles import (
    TileAlphabetID,
    TileArena,
    TileID,
    TileLease,
)
from number_compiler.resources.ledger import ResourceLedger

TileRuntime = tuple[
    ResourceLedger,
    TileArena,
    PrimitiveTileKernelAdapter,
    TileScheduler,
    BaseBlockEffect,
    FieldCellActionID,
    Callable[[Sequence[int]], TileID],
]


@pytest.fixture
def runtime() -> Iterator[TileRuntime]:
    ledger = ResourceLedger()
    tiles = TileArena(ledger)
    quotients = DiamondQuotientArena(SemanticFunctionArena(ledger))
    adapter = PrimitiveTileKernelAdapter(tiles, DiamondKernelArena(ledger), quotients)
    results = CompletedResultArena(
        tiles,
        quotients,
        action_authority=adapter,
        validate_action=adapter.validate_action,
        signature_for=adapter.signature_for,
    )
    adapter.attach_results(results)
    effect = BaseBlockEffect(3)
    primitive = adapter.admit(effect)
    scheduler = TileScheduler(tiles, results, adapter)
    owned: list[TileLease] = []

    def tile(symbols: Sequence[int]) -> TileID:
        level = [tiles.leaf(adapter.alphabet(primitive), value) for value in symbols]
        while len(level) > 1:
            parents = [
                tiles.join(level[i].tile, level[i + 1].tile)
                for i in range(0, len(level), 2)
            ]
            for child in level:
                child.close()
            level = parents
        owned.append(level[0])
        return level[0].tile

    yield ledger, tiles, adapter, scheduler, effect, primitive, tile
    for lease in reversed(owned):
        lease.close()


def scan(
    effect: BlockEffect, symbols: Sequence[int], ports: tuple[int, ...]
) -> tuple[tuple[int, ...], tuple[int, int]]:
    left_domain = effect.boundary_universe(BoundarySide.LEFT)
    right_domain = effect.boundary_universe(BoundarySide.RIGHT)
    assert left_domain is not None and right_domain is not None
    left, right = left_domain[ports[0]], right_domain[ports[1]]
    before = []
    for symbol in symbols:
        before.append(left)
        left = effect.advance(BoundarySide.LEFT, left, symbol)
    after = []
    for symbol in reversed(symbols):
        after.append(right)
        right = effect.advance(BoundarySide.RIGHT, right, symbol)
    output = tuple(
        effect.emit(a, s, b)
        for a, s, b in zip(before, symbols, reversed(after), strict=True)
    )
    assert left_domain is not None
    assert right_domain is not None
    return output, (left_domain.index(left), right_domain.index(right))


def forbidden(*_args: object, **_kwargs: object) -> Never:
    raise AssertionError("demanded fused execution constructed an exact midpoint")


@pytest.mark.parametrize(
    "producer,consumer", tuple(product(((0, 0), (0, 1), (1, 0)), repeat=2))
)
def test_distinct_noninitial_contracts_agree_between_fused_and_completed(
    runtime: TileRuntime,
    monkeypatch: pytest.MonkeyPatch,
    producer: tuple[int, int],
    consumer: tuple[int, int],
) -> None:
    ledger, tiles, adapter, scheduler, effect, primitive, tile = runtime
    symbols = (0, 0, 0, 1)
    source = tile(symbols)
    square = adapter.power(primitive, 2)
    wiring = adapter.wiring(primitive)
    contract = FusedBoundaryContract(
        BoundPorts(producer, wiring), BoundPorts(consumer, wiring)
    )
    midpoint, producer_exits = scan(effect, symbols, producer)
    expected, consumer_exits = scan(effect, midpoint, consumer)
    before = ledger.counters.get("tile_publications", 0)
    with monkeypatch.context() as poison:
        poison.setattr(tiles, "join", forbidden)
        poison.setattr(scheduler, "complete", forbidden)
        poison.setattr(adapter, "temporal_before_context", forbidden)
        assert (
            tuple(
                scheduler.point(square, source, consumer, wiring, i, fusion=contract)
                for i in range(4)
            )
            == expected
        )
        assert scheduler.width(square, source, consumer, wiring, fusion=contract) == 4
    assert ledger.counters.get("tile_publications", 0) == before
    with scheduler.complete(
        square, source, consumer, wiring, fusion=contract
    ) as completed:
        assert tuple(tiles.point(completed.output, i) for i in range(4)) == expected
        assert completed.result.fusion is not None
        assert completed.result.fusion.producer.ports == producer_exits
        assert completed.result.fusion is not None
        assert completed.result.fusion.consumer.ports == consumer_exits
        assert completed.result.physical_ticks == 2
        with monkeypatch.context() as poison:
            poison.setattr(adapter, "temporal_before_context", forbidden)
            poison.setattr(adapter, "fused_leaf_result", forbidden)
            assert (
                scheduler.point(square, source, consumer, wiring, 0, fusion=contract)
                == expected[0]
            )


def test_cached_midpoint_uses_explicit_consumer_incoming_ports(
    runtime: TileRuntime, monkeypatch: pytest.MonkeyPatch
) -> None:
    ledger, _tiles, adapter, scheduler, effect, primitive, tile = runtime
    symbols = (0, 0, 0, 1)
    source = tile(symbols)
    wiring = adapter.wiring(primitive)
    producer, consumer = (1, 0), (0, 1)
    contract = FusedBoundaryContract(
        BoundPorts(producer, wiring), BoundPorts(consumer, wiring)
    )
    expected, _ = scan(effect, scan(effect, symbols, producer)[0], consumer)
    square = adapter.power(primitive, 2)

    # Establish the ordinary fused answer first, then remove only its outer
    # observation binding.  Child interface results remain available, while no
    # completed producer tile exists yet.
    fused_engine = CausalTileEngine(scheduler)
    fused_left, fused_right = bound_states(
        adapter,
        scheduler.results,
        square,
        source,
        contract,
    )
    result_key = fused_engine._composite_key(
        square,
        source,
        fused_left,
        fused_right,
    )
    assert result_key is not None
    fused_payload = fused_engine.interface(
        square,
        source,
        fused_left,
        fused_right,
    )
    scheduler.results._remove_key(causal_interface_key(result_key))

    with scheduler.complete(primitive, source, producer, wiring):
        import number_compiler.hashlife.execution.tile_causal as causal
        from number_compiler.hashlife.execution.tile_causal_tasks import (
            primitive_advance,
        )

        advance = primitive_advance

        def no_midpoint_rescan(
            host: PrimitiveTileKernelAdapter,
            action: FieldCellActionID,
            side: int,
            state: int,
            view: BoundaryTileView,
        ) -> int:
            if view.tile == source and view.relative_extent == len(symbols):
                raise AssertionError(
                    "completed midpoint's outgoing ports were rescanned"
                )
            return advance(host, action, side, state, view)

        monkeypatch.setattr(causal, "primitive_advance", no_midpoint_rescan)
        monkeypatch.setattr(adapter, "fused_leaf_result", forbidden)
        monkeypatch.setattr(adapter, "temporal_before_context", forbidden)
        monkeypatch.setattr(adapter, "temporal_after_context", forbidden)
        cached_engine = CausalTileEngine(scheduler)
        cached_left, cached_right = bound_states(
            adapter,
            scheduler.results,
            square,
            source,
            contract,
        )
        publications_before = ledger.counters.get(
            "causal_interface_result_publications", 0
        )
        midpoint_publications_before = ledger.counters.get(
            "tile_causal_interface_midpoint_publications", 0
        )
        cached_payload = cached_engine.interface(
            square,
            source,
            cached_left,
            cached_right,
        )
        assert cached_payload == fused_payload
        assert cached_payload.incoming_ports == consumer
        assert ledger.counters["tile_causal_interface_midpoint_reuse"] > 0
        assert ledger.counters["tile_causal_midpoint_port_reuses"] > 0
        # The observation first publishes the consumer child interface, then
        # the composed midpoint interface measured by the dedicated counter.
        assert (
            ledger.counters["causal_interface_result_publications"]
            - publications_before
            == 2
        )
        assert (
            ledger.counters["tile_causal_interface_midpoint_publications"]
            - midpoint_publications_before
            == 1
        )
        # A warm observation is an early hit, not another midpoint publication.
        assert (
            cached_engine.interface(
                square,
                source,
                cached_left,
                cached_right,
            )
            == cached_payload
        )
        assert (
            ledger.counters["tile_causal_interface_midpoint_publications"]
            - midpoint_publications_before
            == 1
        )
        assert (
            ledger.counters["causal_interface_result_publications"]
            - publications_before
            == 2
        )
        assert (
            tuple(
                scheduler.point(square, source, consumer, wiring, i, fusion=contract)
                for i in range(4)
            )
            == expected
        )


@pytest.mark.parametrize("side,orientation", tuple(product((0, 1), repeat=2)))
def test_clipped_directional_transfer_matches_exact_scan(
    runtime: TileRuntime, side: int, orientation: int
) -> None:
    ledger, tiles, adapter, _scheduler, effect, primitive, tile = runtime
    symbols = (0, 1, 3, 4, 2, 0, 4, 1)
    source = tile(symbols)
    ports = (1, 0)
    context = BoundPorts(ports, adapter.wiring(primitive))
    view = BoundaryTileView(source, -3, 5, orientation, source_offset=2)
    chosen = symbols[2:7]
    if orientation:
        chosen = chosen[::-1]
    domain = effect.boundary_universe(BoundarySide(side))
    assert domain is not None
    state = domain[ports[side]]
    for symbol in chosen if side == 0 else reversed(chosen):
        state = effect.advance(BoundarySide(side), state, symbol)
    before = ledger.counters.get("tile_publications", 0)
    assert domain is not None
    assert adapter.transfer_view(primitive, view, context, side) == domain.index(state)
    if not orientation:
        assert ledger.counters.get("tile_publications", 0) == before
    assert tiles.resolve(source).width == 8


def test_fused_boundary_operands_are_executed_for_both_current_edge_actions(
    runtime: TileRuntime, monkeypatch: pytest.MonkeyPatch
) -> None:
    ledger, tiles, adapter, scheduler, effect, primitive, tile = runtime
    symbols = (0, 0, 0, 1)
    source = tile(symbols)
    boundary = tile((0, 4, 4, 0))
    wiring = adapter.wiring(primitive)
    operands = BoundaryTileOperands(
        BoundaryTileView(boundary, -2, 2, source_offset=1),
        BoundaryTileView(boundary, 4, 1, source_offset=1),
    )
    context = BoundPorts((0, 0), wiring, operands)
    contract = FusedBoundaryContract(context, context)
    bound = adapter.bind_boundaries(primitive, context)
    assert bound.ports != context.ports
    expected, _ = scan(effect, scan(effect, symbols, bound.ports)[0], bound.ports)
    square = adapter.power(primitive, 2)
    before = ledger.counters.get("tile_publications", 0)
    with monkeypatch.context() as poison:
        poison.setattr(tiles, "join", forbidden)
        poison.setattr(adapter, "temporal_before_context", forbidden)
        assert (
            tuple(
                scheduler.point(
                    square,
                    source,
                    context.ports,
                    wiring,
                    i,
                    boundaries=operands,
                    fusion=contract,
                )
                for i in range(4)
            )
            == expected
        )
    assert ledger.counters.get("tile_publications", 0) == before
    with scheduler.complete(
        square, source, context.ports, wiring, boundaries=operands, fusion=contract
    ) as result:
        assert tuple(tiles.point(result.output, i) for i in range(4)) == expected


@pytest.mark.parametrize("side", (0, 1))
def test_spatial_midpoint_disagreement_rejects_before_parent_publication(
    runtime: TileRuntime, monkeypatch: pytest.MonkeyPatch, side: int
) -> None:
    from dataclasses import replace

    _ledger, tiles, adapter, scheduler, _effect, primitive, tile = runtime
    source = tile((0, 0, 0, 1))
    wiring = adapter.wiring(primitive)
    original = adapter.child_context
    leases = len(tiles._leases)

    def inconsistent(
        action: FieldCellActionID,
        parent: TileID,
        left: TileID,
        right: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
        child_side: int,
    ) -> ChildContext:
        context = original(action, parent, left, right, ports, wiring, child_side)
        if parent == source and child_side == side:
            # Alter only the sibling-derived interior input, never the exterior.
            port = 1 if side == 0 else 0
            context = replace(
                context,
                ports=tuple(
                    value ^ 1 if index == port else value
                    for index, value in enumerate(context.ports)
                ),
            )
        return context

    monkeypatch.setattr(adapter, "child_context", inconsistent)
    with pytest.raises(ValueError, match="midpoint transfer"):
        scheduler.complete(primitive, source, adapter.initial_ports(primitive), wiring)
    assert len(tiles._leases) == leases


@pytest.mark.parametrize(
    "invalid", ("foreign-tile", "foreign-signature", "port-domain")
)
def test_fused_rejection_preserves_complete_ledger_snapshot_before_warm_lookup(
    runtime: TileRuntime, invalid: str
) -> None:
    from dataclasses import replace

    from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
    from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
    from number_compiler.hashlife.tiles.tile_ports import ResultWiring
    from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
    from number_compiler.hashlife.tiles.tiles import TileID

    ledger, _tiles, adapter, scheduler, _effect, primitive, tile = runtime
    source = tile((0, 0, 0, 1))
    square = adapter.power(primitive, 2)
    wiring = adapter.wiring(primitive)
    producer = consumer = BoundPorts((0, 0), wiring)
    fusion = FusedBoundaryContract(producer, consumer)
    with scheduler.complete(square, source, consumer.ports, wiring, fusion=fusion):
        if invalid == "foreign-tile":
            foreign = TileID(ArenaToken("foreign"), "canonical-tile", 0)
            producer = replace(
                producer,
                boundaries=BoundaryTileOperands(BoundaryTileView(foreign, 0, 1)),
            )
        elif invalid == "foreign-signature":
            foreign_signature = PortSignatureID(
                ArenaToken("foreign"), "port-signature", 0
            )
            producer = replace(producer, wiring=ResultWiring(foreign_signature))
        else:
            producer = replace(producer, ports=(1 << 30, 0))
        key = PoweredResultKey(
            square,
            source,
            consumer.ports,
            wiring,
            fusion=FusedBoundaryContract(producer, consumer),
        )
        before = ledger.snapshot()
        with pytest.raises((TypeError, ValueError)):
            scheduler.results.lookup(key)
        assert ledger.snapshot() == before


def test_foreign_directional_operand_rejects_before_work_accounting(
    runtime: TileRuntime,
) -> None:
    from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
    from number_compiler.hashlife.tiles.tiles import TileID

    ledger, _tiles, adapter, _scheduler, _effect, primitive, _tile = runtime
    view = BoundaryTileView(TileID(ArenaToken("foreign"), "canonical-tile", 0), 0, 1)
    incoming = BoundPorts((0, 0), adapter.wiring(primitive))
    before = ledger.snapshot()
    with pytest.raises(ValueError):
        adapter.transfer_view(primitive, view, incoming, 0)
    assert ledger.snapshot() == before
    with pytest.raises(ValueError):
        adapter.bind_boundaries(
            primitive,
            BoundPorts(incoming.ports, incoming.wiring, BoundaryTileOperands(view)),
        )
    assert ledger.snapshot() == before


def test_fused_requests_retain_the_explicit_temporal_edge(runtime: TileRuntime) -> None:
    from number_compiler.hashlife.tiles.tile_result_records import FusedInterfaceKey

    ledger, _tiles, adapter, scheduler, _effect, primitive, tile = runtime
    source = tile((0, 0, 0, 1))
    square = adapter.power(primitive, 2)
    wiring = adapter.wiring(primitive)
    scheduler.point(square, source, (0, 0), wiring, 0)
    keys = [key for key in scheduler.results._memo if type(key) is FusedInterfaceKey]
    assert keys
    assert all((key.before, key.after) == (primitive, primitive) for key in keys)
    key = keys[0]
    before = ledger.snapshot()
    incomplete = FusedInterfaceKey(key.action, key.input, key.ports, key.wiring)
    with pytest.raises(ValueError, match="explicit temporal children"):
        scheduler.results.lookup_fused_interface(incomplete)
    assert ledger.snapshot() == before


@pytest.mark.parametrize(
    "invalid", ("foreign", "bool", "float", "different-edge", "missing-child")
)
def test_fused_edge_validation_precedes_warm_cache_lookup(
    runtime: TileRuntime, invalid: str
) -> None:
    from dataclasses import replace

    from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
    from number_compiler.hashlife.actions.field_actions import FieldCellActionID
    from number_compiler.hashlife.tiles.tile_result_records import FusedInterfaceKey

    ledger, _tiles, adapter, scheduler, _effect, primitive, tile = runtime
    source = tile((0, 0, 0, 1))
    square = adapter.power(primitive, 2)
    wiring = adapter.wiring(primitive)
    scheduler.point(square, source, (0, 0), wiring, 0)
    key = next(key for key in scheduler.results._memo if type(key) is FusedInterfaceKey)
    forged = replace(key)
    if invalid == "foreign":
        value = FieldCellActionID(
            ArenaToken("foreign-edge"), primitive.kind, primitive.local_id
        )
    elif invalid in ("bool", "float"):
        value = replace(primitive)
        object.__setattr__(
            value,
            "local_id",
            bool(primitive.local_id)
            if invalid == "bool"
            else float(primitive.local_id),
        )
    elif invalid == "different-edge":
        value = square
    else:
        value = None
    object.__setattr__(forged, "before", value)
    before = ledger.snapshot()
    with pytest.raises((TypeError, ValueError)):
        scheduler.results.lookup_fused_interface(forged)
    assert ledger.snapshot() == before


@pytest.mark.parametrize("invalid", ("foreign", "retired", "alphabet", "numeric"))
def test_consumer_operand_rejected_before_fused_warm_lookup(
    runtime: TileRuntime, invalid: str
) -> None:
    from dataclasses import replace

    from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
    from number_compiler.hashlife.tiles.tile_result_records import FusedInterfaceKey
    from number_compiler.hashlife.tiles.tiles import TileAlphabet, TileID

    ledger, tiles, adapter, scheduler, _effect, primitive, tile = runtime
    source = tile((0, 0, 0, 1))
    square = adapter.power(primitive, 2)
    wiring = adapter.wiring(primitive)
    scheduler.point(square, source, (0, 0), wiring, 0)
    key = next(key for key in scheduler.results._memo if type(key) is FusedInterfaceKey)
    lease = None
    if invalid == "foreign":
        operand = TileID(ArenaToken("foreign-consumer"), source.kind, source.local_id)
    elif invalid == "retired":
        lease = tiles.leaf(adapter.alphabet(primitive), 2)
        operand = lease.tile
        lease.close()
    elif invalid == "alphabet":
        alphabet = tiles.intern_alphabet(TileAlphabet(3, 2, 2, 2, "different", "v1"))
        lease = tiles.leaf(alphabet, 1)
        operand = lease.tile
    else:
        operand = replace(source)
        object.__setattr__(operand, "local_id", float(source.local_id))
    forged = replace(
        key, consumer_boundaries=BoundaryTileOperands(BoundaryTileView(operand, 0, 1))
    )
    before = ledger.snapshot()
    try:
        with pytest.raises((TypeError, ValueError)):
            scheduler.results.lookup_fused_interface(forged)
        assert ledger.snapshot() == before
    finally:
        if lease is not None:
            lease.close()


@pytest.mark.parametrize(
    "first_reverse,second_reverse", tuple(product((0, 1), repeat=2))
)
def test_causal_boundary_concat_reuses_content_without_digit_emission(
    runtime: TileRuntime,
    monkeypatch: pytest.MonkeyPatch,
    first_reverse: bool,
    second_reverse: bool,
) -> None:
    from number_compiler.hashlife.tiles.tile_boundaries import concat_boundary_views

    _ledger, tiles, adapter, _scheduler, _effect, primitive, tile = runtime
    symbols = (0, 1, 2, 3, 4, 5, 1, 2)
    source = tile(symbols)
    first = BoundaryTileView(source, -3, 3, first_reverse, 2)
    second = BoundaryTileView(source, 0, 4, second_reverse, 1)
    a, b = symbols[2:5], symbols[1:5]
    expected = (a[::-1] if first_reverse else a) + (b[::-1] if second_reverse else b)
    leaf = tiles.leaf

    def padding_only(alphabet: TileAlphabetID, symbol: int) -> TileLease:
        assert symbol == tiles.alphabet(alphabet).blank
        return leaf(alphabet, symbol)

    with monkeypatch.context() as poison:
        poison.setattr(tiles, "point", forbidden)
        poison.setattr(tiles, "leaf", padding_only)
        view, lease = concat_boundary_views(
            tiles, adapter.alphabet(primitive), first, second
        )
    assert view is not None and lease is not None
    try:
        assert view.relative_extent == 7
        assert tuple(tiles.point(view.tile, i) for i in range(7)) == expected
        assert (
            tiles.point(view.tile, 7)
            == tiles.alphabet(adapter.alphabet(primitive)).blank
        )
    finally:
        lease.close()


@pytest.mark.parametrize("orientation", (0, 1))
def test_adjacent_causal_views_reuse_the_existing_root_before_descendants(
    runtime: TileRuntime, monkeypatch: pytest.MonkeyPatch, orientation: int
) -> None:
    from number_compiler.hashlife.tiles.tile_boundaries import concat_boundary_views

    ledger, tiles, adapter, _scheduler, _effect, primitive, tile = runtime
    source = tile((0, 1, 2, 3))
    left = BoundaryTileView(source, 0, 2, orientation, 2 if orientation else 0)
    right = BoundaryTileView(source, 0, 2, orientation, 0 if orientation else 2)
    before = ledger.counters.get("tile_boundary_concat_child_visits", 0)
    with monkeypatch.context() as poison:
        poison.setattr(tiles, "join", forbidden)
        view, lease = concat_boundary_views(
            tiles, adapter.alphabet(primitive), left, right
        )
    assert view is not None
    assert view.tile == source
    assert view is not None
    assert view.orientation == orientation
    assert view is not None
    assert view.relative_extent == 4
    assert ledger.counters.get("tile_boundary_concat_child_visits", 0) == before
    assert lease is not None
    lease.close()


def test_whole_mirrored_causal_scan_reuses_canonical_parent_without_concat(
    runtime: TileRuntime, monkeypatch: pytest.MonkeyPatch
) -> None:
    from number_compiler.hashlife.execution.tile_causal_tasks import scan_view

    ledger, tiles, _adapter, _scheduler, _effect, _primitive, tile = runtime
    source = tile((0, 1, 2, 3))
    mirror = tiles.mirror(source)
    expected = mirror.tile
    leases: list[TileLease] = []
    before = ledger.counters.get("tile_boundary_concat_frames", 0)
    try:
        with monkeypatch.context() as poison:
            poison.setattr(tiles, "join", forbidden)
            actual = scan_view(
                tiles,
                leases,
                BoundaryTileView(source, 0, 4, 1, 0),
            )
        assert actual == BoundaryTileView(expected, 0, 4)
        assert ledger.counters.get("tile_boundary_concat_frames", 0) == before
        assert ledger.counters["tile_boundary_scan_whole_mirror_hits"] == 1
    finally:
        mirror.close()
        for lease in reversed(leases):
            lease.close()


def test_causal_concat_failure_releases_every_temporary_tile_lease(
    runtime: TileRuntime, monkeypatch: pytest.MonkeyPatch
) -> None:
    from number_compiler.hashlife.tiles.tile_boundaries import concat_boundary_views

    ledger, tiles, adapter, _scheduler, _effect, primitive, tile = runtime
    source = tile((0, 1, 2, 3, 4, 5, 1, 2))
    first = BoundaryTileView(source, 0, 3, 0, 2)
    second = BoundaryTileView(source, 0, 4, 0, 1)
    before = (
        ledger.entries,
        ledger.nodes,
        dict(tiles._nodes),
        dict(tiles._leases),
        dict(tiles._refs),
    )
    join = tiles.join
    calls = 0

    def fail_late(left: TileID, right: TileID) -> TileLease:
        nonlocal calls
        calls += 1
        if calls == 3:
            raise RuntimeError("causal join failed")
        return join(left, right)

    with monkeypatch.context() as poison:
        poison.setattr(tiles, "join", fail_late)
        with pytest.raises(RuntimeError, match="causal join failed"):
            concat_boundary_views(tiles, adapter.alphabet(primitive), first, second)
    assert (
        ledger.entries,
        ledger.nodes,
        dict(tiles._nodes),
        dict(tiles._leases),
        dict(tiles._refs),
    ) == before


@pytest.mark.parametrize("orientation", (0, 1))
def test_causal_dyadic_cover_excludes_padding_and_preserves_order(
    runtime: TileRuntime, monkeypatch: pytest.MonkeyPatch, orientation: int
) -> None:
    from number_compiler.hashlife.tiles.tile_boundaries import boundary_dyadic_pieces

    _ledger, tiles, _adapter, _scheduler, _effect, _primitive, tile = runtime
    symbols = (0, 1, 2, 3, 4, 5, 1, 2)
    source = tile(symbols)
    for start in range(9):
        for length in range(9 - start):
            view = BoundaryTileView(source, -5, length, orientation, start)
            with monkeypatch.context() as poison:
                poison.setattr(tiles, "join", forbidden)
                poison.setattr(tiles, "leaf", forbidden)
                poison.setattr(tiles, "point", forbidden)
                pieces = boundary_dyadic_pieces(tiles, view)
            actual: list[int] = []
            cursor = -5
            for piece in pieces:
                assert piece.source_offset == 0
                assert piece.relative_origin == cursor
                width = tiles.resolve(piece.tile).width
                assert piece.relative_extent == width
                actual.extend(
                    tiles.point(piece.tile, i)
                    for i in (range(width - 1, -1, -1) if orientation else range(width))
                )
                cursor += width
            expected = symbols[start : start + length]
            assert tuple(actual) == (expected[::-1] if orientation else expected)
            assert len(pieces) <= 2 * tiles.resolve(source).level + 1

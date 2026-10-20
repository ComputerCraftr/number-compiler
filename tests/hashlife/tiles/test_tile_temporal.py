"""Canonical full-tile temporal composition reuses completed midpoints."""

from __future__ import annotations

from array import array
from typing import Never, cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.contracts.block_kernel import (
    BaseBlockEffect,
    FiniteBlockEffect,
)
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.actions.tile_action_algebra import PrimitiveTileAction
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
from number_compiler.hashlife.interfaces.diamond_quotient import DiamondQuotientArena
from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
from number_compiler.hashlife.tiles.tile_ports import ResultWiring
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from number_compiler.hashlife.tiles.tiles import TileArena, TileID, TileLease
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from number_compiler.sequences.collatz.tile_family_hooks import collatz_tile_hooks
from tests.support.tile_kernel import literal_tile_output as _step
from tests.support.tile_kernel import make_tile_from_symbols as _canonical_tile


def _runtime(
    base: int,
) -> tuple[ResourceLedger, TileArena, PrimitiveTileKernelAdapter, TileScheduler]:
    ledger = ResourceLedger()
    tiles = TileArena(ledger)
    kernels = DiamondKernelArena(ledger)
    quotients = DiamondQuotientArena(SemanticFunctionArena(ledger))
    adapter = PrimitiveTileKernelAdapter(
        tiles, kernels, quotients, family_hooks=collatz_tile_hooks()
    )
    results = CompletedResultArena(
        tiles,
        quotients,
        action_authority=adapter,
        validate_action=adapter.validate_action,
        signature_for=adapter.signature_for,
    )
    adapter.attach_results(results)
    return ledger, tiles, adapter, TileScheduler(tiles, results, adapter)


def _tile(
    tiles: TileArena,
    adapter: PrimitiveTileKernelAdapter,
    action: object,
    symbols: tuple[int, ...],
) -> TileLease:
    from number_compiler.hashlife.actions.field_actions import FieldCellActionID

    if type(action) is not FieldCellActionID:
        raise TypeError("test action is not scoped")
    return _canonical_tile(tiles, adapter, action, symbols)


def _symbols(tiles: TileArena, tile: TileID) -> tuple[int, ...]:
    return tuple(tiles.point(tile, index) for index in range(tiles.resolve(tile).width))


def _collatz_source(value: int, width: int, blank: int) -> tuple[int, ...]:
    bits = tuple((value >> index) & 1 for index in range(value.bit_length()))
    return bits + (blank,) * (width - len(bits))


def _physical(value: int, steps: int) -> tuple[int, int]:
    odd = 0
    for _ in range(steps):
        odd += value & 1
        value = 3 * value + 1 if value & 1 else value // 2
    return value, odd


def _mapped_effect(name: str, outputs: tuple[int, int, int, int]) -> FiniteBlockEffect:
    return FiniteBlockEffect(
        base=3,
        exponent=1,
        left_count=1,
        right_count=1,
        alphabet_size=4,
        initial_left=0,
        initial_right=0,
        left_transitions=array("I", (0,) * 4),
        right_transitions=array("I", (0,) * 4),
        outputs=bytes(outputs),
        kernel_name=name,
        storage_bytes=0,
        uncompressed_bytes=0,
        blank_left_tail=0,
        blank_right_tail=0,
        stable_blank_output=True,
        blank=3,
    )


def _square_source() -> tuple[
    BaseBlockEffect,
    ResourceLedger,
    TileArena,
    PrimitiveTileKernelAdapter,
    TileScheduler,
    FieldCellActionID,
    FieldCellActionID,
    TileLease,
]:
    effect = BaseBlockEffect(3)
    ledger, tiles, adapter, scheduler = _runtime(3)
    primitive = adapter.admit(effect)
    action = adapter.power(primitive, 2)
    source = _tile(tiles, adapter, primitive, (0, 2, 4, effect.blank))
    return effect, ledger, tiles, adapter, scheduler, primitive, action, source


@pytest.mark.parametrize("base", (2, 10))
@pytest.mark.parametrize("steps", (2, 4, 16))
def test_complete_temporal_power_matches_repeated_primitive(
    base: int,
    steps: int,
) -> None:
    effect = BaseBlockEffect(base)
    ledger, tiles, adapter, scheduler = _runtime(base)
    primitive = adapter.admit(effect)
    action = adapter.power(primitive, steps)
    source_values = (
        0,
        base - 1,
        2 * base - 2,
        effect.blank,
    )
    source = _tile(tiles, adapter, primitive, source_values)
    expected: tuple[int, ...] = source_values
    for _ in range(steps):
        expected = _step(effect, expected)
    try:
        result = scheduler.complete(
            action,
            source.tile,
            adapter.initial_ports(primitive),
            adapter.wiring(action),
        )
        try:
            assert _symbols(tiles, result.output) == expected
            assert result.result.physical_ticks == steps
            assert (
                ledger.counters.get("tile_scheduler_temporal_complete_requests", 0) == 1
            )
            assert ledger.counters.get("tile_scheduler_fused_requests", 0) == 0
            assert ledger.counters.get("sequential_generation_advances", 0) == 0
            assert ledger.counters.get("whole_word_sweeps", 0) == 0
        finally:
            result.close()
    finally:
        source.close()


def test_complete_temporal_power_reuses_published_root_and_midpoints() -> None:
    (
        _unused_effect_binding,
        ledger,
        _unused_tiles_binding,
        adapter,
        scheduler,
        primitive,
        action,
        source,
    ) = _square_source()
    try:
        first = scheduler.complete(
            action,
            source.tile,
            adapter.initial_ports(primitive),
            adapter.wiring(action),
        )
        expected = first.output
        frames = ledger.counters.get("tile_temporal_complete_frames", 0)
        second = scheduler.complete(
            action,
            source.tile,
            adapter.initial_ports(primitive),
            adapter.wiring(action),
        )
        try:
            assert second.output == expected
            assert ledger.counters.get("tile_temporal_complete_frames", 0) == frames
            assert ledger.counters["tile_scheduler_parent_early_hits"] == 1
        finally:
            second.close()
            first.close()
    finally:
        source.close()


def test_cached_composite_prefix_dispatches_composite_suffix_iteratively() -> None:
    effect = BaseBlockEffect(3)
    ledger, tiles, adapter, scheduler = _runtime(3)
    primitive = adapter.admit(effect)
    square = adapter.power(primitive, 2)
    fourth = adapter.power(primitive, 4)
    source = _tile(tiles, adapter, primitive, (0, 2, 4, effect.blank))
    expected: tuple[int, ...] = (0, 2, 4, effect.blank)
    for _ in range(4):
        expected = _step(effect, expected)
    try:
        midpoint = scheduler.complete(
            square,
            source.tile,
            adapter.initial_ports(square),
            adapter.wiring(square),
        )
        midpoint.close()
        result = scheduler.complete(
            fourth,
            source.tile,
            adapter.initial_ports(fourth),
            adapter.wiring(fourth),
        )
        try:
            assert _symbols(tiles, result.output) == expected
            assert result.result.physical_ticks == 4
            assert ledger.counters["tile_temporal_complete_compositions"] >= 2
        finally:
            result.close()
    finally:
        source.close()


@pytest.mark.parametrize("seed", (1, 2, 3, 6, 7, 15, 31))
def test_collatz_temporal_results_preserve_branch_dependent_odd_weight(
    seed: int,
) -> None:
    effect = CollatzPhysicalBlockEffect()
    _ledger, tiles, adapter, scheduler = _runtime(2)
    primitive = adapter.admit(effect)
    values = _collatz_source(seed, 16, effect.blank)
    source = _tile(tiles, adapter, primitive, values)
    try:
        for steps in (1, 2, 3, 6):
            action = adapter.power(primitive, steps)
            expected, odd = _physical(seed, steps)
            result = scheduler.complete(
                action,
                source.tile,
                adapter.initial_ports(primitive),
                adapter.wiring(action),
            )
            try:
                output = _symbols(tiles, result.output)
                actual = sum(
                    bit << index
                    for index, bit in enumerate(output)
                    if bit != effect.blank
                )
                assert actual == expected
                assert result.result.physical_ticks == steps
                assert result.result.event_weight == odd
                assert result.result.frame_shift == 0
            finally:
                result.close()
    finally:
        source.close()


def test_equal_collatz_output_tiles_keep_distinct_complete_result_weights() -> None:
    effect = CollatzPhysicalBlockEffect()
    _ledger, tiles, adapter, scheduler = _runtime(2)
    primitive = adapter.admit(effect)
    one = _tile(tiles, adapter, primitive, _collatz_source(1, 4, effect.blank))
    two = _tile(tiles, adapter, primitive, _collatz_source(2, 4, effect.blank))
    try:
        c3 = scheduler.complete(
            adapter.power(primitive, 3),
            one.tile,
            adapter.initial_ports(primitive),
            adapter.wiring(primitive),
        )
        c1 = scheduler.complete(
            primitive,
            two.tile,
            adapter.initial_ports(primitive),
            adapter.wiring(primitive),
        )
        try:
            assert c3.output == c1.output
            assert (c3.result.physical_ticks, c3.result.event_weight) == (3, 1)
            assert (c1.result.physical_ticks, c1.result.event_weight) == (1, 0)
        finally:
            c3.close()
            c1.close()
    finally:
        one.close()
        two.close()


@pytest.mark.parametrize("base", (2, 10))
def test_primitive_pair_point_and_width_are_fused_without_future_tiles(
    base: int,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    effect = BaseBlockEffect(base)
    ledger, tiles, adapter, scheduler = _runtime(base)
    primitive = adapter.admit(effect)
    action = adapter.power(primitive, 2)
    values = (0, base - 1, 2 * base - 2, effect.blank)
    expected: tuple[int, ...] = _step(effect, _step(effect, values))
    source = _tile(tiles, adapter, primitive, values)
    try:
        before = ledger.counters.get("tile_publications", 0)

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("fused demand constructed a midpoint tile")

        monkeypatch.setattr(tiles, "join", forbidden)
        ports, wiring = adapter.initial_ports(primitive), adapter.wiring(action)
        assert (
            tuple(
                scheduler.point(action, source.tile, ports, wiring, coordinate)
                for coordinate in range(len(values))
            )
            == expected
        )
        width = max(
            (
                index + 1
                for index, symbol in enumerate(expected)
                if symbol != effect.blank
            ),
            default=0,
        )
        assert scheduler.width(action, source.tile, ports, wiring) == width
        assert ledger.counters.get("tile_publications", 0) == before
        assert ledger.counters.get("tile_fused_leaf_evaluations", 0) > 0
    finally:
        source.close()


def test_collatz_primitive_pair_fused_point_matches_physical_c2(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    effect = CollatzPhysicalBlockEffect()
    ledger, tiles, adapter, scheduler = _runtime(2)
    primitive = adapter.admit(effect)
    action = adapter.power(primitive, 2)
    values = (1, 1, 0, effect.blank)
    expected: tuple[int, ...] = _step(effect, _step(effect, values))
    source = _tile(tiles, adapter, primitive, values)
    try:
        before = ledger.counters.get("tile_publications", 0)

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("Collatz C2 demand constructed an exact midpoint")

        monkeypatch.setattr(tiles, "join", forbidden)
        ports, wiring = adapter.initial_ports(primitive), adapter.wiring(action)
        assert (
            tuple(
                scheduler.point(action, source.tile, ports, wiring, coordinate)
                for coordinate in range(len(values))
            )
            == expected
        )
        assert ledger.counters.get("tile_publications", 0) == before
    finally:
        source.close()


def test_heterogeneous_reverse_terminal_fuses_without_a_midpoint(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    base = 10
    pair_effect = BaseBlockEffect(base)
    terminal_effect = DigitNormalizeBlockEffect(base)
    ledger, tiles, adapter, scheduler = _runtime(base)
    pair = adapter.admit(pair_effect)
    terminal = adapter.admit(terminal_effect)
    action = adapter.compose(pair, terminal)
    values = (7, 18, 7, pair_effect.blank)
    expected: tuple[int, ...] = _step(terminal_effect, _step(pair_effect, values))
    source = _tile(tiles, adapter, pair, values)
    before_tiles = ledger.counters.get("tile_publications", 0)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("heterogeneous fusion constructed a midpoint")

    monkeypatch.setattr(tiles, "join", forbidden)
    try:
        ports, wiring = adapter.initial_ports(action), adapter.wiring(action)
        assert (
            tuple(
                scheduler.point(action, source.tile, ports, wiring, coordinate)
                for coordinate in range(len(values))
            )
            == expected
        )
        assert ledger.counters.get("tile_publications", 0) == before_tiles
        assert adapter.signature_for(pair) != adapter.signature_for(action)
        assert ledger.counters["powered_absorption_successes"] == len(values)
        assert ledger.counters["powered_absorption_max_span"] == 1
    finally:
        source.close()


def test_noncommuting_heterogeneous_primitives_remain_distinct() -> None:
    first_effect = _mapped_effect("add-one", (1, 2, 0, 3))
    second_effect = _mapped_effect("double", (0, 2, 1, 3))
    ledger, tiles, adapter, scheduler = _runtime(3)
    first, second = adapter.admit(first_effect), adapter.admit(second_effect)
    first_second = adapter.compose(first, second)
    second_first = adapter.compose(second, first)
    assert first_second != second_first
    source = _tile(tiles, adapter, first, (0, 1, 2, 3))
    try:

        def observe(action: object) -> tuple[int, ...]:
            from number_compiler.hashlife.actions.field_actions import FieldCellActionID

            assert type(action) is FieldCellActionID
            return tuple(
                scheduler.point(
                    action,
                    source.tile,
                    adapter.initial_ports(action),
                    adapter.wiring(action),
                    coordinate,
                )
                for coordinate in range(4)
            )

        assert observe(first_second) == (2, 1, 0, 3)
        assert observe(second_first) == (1, 0, 2, 3)
        from number_compiler.hashlife.execution.tile_causal import CausalTileEngine

        triple = adapter.compose(first_second, first)
        fourth = adapter.compose(first_second, first_second)
        assert adapter.action_children(triple) == (first_second, first)
        assert adapter.action_children(fourth) == (first_second, first_second)
        engine = CausalTileEngine(scheduler)
        for action, expected in ((triple, (0, 2, 1, 3)), (fourth, (0, 1, 2, 3))):
            assert observe(action) == expected
            with engine.output(action, source.tile) as result:
                assert tuple(tiles.point(result.tile, i) for i in range(4)) == expected
        assert adapter.compose(first_second, first_second) == fourth
        assert ledger.counters["tile_temporal_action_hits"] > 0
    finally:
        source.close()


def test_complete_temporal_power_rejects_noncanonical_exterior_ports() -> None:
    (
        _unused_effect_binding,
        _unused_ledger_binding,
        _unused_tiles_binding,
        adapter,
        scheduler,
        _unused_primitive_binding,
        action,
        source,
    ) = _square_source()
    try:
        with pytest.raises(ValueError, match="canonical exterior"):
            scheduler.complete(
                action,
                source.tile,
                (1, 0),
                adapter.wiring(action),
            )
    finally:
        source.close()


@pytest.mark.parametrize("orientation,phase", ((1, 0), (0, 1)))
def test_primitive_wiring_rejects_uncertified_automorphism_before_lookup(
    monkeypatch: pytest.MonkeyPatch,
    orientation: int,
    phase: int,
) -> None:
    effect = BaseBlockEffect(3)
    _ledger, tiles, adapter, scheduler = _runtime(3)
    primitive = adapter.admit(effect)
    source = _tile(tiles, adapter, primitive, (0, 2, 4, effect.blank))

    def forbidden_lookup(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("unsupported wiring reached the result memo")

    monkeypatch.setattr(scheduler.results, "lookup", forbidden_lookup)
    try:
        with pytest.raises(
            ValueError,
            match="no certified wiring automorphism|phase lies outside|orientation lies outside",
        ):
            scheduler.complete(
                primitive,
                source.tile,
                adapter.initial_ports(primitive),
                ResultWiring(adapter.signature_for(primitive), orientation, phase),
            )
    finally:
        source.close()


def test_temporal_context_failure_releases_completed_prefix(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    (
        _unused_effect_binding,
        _unused_ledger_binding,
        tiles,
        adapter,
        scheduler,
        primitive,
        action,
        source,
    ) = _square_source()
    leases_before = len(tiles.audit_snapshot().leases)

    def fail_context(*_args: object, **_kwargs: object) -> Never:
        raise RuntimeError("injected temporal context failure")

    monkeypatch.setattr(adapter, "temporal_after_context", fail_context)
    try:
        # The reference midpoint executor retains its independent failure
        # cleanup check; production completion now bypasses this route.
        from number_compiler.hashlife.execution.tile_temporal import complete_temporal
        from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey

        with pytest.raises(RuntimeError, match="injected temporal context"):
            complete_temporal(
                scheduler,
                PoweredResultKey(
                    action,
                    source.tile,
                    adapter.initial_ports(primitive),
                    adapter.wiring(action),
                ),
            )
        assert len(tiles.audit_snapshot().leases) == leases_before
    finally:
        source.close()


def test_temporal_parent_publication_failure_releases_all_children(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    (
        _unused_effect_binding,
        _unused_ledger_binding,
        tiles,
        adapter,
        scheduler,
        primitive,
        action,
        source,
    ) = _square_source()
    leases_before = len(tiles.audit_snapshot().leases)
    publish = scheduler.results.publish

    def fail_parent(key: object, result: object) -> object:
        from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey

        if type(key) is PoweredResultKey and key.action == action:
            raise RuntimeError("injected temporal publication failure")
        from number_compiler.hashlife.tiles.tile_result_records import CompletedResult

        return publish(cast(PoweredResultKey, key), cast(CompletedResult, result))

    monkeypatch.setattr(scheduler.results, "publish", fail_parent)
    try:
        with pytest.raises(RuntimeError, match="injected temporal publication"):
            scheduler.complete(
                action,
                source.tile,
                adapter.initial_ports(primitive),
                adapter.wiring(action),
            )
        assert len(tiles.audit_snapshot().leases) == leases_before
    finally:
        source.close()


def test_temporal_power_identity_is_association_independent() -> None:
    _ledger, _tiles, adapter, _scheduler = _runtime(3)
    primitive = adapter.admit(BaseBlockEffect(3))
    square = adapter.compose(primitive, primitive)
    cube = adapter.compose(primitive, square)
    left = adapter.compose(square, square)
    right = adapter.compose(primitive, cube)
    assert left == right == adapter.power(primitive, 4)
    assert adapter.compose(primitive, cube) == right
    assert adapter.action_record(left).repetitions == 4


def test_failed_temporal_action_publication_is_atomic() -> None:
    ledger, _tiles, adapter, _scheduler = _runtime(3)
    primitive = adapter.admit(BaseBlockEffect(3))
    before = ledger.snapshot()
    next_action = adapter.audit_snapshot().next_action
    ledger.max_cache_entries = ledger.entries + 2
    with pytest.raises(BlockContextBudgetExceeded, match="cache budget exceeded"):
        adapter.compose(primitive, primitive)
    assert ledger.snapshot() == before
    after_snapshot = adapter.audit_snapshot()
    assert after_snapshot.next_action == next_action
    assert (primitive, primitive) not in after_snapshot.compositions
    assert (
        "power",
        adapter.action_record(primitive).kernel,
        2,
        TemporalCocycle(2),
    ) not in after_snapshot.action_keys


def test_temporal_action_forward_reference_rejects_before_warm_lookup() -> None:
    from dataclasses import replace

    from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey

    ledger, tiles, adapter, scheduler = _runtime(3)
    primitive = adapter.admit(BaseBlockEffect(3))
    twice = adapter.power(primitive, 2)
    fourth = adapter.power(primitive, 4)
    source = _tile(tiles, adapter, primitive, (1, 2, 1, 5))
    ports, wiring = adapter.initial_ports(twice), adapter.wiring(twice)
    with scheduler.complete(twice, source.tile, ports, wiring):
        action_snapshot = adapter.audit_snapshot()
        action_store_value: object = action_snapshot.ledger.registered_container(
            action_snapshot.action_owner
        )
        if (
            id(action_store_value) != action_snapshot.action_store_identity
            or type(action_store_value) is not LedgerDict
        ):
            raise AssertionError("primitive action audit lost its registered store")
        action_store = cast(LedgerDict[int, PrimitiveTileAction], action_store_value)
        original = action_store[twice.local_id]
        action_store[twice.local_id] = replace(original, children=(fourth, primitive))
        before = ledger.snapshot()
        try:
            with pytest.raises(ValueError, match="precede their parent"):
                scheduler.results.lookup(
                    PoweredResultKey(twice, source.tile, ports, wiring)
                )
            assert ledger.snapshot() == before
            with pytest.raises(ValueError, match="precede their parent"):
                adapter.validate_input(twice, source.tile)
            assert ledger.snapshot() == before
        finally:
            action_store[twice.local_id] = original
    source.close()

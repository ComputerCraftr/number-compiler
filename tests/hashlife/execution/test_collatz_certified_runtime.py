"""Public certified Collatz routing through the typed field executor."""

from __future__ import annotations

import importlib.util
from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.dyadic_return_images import (
    DyadicReturnImageWorkspace,
)
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileOperands
from number_compiler.hashlife.tiles.tile_ports import (
    FusedBoundaryContract,
    ResultWiring,
)
from number_compiler.hashlife.tiles.tiles import TileArena, TileID
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.collatz.block_power import (
    CollatzPhysicalBlockEffect,
    PoweredCollatzTerm,
)
from tests.support.reference_arithmetic import physical_collatz_literal as _physical
from tests.support.source_image_assertions import assert_collatz_source_publications
from tests.support.tile_kernel import (
    literal_tile_output,
    make_tile_from_symbols,
    make_tile_runtime,
    make_tile_runtime_source,
)


@pytest.mark.parametrize("seed", (1, 2, 3, 7, 27))
@pytest.mark.parametrize("steps", (1, 2, 3, 4))
def test_public_certified_collatz_matches_small_exact_oracle(
    seed: int,
    steps: int,
) -> None:
    term = PoweredCollatzTerm(seed, steps)
    width = term.width()
    value = sum(term.digit(position) << position for position in range(width))
    assert value == _physical(seed, steps)


def test_physical_collatz_leaf_consumer_is_exact_in_every_finite_context() -> None:
    effect = CollatzPhysicalBlockEffect()
    _ledger, tiles, adapter, primitive, _scheduler = make_tile_runtime(effect)
    alphabet = adapter.alphabet(primitive)
    expected = (
        ((0, 1, 2), (0, 1, 2), (0, 0, 0), (1, 1, 1), (1, 1, 1), (0, 0, 0)),
        ((0, 0, 0), (0, 1, 2), (1, 1, 1), (0, 0, 0), (0, 0, 0), (1, 1, 1)),
        ((2, 2, 2), (0, 1, 2), (2, 2, 2), (1, 1, 1), (1, 1, 1), (0, 0, 0)),
    )
    for symbol in range(3):
        with tiles.leaf(alphabet, symbol) as leaf:
            interface = adapter.compile_interface(
                primitive, leaf.tile, adapter.wiring(primitive)
            )
        output = adapter.interface_components(interface)[2]
        for left in range(6):
            for right in range(3):
                binding = {
                    PortVariable(0, 0, "tile-left", 0): left,
                    PortVariable(0, 1, "tile-right", 0): right,
                }
                observed = adapter.bits.evaluate(output, binding)
                assert observed == expected[symbol][left][right]
                assert effect.emit(left, symbol, right) == observed


@pytest.mark.parametrize("steps", (16, 32))
def test_public_powered_collatz_uses_source_image_consumer(steps: int) -> None:
    expected = _physical(27, steps)
    term = PoweredCollatzTerm(27, steps)
    assert term.width() == expected.bit_length()
    assert tuple(term.digit(i) for i in range(term.width())) == tuple(
        (expected >> i) & 1 for i in range(expected.bit_length())
    )
    counters = term.resource_ledger.counters
    assert_collatz_source_publications(counters)
    assert counters.get("sequential_generation_advances", 0) == 0
    assert counters.get("whole_word_symbol_visits", 0) == 0


def test_nonboundary_collatz_interfaces_elide_the_low_source_read(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    effect = CollatzPhysicalBlockEffect()
    ledger, tiles, adapter, primitive, scheduler, source = make_tile_runtime_source(
        effect, (0, 1, 1, 0, 1, 0, 1, 1)
    )
    right = effect.initial(BoundarySide.RIGHT)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("nonboundary event observation read the low source")

    monkeypatch.setattr(type(tiles), "point", forbidden)
    try:
        for left in range(1, 6):
            application = scheduler.application(
                primitive,
                source.tile,
                (left, right),
                adapter.wiring(primitive),
            )
            try:
                payload = application.interface()
                assert payload.incoming_ports == (left, right)
                assert payload.event_weight == 0
                assert payload.physical_ticks == 1
            finally:
                application.close()
        assert ledger.counters["collatz_physical_event_source_reads_elided"] == 5
        assert ledger.counters.get("tile_observation_descents", 0) == 0
    finally:
        source.close()


def test_boundary_collatz_interface_reads_the_low_source_for_event_weight(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    effect = CollatzPhysicalBlockEffect()
    _ledger, tiles, adapter, primitive, scheduler, source = make_tile_runtime_source(
        effect, (1, 1, 1, 0, 1, 0, 1, 1)
    )
    original = type(tiles).point
    reads = 0

    def tracked(arena: TileArena, tile: TileID, coordinate: int) -> int:
        nonlocal reads
        reads += 1
        return original(arena, tile, coordinate)

    monkeypatch.setattr(type(tiles), "point", tracked)
    application = scheduler.application(
        primitive,
        source.tile,
        adapter.initial_ports(primitive),
        adapter.wiring(primitive),
    )
    try:
        payload = application.interface()
        assert payload.event_weight == 1
        assert payload.physical_ticks == 1
        assert reads == 1
    finally:
        application.close()
        source.close()


@pytest.mark.parametrize("steps", (1, 4))
def test_zero_field_uses_current_tile_interface_under_original_limits(
    steps: int,
) -> None:
    effect = CollatzPhysicalBlockEffect()
    ledger, tiles, adapter, primitive, scheduler = make_tile_runtime(effect)
    ledger.tighten_limits(100_000, 200_000)
    action = adapter.power(primitive, steps)
    source = make_tile_from_symbols(tiles, adapter, primitive, (0,) * 8)
    application = scheduler.application(
        action,
        source.tile,
        adapter.initial_ports(action),
        adapter.wiring(action),
    )
    expected: tuple[int, ...] = (0,) * 8
    for _ in range(steps):
        expected = literal_tile_output(effect, expected)
    try:
        first = application.interface()
        before = ledger.counters.get("causal_interface_result_early_hits", 0)
        assert application.interface() == first
        assert ledger.counters.get("causal_interface_result_early_hits", 0) > before
        assert tuple(application.point(position) for position in range(8)) == expected
        assert ledger.counters.get("whole_word_symbol_visits", 0) == 0
        assert ledger.counters.get("sequential_generation_advances", 0) == 0
    finally:
        application.close()
        source.close()


@pytest.mark.parametrize("steps", (3, 5, 7, 11, 13))
def test_non_power_temporal_dag_does_not_require_unpublished_nested_images(
    steps: int,
) -> None:
    expected = _physical(12345, steps)
    term = PoweredCollatzTerm(12345, steps)
    assert term.width() == expected.bit_length()
    assert (
        sum(term.digit(position) << position for position in range(term.width()))
        == expected
    )


def test_public_collatz_does_not_reach_retired_executors(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("retired Collatz executor was reached")

    monkeypatch.setattr(
        "devtools.verification.collatz_spacetime.CollatzCausalSpacetimeEngine.advance",
        forbidden,
    )
    monkeypatch.setattr(
        "devtools.verification.collatz_spacetime.CollatzCausalSpacetimeEngine.advance_power",
        forbidden,
    )
    monkeypatch.setattr(
        "number_compiler.hashlife.execution.continuations.diamond_runtime.DiamondRuntime.execute",
        forbidden,
    )
    monkeypatch.setattr(
        "number_compiler.hashlife.execution.recursive_outputs."
        "RecursiveCoordinateMorphismArena._observe",
        forbidden,
    )
    monkeypatch.setattr(
        "devtools.verification.collatz_c4_reference."
        "CollatzC4ReferenceApplication._apply_machine",
        forbidden,
    )
    monkeypatch.setattr(
        "number_compiler.hashlife.interfaces.semantic_state_codec.StateCodecArena.compile",
        forbidden,
    )
    _assert_noncycle_output()


def _assert_noncycle_output() -> None:
    term = PoweredCollatzTerm(7, 4)
    assert term.width() == 5
    assert tuple(term.digit(position) for position in range(5)) == (1, 0, 0, 0, 1)


def test_noncycle_public_observations_do_not_use_higher_point_or_width(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("public observation bypassed the recursive morphism")

    monkeypatch.setattr(
        "number_compiler.hashlife.execution.continuations.higher_bimachine.HigherBimachineRuntime.point",
        forbidden,
    )
    monkeypatch.setattr(
        "number_compiler.hashlife.execution.continuations.higher_bimachine.HigherBimachineRuntime.width",
        forbidden,
    )
    _assert_noncycle_output()


def test_noncycle_point_does_not_eagerly_observe_width_channels() -> None:
    term = PoweredCollatzTerm(27, 4)
    assert term.digit(0) == 0
    assert term.resource_ledger.counters.get("direct_powered_point_queries", 0) == 1
    assert term._active_width is None


@pytest.mark.validation  # N=64 end-to-end temporal execution poison gate.
def test_temporal_prefix_uses_admitted_image_without_observer_reentry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.hashlife.execution import dyadic_return_observers

    original = TileScheduler.point
    original_cell = dyadic_return_observers.binary_cell
    active = peak = 0
    cell_calls = 0
    empty_boundaries = BoundaryTileOperands()

    def checked_cell(workspace: DyadicReturnImageWorkspace, position: int) -> int:
        nonlocal cell_calls
        cell_calls += 1
        return original_cell(workspace, position)

    def checked(
        self: TileScheduler,
        action: FieldCellActionID,
        source: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
        coordinate: int,
        *,
        _application: int | None = None,
        boundaries: BoundaryTileOperands = empty_boundaries,
        fusion: FusedBoundaryContract | None = None,
    ) -> int:
        nonlocal active, peak
        active += 1
        peak = max(peak, active)
        try:
            return original(
                self,
                action,
                source,
                ports,
                wiring,
                coordinate,
                _application=_application,
                boundaries=boundaries,
                fusion=fusion,
            )
        finally:
            active -= 1

    def endpoint_reconstruction_forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("prefix observation reconstructed the source endpoint")

    monkeypatch.setattr(dyadic_return_observers, "binary_cell", checked_cell)
    monkeypatch.setattr(TileScheduler, "point", checked)
    monkeypatch.setattr(
        PoweredCollatzTerm, "_source_numerator", endpoint_reconstruction_forbidden
    )
    term = PoweredCollatzTerm(27, 64)
    assert term.digit(0) == (_physical(27, 64) & 1)
    assert cell_calls == 1
    assert peak == 0
    assert term._workspace is not None
    assert term._workspace.ledger is term.resource_ledger
    assert (
        term.resource_ledger.counters.get("collatz_physical_point_germ_demands", 0) == 1
    )


@pytest.mark.parametrize("steps", (16, 32))
@pytest.mark.validation  # Deep powered-parent extent and allocation audit.
def test_powered_parent_exact_extent_and_payload_boundary(steps: int) -> None:
    expected = _physical(27, steps)
    term = PoweredCollatzTerm(27, steps)
    assert term.width() == expected.bit_length()
    assert (
        sum(term.digit(position) << position for position in range(term.width()))
        == expected
    )
    with pytest.raises(IndexError):
        term.digit(term.width())
    audit = audit_registered_payloads(term.resource_ledger)
    assert audit.forbidden_future_payloads == 0
    assert audit.unbounded_future_integers == 0
    assert audit.unknown_payloads == 0
    assert term.resource_ledger.counters.get("sequential_generation_advances", 0) == 0
    assert term.resource_ledger.counters.get("whole_word_symbol_visits", 0) == 0


@pytest.mark.parametrize(
    ("seed", "steps", "expected"),
    ((1, 8, 2), (2, 16, 1), (4, 32, 1)),
)
def test_certified_fixed_cycle_all_phases_skip_retired_routes(
    monkeypatch: pytest.MonkeyPatch,
    seed: int,
    steps: int,
    expected: int,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("fixed-cycle observation entered the higher evaluator")

    monkeypatch.setattr(
        "number_compiler.hashlife.execution.continuations.higher_bimachine.HigherBimachineRuntime.point",
        forbidden,
    )
    monkeypatch.setattr(
        "number_compiler.hashlife.execution.continuations.higher_bimachine.HigherBimachineRuntime.width",
        forbidden,
    )
    assert (
        importlib.util.find_spec("number_compiler.sequences.collatz.higher_interface")
        is None
    )
    term = PoweredCollatzTerm(seed, steps)
    width = term.width()
    assert (
        sum(term.digit(position) << position for position in range(width)) == expected
    )

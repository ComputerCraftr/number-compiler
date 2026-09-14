"""Public certified Collatz routing through the typed field executor."""

from __future__ import annotations

import importlib.util
from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.functions.finite_function_types import (
    AtomSort,
    FinitePort,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.execution.tile_scheduler import (
    TileApplication,
    TileScheduler,
)
from number_compiler.hashlife.interfaces.semantic_bits import FactoredFunctionID
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileOperands
from number_compiler.hashlife.tiles.tile_ports import (
    FusedBoundaryContract,
    ResultWiring,
)
from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
from number_compiler.hashlife.tiles.tiles import TileArena, TileID
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.collatz.block_power import (
    CollatzPhysicalBlockEffect,
    PoweredCollatzTerm,
)
from tests.arithmetic.contracts.test_tile_kernel import _oracle, _runtime, _tile


def _application(term: PoweredCollatzTerm) -> TileApplication:
    application = term._point_index()._lazy_application._open()
    assert type(application) is TileApplication
    return application


def _assert_no_completed_root(application: TileApplication) -> None:
    key = PoweredResultKey(
        application.action,
        application.source,
        application.ports,
        application.wiring,
    )
    found = application.scheduler.results.lookup(key)
    try:
        assert found is None
    finally:
        if found is not None:
            found.close()


def _physical(seed: int, steps: int) -> int:
    value = seed
    for _ in range(steps):
        value = value // 2 if value % 2 == 0 else 3 * value + 1
    return value


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
    _ledger, tiles, adapter, primitive, _scheduler = _runtime(effect)
    alphabet = adapter.alphabet(primitive)
    expected = (
        ((0, 1, 2), (0, 1, 2), (0, 0, 0), (1, 1, 1), (1, 1, 1), (0, 0, 0)),
        ((0, 0, 0), (0, 1, 2), (1, 1, 1), (0, 0, 0), (0, 0, 0), (1, 1, 1)),
        ((2, 2, 2), (0, 1, 2), (2, 2, 2), (1, 1, 1), (1, 1, 1), (0, 0, 0)),
    )
    for symbol in range(3):
        with tiles.leaf(alphabet, symbol) as leaf:
            interface = adapter._compile_interface(
                primitive, leaf.tile, adapter.wiring(primitive)
            )
        output = adapter._components(interface)[2]
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
def test_public_powered_collatz_uses_factored_physical_consumer(
    monkeypatch: pytest.MonkeyPatch,
    steps: int,
) -> None:
    original = PrimitiveTileKernelAdapter._tabulated

    def reject_joint_output(
        self: PrimitiveTileKernelAdapter,
        ports: tuple[FinitePort, ...],
        output: AtomSort,
        active: tuple[FinitePort, ...],
        table: tuple[int, ...],
    ) -> FactoredFunctionID:
        if len(active) == 2:
            raise AssertionError("physical Collatz rebuilt the joint output table")
        return original(self, ports, output, active, table)

    monkeypatch.setattr(PrimitiveTileKernelAdapter, "_tabulated", reject_joint_output)
    expected = _physical(27, steps)
    term = PoweredCollatzTerm(27, steps)
    assert term.width() == expected.bit_length()
    assert tuple(term.digit(i) for i in range(term.width())) == tuple(
        (expected >> i) & 1 for i in range(expected.bit_length())
    )
    counters = term._ledger.counters
    assert counters.get("collatz_physical_factored_output_compilations", 0) > 0
    assert counters.get("collatz_physical_joint_output_tables_elided", 0) > 0
    assert counters.get("powered_absorption_max_span", 0) == steps
    assert counters.get("sequential_generation_advances", 0) == 0
    assert counters.get("whole_word_symbol_visits", 0) == 0


def test_collatz_primitive_interface_reuses_the_canonical_tile_result() -> None:
    term = PoweredCollatzTerm(27, 1)
    application = _application(term)
    first = application.interface()
    before = term._ledger.counters.get("causal_interface_result_early_hits", 0)
    second = application.interface()
    assert second == first
    assert term._ledger.counters.get("causal_interface_result_early_hits", 0) > before
    assert term._ledger.counters.get("whole_word_symbol_visits", 0) == 0
    assert term._ledger.counters.get("sequential_generation_advances", 0) == 0


def test_nonboundary_collatz_interfaces_elide_the_low_source_read(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    effect = CollatzPhysicalBlockEffect()
    ledger, tiles, adapter, primitive, scheduler = _runtime(effect)
    source = _tile(tiles, adapter, primitive, (0, 1, 1, 0, 1, 0, 1, 1))
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
    _ledger, tiles, adapter, primitive, scheduler = _runtime(effect)
    source = _tile(tiles, adapter, primitive, (1, 1, 1, 0, 1, 0, 1, 1))
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
    ledger, tiles, adapter, primitive, scheduler = _runtime(effect)
    ledger.tighten_limits(100_000, 200_000)
    action = adapter.power(primitive, steps)
    source = _tile(tiles, adapter, primitive, (0,) * 8)
    application = scheduler.application(
        action,
        source.tile,
        adapter.initial_ports(action),
        adapter.wiring(action),
    )
    expected: tuple[int, ...] = (0,) * 8
    for _ in range(steps):
        expected = _oracle(effect, expected)
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
        "devtools.proofs.collatz_spacetime.CollatzCausalSpacetimeEngine.advance",
        forbidden,
    )
    monkeypatch.setattr(
        "devtools.proofs.collatz_spacetime.CollatzCausalSpacetimeEngine.advance_power",
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
        "devtools.proofs.extensional_family_application."
        "ExtensionalFamilyApplication._apply_machine",
        forbidden,
    )
    monkeypatch.setattr(
        "number_compiler.hashlife.interfaces.semantic_state_codec.StateCodecArena.compile",
        forbidden,
    )
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
    term = PoweredCollatzTerm(7, 4)
    assert term.width() == 5
    assert tuple(term.digit(position) for position in range(5)) == (1, 0, 0, 0, 1)


def test_noncycle_point_does_not_eagerly_observe_width_channels() -> None:
    term = PoweredCollatzTerm(27, 4)
    assert term.digit(0) == 0
    assert term._ledger.counters.get("powered_absorption_successes", 0) > 0
    assert term._ledger.counters.get("tile_causal_width_requests", 0) == 0
    assert term._ledger.counters.get("tile_projection_width_observations", 0) == 0


def test_temporal_actions_compose_before_canonical_tile_observation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = PrimitiveTileKernelAdapter.compose
    calls = 0

    def checked(
        self: PrimitiveTileKernelAdapter,
        before: FieldCellActionID,
        after: FieldCellActionID,
    ) -> FieldCellActionID:
        nonlocal calls
        calls += 1
        return original(self, before, after)

    monkeypatch.setattr(PrimitiveTileKernelAdapter, "compose", checked)
    term = PoweredCollatzTerm(27, 16)
    assert term.digit(0) == 1
    assert calls > 0
    counters = term._ledger.snapshot().counters
    assert counters.get("tile_temporal_action_publications", 0) > 0
    assert counters.get("powered_absorption_successes", 0) > 0
    assert counters.get("powered_absorption_max_span", 0) == 16
    assert counters.get("sequential_generation_advances", 0) == 0
    assert counters.get("whole_word_symbol_visits", 0) == 0


def test_temporal_observation_never_replays_the_complete_root_emit(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("point observation completed the exact output root")

    monkeypatch.setattr(TileApplication, "complete", forbidden)
    term = PoweredCollatzTerm(27, 16)
    assert term.digit(0) == (_physical(27, 16) & 1)
    application = _application(term)
    assert application._root is None
    _assert_no_completed_root(application)
    assert term._ledger.counters.get("powered_absorption_successes", 0) > 0


@pytest.mark.validation  # N=64 end-to-end temporal execution poison gate.
def test_temporal_prefix_evaluation_does_not_reenter_output_observer(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = TileScheduler.point
    active = peak = 0
    empty_boundaries = BoundaryTileOperands()

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

    monkeypatch.setattr(TileScheduler, "point", checked)
    term = PoweredCollatzTerm(27, 64)
    assert term.digit(0) == (_physical(27, 64) & 1)
    assert peak == 1


def test_noncycle_width_uses_tile_extent_without_completing_output(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("width observation completed the exact output root")

    monkeypatch.setattr(TileApplication, "complete", forbidden)
    expected = _physical(27, 16)
    term = PoweredCollatzTerm(27, 16)
    assert term.width() == expected.bit_length()
    application = _application(term)
    assert application._root is None
    _assert_no_completed_root(application)
    assert term._ledger.counters.get("tile_causal_width_requests", 0) > 0
    assert term._ledger.counters.get("tile_projection_width_observations", 0) == 1
    assert term._ledger.counters.get("tile_endpoint_emissions", 0) == 0


@pytest.mark.validation  # N=64 execution and complete port-growth inventory.
def test_collatz_public_ports_do_not_scale_with_future_extent() -> None:
    term = PoweredCollatzTerm(27, 64)
    assert term.digit(0) == _physical(27, 64) & 1
    application = _application(term)
    adapter = application.scheduler.adapter
    assert type(adapter) is PrimitiveTileKernelAdapter
    pending = [application.action]
    signatures: set[tuple[tuple[str, int], ...]] = set()
    while pending:
        action = pending.pop()
        signature = adapter.quotients.interface(adapter.signature_for(action))
        signatures.add(
            tuple((port.variable.role, port.cardinality) for port in signature.inputs)
        )
        assert all(
            type(output) is AtomSort and "position" not in output.name
            for output in signature.outputs
        )
        children = adapter.action_children(action)
        if children is not None:
            pending.extend(children)
    assert len(signatures) == 1
    assert max(cardinality for _role, cardinality in signatures.pop()) <= 6


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
    audit = audit_registered_payloads(term._ledger)
    assert audit.forbidden_future_payloads == 0
    assert audit.unbounded_future_integers == 0
    assert audit.unknown_payloads == 0
    assert term._ledger.counters.get("sequential_generation_advances", 0) == 0
    assert term._ledger.counters.get("whole_word_symbol_visits", 0) == 0


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

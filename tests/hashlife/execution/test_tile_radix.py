"""Canonical quotient-tile radix projection without whole-integer conversion."""

from __future__ import annotations

from copy import copy
from typing import cast

import pytest

from number_compiler.arithmetic.contracts.block_kernel import FiniteBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.arithmetic.radix_division import (
    certified_binary_division_radix,
)
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.execution.tile_scheduler import (
    TileApplication,
    TileScheduler,
)
from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
from number_compiler.hashlife.interfaces.diamond_quotient import DiamondQuotientArena
from number_compiler.hashlife.observation.tile_projection import (
    LazyProjection,
    build_tile_projection,
    import_exact_source,
)
from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from number_compiler.hashlife.tiles.tiles import TileAlphabet, TileArena
from number_compiler.projection.tile_radix import (
    TileRadixObservation,
    TileRadixProjection,
    _division_effect,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect


def _digits(value: int, radix: int) -> tuple[int, ...]:
    if value == 0:
        return (0,)
    out = []
    while value:
        value, remainder = divmod(value, radix)
        out.append(remainder)
    return tuple(out)


def _runtime(
    value: int, radix: int
) -> tuple[
    ResourceLedger,
    TileArena,
    TileScheduler,
    PrimitiveTileKernelAdapter,
    TileRadixProjection,
]:
    ledger = ResourceLedger()
    quotients = DiamondQuotientArena(SemanticFunctionArena(ledger))
    tiles = TileArena(ledger)
    kernels = DiamondKernelArena(ledger)
    adapter = PrimitiveTileKernelAdapter(tiles, kernels, quotients)
    action = adapter.admit(_division_effect(radix))
    results = CompletedResultArena(
        tiles,
        quotients,
        action_authority=adapter,
        validate_action=adapter.validate_action,
        signature_for=adapter.signature_for,
    )
    adapter.attach_results(results)
    scheduler = TileScheduler(tiles, results, adapter)
    bits = tuple((value >> bit) & 1 for bit in range(max(1, value.bit_length())))
    source = ExactSource(
        bits,
        2,
        blank=2,
        extent=max(8, len(bits) + 3),
        alphabet_size=2,
    )
    root = import_exact_source(
        source,
        SourceGeometry(ledger, source),
        tiles,
        adapter.alphabet(action),
    )
    projection = TileRadixProjection(
        scheduler,
        adapter,
        root.tile,
        radix,
    )
    root.close()
    return ledger, tiles, scheduler, adapter, projection


@pytest.mark.parametrize("radix", (2, 3, 6, 12))
@pytest.mark.parametrize("value", (0, 1, 2, 5, 71, 140137))
def test_tile_radix_digits_width_and_zero_quotient(
    radix: int,
    value: int,
) -> None:
    _, tiles, _, _, projection = _runtime(value, radix)
    expected = _digits(value, radix)
    try:
        assert projection.active_width() == len(expected)
        assert (
            tuple(projection.point(index) for index in range(len(expected))) == expected
        )
        with pytest.raises(IndexError):
            projection.point(len(expected))
        final = projection.quotient(len(expected))
        assert tiles.resolve(final).extent == 0
    finally:
        projection.close()


@pytest.mark.parametrize("radix", (2, 3, 6, 12, 255))
def test_finite_division_uses_the_certified_closed_arithmetic_interface(
    radix: int,
) -> None:
    ledger, _, _, adapter, projection = _runtime(140137, radix)
    try:
        effect = adapter.kernels.kernel(
            adapter._action(projection._stage(1).action).kernel
        ).effect
        assert certified_binary_division_radix(effect) == radix
        projection._stage(1).interface()
        assert ledger.counters.get("tile_radix_arithmetic_parent_interfaces", 0) > 0
    finally:
        projection.close()


def test_closed_division_rejects_a_mutated_finite_behavior_record() -> None:
    effect = _division_effect(3)
    assert type(effect) is FiniteBlockEffect
    transitions = list(effect.right_transitions)
    transitions[0] = 1
    object.__setattr__(effect, "right_transitions", tuple(transitions))
    assert certified_binary_division_radix(effect) is None


def test_copied_tile_application_has_no_issuer_authority() -> None:
    ledger, _, _, _, projection = _runtime(71, 3)
    try:
        application = projection._stage(1)
        forged = copy(application)
        before = ledger.snapshot()
        with pytest.raises(ValueError, match="was not issued"):
            forged.interface()
        after = ledger.snapshot()
        assert (after.entries, after.nodes) == (before.entries, before.nodes)
    finally:
        projection.close()


@pytest.mark.parametrize("radix", (3, 6, 12))
def test_each_retained_quotient_is_the_exact_normalized_parent(
    radix: int,
) -> None:
    value = 140137
    _, tiles, _, _, projection = _runtime(value, radix)
    try:
        for stage in range(1, 5):
            quotient = projection.quotient(stage)
            extent = tiles.resolve(quotient).extent
            observed = sum(
                tiles.point(quotient, coordinate) << coordinate
                for coordinate in range(extent)
            )
            assert observed == value // radix**stage
            if extent:
                assert tiles.point(quotient, extent - 1) == 1
    finally:
        projection.close()


def test_digit_three_builds_only_the_requested_power_and_activity_witness() -> None:
    ledger, _, scheduler, adapter, projection = _runtime(140137, 3)
    try:
        assert projection.point(3) == _digits(140137, 3)[3]
        assert set(projection._stages) == {3, 4}
        stage_inventory = next(
            item for item in ledger.inventory() if item.owner == projection._stage_owner
        )
        assert stage_inventory.entries == stage_inventory.observed_entries == 2
        assert ledger.counters["tile_radix_stage_publications"] == 2
        audit = audit_registered_payloads(ledger)
        assert (
            audit.forbidden_future_payloads,
            audit.unbounded_future_integers,
            audit.unknown_payloads,
        ) == (0, 0, 0)
        before = (
            ledger.counters.get("completed_result_publications", 0),
            ledger.counters.get("tile_publications", 0),
            ledger.counters.get("primitive_tile_interface_publications", 0),
        )
        assert projection.point(3) == _digits(140137, 3)[3]
        assert before == (
            ledger.counters.get("completed_result_publications", 0),
            ledger.counters.get("tile_publications", 0),
            ledger.counters.get("primitive_tile_interface_publications", 0),
        )

        second = TileRadixProjection(
            scheduler,
            adapter,
            projection._source.tile,
            3,
        )
        try:
            assert second.point(3) == projection.point(3)
            assert before == (
                ledger.counters.get("completed_result_publications", 0),
                ledger.counters.get("tile_publications", 0),
                ledger.counters.get("primitive_tile_interface_publications", 0),
            )
        finally:
            second.close()
    finally:
        stage_owner = projection._stage_owner
        projection.close()
        assert (
            next(
                item for item in ledger.inventory() if item.owner == stage_owner
            ).entries
            == 0
        )


def test_reserved_binary_symbol_rejects_without_projection_mutation() -> None:
    ledger, tiles, scheduler, adapter, projection = _runtime(7, 3)
    wrong_alphabet = tiles.intern_alphabet(
        TileAlphabet(
            4,
            3,
            2,
            2,
            "unsigned-radix-cell-with-explicit-blank",
            "canonical-tile-alphabet-v1",
        )
    )
    reserved = tiles.leaf(wrong_alphabet, 2)
    try:
        before = ledger.snapshot()
        with pytest.raises(ValueError, match="canonical binary"):
            TileRadixProjection(scheduler, adapter, reserved.tile, 3)
        assert ledger.snapshot() == before
    finally:
        reserved.close()
        projection.close()


def test_tile_radix_prototype_is_not_in_the_public_radix_router() -> None:
    from number_compiler.projection import lazy_radix

    assert "TileRadixProjection" not in vars(lazy_radix)


@pytest.mark.parametrize(
    ("radix", "error"),
    (
        (True, TypeError),
        (0.0, TypeError),
        (0, ValueError),
        (1, ValueError),
        (4, ValueError),
        (1 << 80, ValueError),
    ),
)
def test_tile_radix_rejects_invalid_radix_before_retaining_source(
    radix: object,
    error: type[Exception],
) -> None:
    ledger, _, scheduler, adapter, projection = _runtime(7, 3)
    try:
        before = ledger.snapshot()
        with pytest.raises(error):
            TileRadixProjection(
                scheduler,
                adapter,
                projection._source.tile,
                cast(int, radix),
            )
        assert ledger.snapshot() == before
    finally:
        projection.close()


@pytest.mark.parametrize(
    ("coordinate", "error"),
    ((True, TypeError), (0.0, TypeError), (-1, IndexError), (1 << 80, IndexError)),
)
def test_tile_radix_rejects_legacy_numeric_coordinate_aliases_before_work(
    coordinate: object,
    error: type[Exception],
) -> None:
    ledger, _, _, _, projection = _runtime(598926, 3)
    try:
        before = ledger.snapshot()
        with pytest.raises(error):
            projection.point(cast(int, coordinate))
        after = ledger.snapshot()
        assert (after.entries, after.nodes) == (before.entries, before.nodes)
    finally:
        projection.close()


@pytest.mark.parametrize("steps", (4, 64))
@pytest.mark.validation  # Fixed large-source physical/radix release witness.
def test_large_seed_collatz_radix_uses_current_tile_observation(steps: int) -> None:
    from number_compiler.projection.lazy_radix import collatz_radix_digit
    from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm

    expected = 598926
    for _ in range(steps):
        expected = expected // 2 if expected % 2 == 0 else 3 * expected + 1
    term = PoweredCollatzTerm(598926, steps)
    assert collatz_radix_digit(term, 3, 0) == expected % 3
    observation = term._radix_projections[3]._tile_observation
    assert type(observation) is TileRadixObservation
    assert observation.scheduler.ledger is term._ledger
    assert term._ledger.counters.get("tile_radix_interface_observations", 0) > 0


def test_adjacent_digits_consume_completed_quotient_tiles() -> None:
    ledger, _, _, _, projection = _runtime(140137, 2)
    try:
        expected = _digits(140137, 2)
        assert (
            tuple(projection.point(index) for index in range(len(expected))) == expected
        )
        assert ledger.counters.get("tile_radix_direct_power_stages", 0) == 1
        assert (
            ledger.counters.get("tile_radix_completed_stage_reuses", 0)
            == len(expected) - 1
        )
        for exponent in range(2, len(expected) + 1):
            stage = projection._stages[exponent]
            previous = projection._stages[exponent - 1]
            assert previous._root is not None
            assert stage.source == projection._source.tile
            assert stage.action == projection.adapter.compose(
                previous.action, projection.action
            )
        audit = audit_registered_payloads(ledger)
        assert (
            audit.forbidden_future_payloads,
            audit.unbounded_future_integers,
            audit.unknown_payloads,
        ) == (0, 0, 0)
    finally:
        projection.close()


def test_radix_division_stages_do_not_claim_collatz_physical_ticks() -> None:
    _, _, _, adapter, projection = _runtime(140137, 3)
    try:
        direct = projection._stage(3)
        assert adapter.action_cocycle(direct.action) == TemporalCocycle()
        assert direct.complete().physical_ticks == 0
        adjacent = projection._stage(4)
        assert adapter.action_cocycle(adjacent.action) == TemporalCocycle()
        assert adjacent.complete().physical_ticks == 0
    finally:
        projection.close()


def test_primitive_cocycle_is_part_of_canonical_action_identity() -> None:
    _, _, _, adapter, projection = _runtime(71, 3)
    try:
        zero_tick = projection.action
        temporal = adapter.admit(_division_effect(3))
        assert zero_tick != temporal
        assert adapter._action(zero_tick).kernel == adapter._action(temporal).kernel
        assert adapter.action_cocycle(zero_tick) == TemporalCocycle()
        assert adapter.action_cocycle(temporal) == TemporalCocycle(1)
        assert (
            adapter.admit(_division_effect(3), cocycle=TemporalCocycle()) == zero_tick
        )
    finally:
        projection.close()


@pytest.mark.parametrize("radix", (2, 3, 6, 12))
@pytest.mark.parametrize("value", (1, 2, 5, 71, 140137))
@pytest.mark.validation  # Complete cross-family endpoint/radix matrix.
def test_actual_collatz_completed_tile_feeds_radix_projection(
    radix: int,
    value: int,
) -> None:
    ledger = ResourceLedger()
    quotients = DiamondQuotientArena(SemanticFunctionArena(ledger))
    tiles = TileArena(ledger)
    kernels = DiamondKernelArena(ledger)
    adapter = PrimitiveTileKernelAdapter(tiles, kernels, quotients)
    collatz = adapter.admit(CollatzPhysicalBlockEffect())
    results = CompletedResultArena(
        tiles,
        quotients,
        action_authority=adapter,
        validate_action=adapter.validate_action,
        signature_for=adapter.signature_for,
    )
    adapter.attach_results(results)
    scheduler = TileScheduler(tiles, results, adapter)
    bits = tuple((value >> bit) & 1 for bit in range(max(1, value.bit_length())))
    source = ExactSource(
        bits,
        2,
        blank=2,
        extent=max(8, len(bits) + 3),
        alphabet_size=2,
    )
    root = import_exact_source(
        source,
        SourceGeometry(ledger, source),
        tiles,
        adapter.alphabet(collatz),
    )
    application = scheduler.application(
        collatz,
        root.tile,
        adapter.initial_ports(collatz),
        adapter.wiring(collatz),
    )
    expected_value = value // 2 if value % 2 == 0 else 3 * value + 1
    projection: TileRadixProjection | None = None
    try:
        completed = application.complete()
        projection = TileRadixProjection(
            scheduler,
            adapter,
            completed.output,
            radix,
        )
        expected = _digits(expected_value, radix)
        assert projection.active_width() == len(expected)
        assert (
            tuple(projection.point(index) for index in range(len(expected))) == expected
        )
        audit = audit_registered_payloads(ledger)
        assert (
            audit.forbidden_future_payloads,
            audit.unbounded_future_integers,
            audit.unknown_payloads,
        ) == (0, 0, 0)
    finally:
        if projection is not None:
            projection.close()
        application.close()
        root.close()


def test_collatz_radix_observation_composes_without_endpoint_completion(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.collatz.compilation import (
        compile_collatz_physical_power,
    )

    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger)
    power = compile_collatz_physical_power(compiler, 2)
    assert power.root is not None
    source = ExactSource((1, 0, 1), 2, blank=2, extent=8, alphabet_size=2)
    projection = build_tile_projection(power.root, SourceGeometry(ledger, source))
    radix = TileRadixObservation(projection, 3)
    endpoint_emissions = ledger.counters.get("tile_endpoint_emissions", 0)

    def forbidden_complete(_self: object) -> object:
        raise AssertionError("radix observation completed a future endpoint")

    monkeypatch.setattr(TileApplication, "complete", forbidden_complete)
    try:
        assert projection.point(3) == 1
        assert projection.active_width() == 4
        # C**2(5) = 8 = (2, 2)_3.
        assert radix.digit(0) == 2
        assert radix.digit(1) == 2
        assert all(application._root is None for application in radix._apps.values())
        assert {
            application.interface().physical_ticks
            for application in radix._apps.values()
        } == {2}
        assert ledger.counters.get("tile_endpoint_emissions", 0) == endpoint_emissions
        audit = audit_registered_payloads(ledger)
        assert (
            audit.forbidden_future_payloads,
            audit.unbounded_future_integers,
            audit.unknown_payloads,
        ) == (0, 0, 0)
    finally:
        radix.close()
        projection.close()


def test_warm_radix_observation_rejects_a_foreign_application_before_lookup() -> None:
    from number_compiler.sequences.collatz.compilation import (
        compile_collatz_physical_power,
    )

    def projection() -> LazyProjection:
        ledger = ResourceLedger()
        compiler = LazyCompiler(ledger)
        power = compile_collatz_physical_power(compiler, 2)
        assert power.root is not None
        source = ExactSource((1, 0, 1), 2, blank=2, extent=8, alphabet_size=2)
        return build_tile_projection(power.root, SourceGeometry(ledger, source))

    first = projection()
    second = projection()
    observation = TileRadixObservation(first, 3)
    try:
        assert observation.digit(0) == 2
        object.__setattr__(observation, "projection", second)
        before = observation.scheduler.ledger.snapshot()
        with pytest.raises(ValueError, match="another application"):
            observation.digit(0)
        assert observation.scheduler.ledger.snapshot() == before
    finally:
        object.__setattr__(observation, "projection", first)
        observation.close()
        first.close()
        second.close()

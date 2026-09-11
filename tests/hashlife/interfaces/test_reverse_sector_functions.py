"""The public tile runtime exposes authenticated reverse sector products."""

from __future__ import annotations

from dataclasses import replace
from typing import Never

import pytest

import number_compiler.hashlife.execution.tile_causal_api as causal_api

from number_compiler.arithmetic.carry.event_memory import carry_field, pair_step
from number_compiler.arithmetic.carry.reverse_sector_transfer import (
    ReverseCarrySectorTransfer,
)
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.execution.tile_scheduler import TileApplication
from number_compiler.hashlife.interfaces.tile_reverse_sector_functions import (
    _aligned_reverse_interval_forcing,
    reverse_sector_width_from_interface,
)
from number_compiler.hashlife.interfaces.tile_reverse_functions import (
    reverse_parent_components,
)
from number_compiler.hashlife.interfaces.diamond_quotient import (
    QuotientRecord,
)
from number_compiler.hashlife.observation.tile_projection import build_tile_projection
from number_compiler.hashlife.tiles.interface_publication import (
    publish_spatial_quotient,
)
from number_compiler.hashlife.tiles.tile_result_records import SpatialInterfaceKey
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.sequences.reverse_add.tile_sector_observation import (
    observe_reverse_interval_forcing,
    observe_reverse_sector_product,
)


def _reduce(values: tuple[int, ...], classes: int) -> tuple[int, ...]:
    out = [0] * classes
    for index, value in enumerate(values):
        quotient, target = divmod(index, classes)
        out[target] = (out[target] + (-value if quotient & 1 else value)) % 32
    return tuple(out)


def _multiply(
    left: tuple[int, ...],
    right: tuple[int, ...],
) -> tuple[int, ...]:
    width = len(left)
    out = [0] * width
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            quotient, target = divmod(i + j, width)
            out[target] += (-1 if quotient & 1 else 1) * a * b
    return tuple(value % 32 for value in out)


def _source(
    ledger: ResourceLedger,
    values: tuple[int, ...] = (7, 18, 7),
) -> SourceGeometry:
    return SourceGeometry(
        ledger,
        ExactSource(values, 10, blank=19, extent=16, alphabet_size=19),
    )


@pytest.mark.parametrize("steps", (1, 2, 4, 8))
def test_authenticated_application_observes_sector_product_without_endpoint(
    monkeypatch: pytest.MonkeyPatch,
    steps: int,
) -> None:
    ledger = ResourceLedger()
    source_values = (7, 18, 7)
    target: tuple[int, ...] = source_values
    for _ in range(steps):
        target, _growth = pair_step(target, 10)
    with build_tile_projection(BaseBlockEffect(10), _source(ledger)) as projection:
        primitive_application = projection._application
        adapter = primitive_application.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter
        action = adapter.power(primitive_application.action, steps)
        application = primitive_application.scheduler.application(
            action,
            primitive_application.source,
            adapter.initial_ports(action),
            adapter.wiring(action),
        )

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("sector observation constructed an exact endpoint")

        monkeypatch.setattr(application.scheduler, "complete", forbidden)
        try:
            application.interface()
            monkeypatch.setattr(adapter, "apply_leaf", forbidden)
            product = observe_reverse_sector_product(application)
            assert product.steps == steps
            assert product.growth == len(target) - len(source_values)
            for block in product.sectors:
                transported = _multiply(
                    block.radial.multiplier_residue(),
                    _reduce(source_values, block.classes),
                )
                assert tuple(
                    (value + forcing) % 32
                    for value, forcing in zip(
                        transported,
                        block.innovation,
                        strict=True,
                    )
                ) == _reduce(target, block.classes)
            assert ledger.counters["reverse_sector_product_observation_evaluations"]
        finally:
            application.close()


def test_primitive_sector_product_uses_authenticated_source_before_future_interface(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    source_values = (7, 18, 7)
    target, growth = pair_step(source_values, 10)
    with build_tile_projection(BaseBlockEffect(10), _source(ledger)) as projection:
        application = projection._application

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError(
                "primitive sector product requested a future interface"
            )

        monkeypatch.setattr(TileApplication, "interface", forbidden)
        monkeypatch.setattr(application.scheduler, "complete", forbidden)
        product = observe_reverse_sector_product(application)
        assert product.steps == 1
        assert product.growth == growth
        for block in product.sectors:
            transported = _multiply(
                block.radial.multiplier_residue(),
                _reduce(source_values, block.classes),
            )
            assert tuple(
                (value + forcing) % 32
                for value, forcing in zip(
                    transported,
                    block.innovation,
                    strict=True,
                )
            ) == _reduce(target, block.classes)


def test_sector_observation_rejects_noninitial_and_asymmetric_applications() -> None:
    ledger = ResourceLedger()
    with build_tile_projection(BaseBlockEffect(10), _source(ledger)) as projection:
        initial = projection._application
        adapter = initial.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter
        ports = adapter.initial_ports(initial.action)
        noninitial = initial.scheduler.application(
            initial.action,
            initial.source,
            (1 - ports[0], ports[1]),
            initial.wiring,
        )
        try:
            with pytest.raises(ValueError, match="initial boundary"):
                observe_reverse_sector_product(noninitial)
        finally:
            noninitial.close()

    with build_tile_projection(
        BaseBlockEffect(10),
        _source(ResourceLedger(), (7, 18, 6)),
    ) as projection:
        with pytest.raises(ValueError, match="symmetric pair field"):
            observe_reverse_sector_product(projection._application)


def test_annihilated_source_observation_skips_source_sector_compilation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    source = SourceGeometry(
        ledger,
        ExactSource((0,), 10, blank=19, extent=64, alphabet_size=19),
    )
    with build_tile_projection(BaseBlockEffect(10), source) as projection:
        original = projection._application
        adapter = original.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter
        action = adapter.power(original.action, 20)
        application = original.scheduler.application(
            action,
            original.source,
            adapter.initial_ports(action),
            adapter.wiring(action),
        )
        try:
            application.interface()

            def forbidden(*_args: object, **_kwargs: object) -> Never:
                raise AssertionError("annihilated source was compiled again")

            monkeypatch.setattr(adapter, "_compile_interface", forbidden)
            monkeypatch.setattr(application.scheduler, "complete", forbidden)
            product = observe_reverse_sector_product(application)
            assert product.steps == 20
            assert product.growth == 0
            assert all(product.source_annihilated_sectors)
            assert all(not any(block.innovation) for block in product.sectors)
            assert ledger.counters["reverse_sector_product_source_elisions"] == 1
            report = collect_ledger_metrics(ledger)
            assert report.reverse_sector_product_source_elisions == 1
            assert report.reverse_sector_product_observation_evaluations == 1
            assert report.source_annihilations == 0
        finally:
            application.close()


def test_aligned_interval_forcing_counts_evaluation_and_failed_work(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    source = SourceGeometry(
        ledger,
        ExactSource((7, 18, 18, 7), 10, blank=19, extent=4, alphabet_size=19),
    )
    with build_tile_projection(BaseBlockEffect(10), source) as projection:
        application = projection._application
        adapter = application.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter
        payload = application.interface()
        observed = _aligned_reverse_interval_forcing(
            adapter,
            payload,
            payload,
            incoming=0,
            reflected_incoming=0,
            growth=0,
        )
        assert observed.growth == 0
        assert ledger.counters["reverse_interval_forcing_requests"] == 1
        assert ledger.counters["reverse_interval_forcing_evaluations"] == 1
        assert ledger.counters.get("reverse_interval_forcing_failures", 0) == 0

        def fail_interval(*_args: object, **_kwargs: object) -> Never:
            raise RuntimeError("injected interval forcing failure")

        monkeypatch.setattr(
            ReverseCarrySectorTransfer,
            "interval_forcing",
            fail_interval,
        )
        with pytest.raises(RuntimeError, match="injected interval"):
            _aligned_reverse_interval_forcing(
                adapter,
                payload,
                payload,
                incoming=0,
                reflected_incoming=0,
                growth=0,
            )
        report = collect_ledger_metrics(ledger)
        assert report.reverse_interval_forcing_requests == 2
        assert report.reverse_interval_forcing_evaluations == 1
        assert report.reverse_interval_forcing_failures == 1


def test_authenticated_local_interval_forcing_reuses_canonical_regions(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    source_values = (7, 18, 18, 7)
    target, growth = pair_step(source_values, 10)
    assert growth == 0
    source = SourceGeometry(
        ledger,
        ExactSource(source_values, 10, blank=19, extent=4, alphabet_size=19),
    )
    with build_tile_projection(BaseBlockEffect(10), source) as projection:
        application = projection._application
        expected = observe_reverse_interval_forcing(application, 0, 2)
        for sector in expected.sectors:
            assert sector.output == _reduce(target[:2], sector.classes)

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("warm interval observation constructed exact output")

        monkeypatch.setattr(application.scheduler, "complete", forbidden)
        adapter = application.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter
        monkeypatch.setattr(adapter, "apply_leaf", forbidden)
        before = ledger.counters.get("tile_region_normalization_early_hits", 0)
        assert observe_reverse_interval_forcing(application, 0, 2) == expected
        assert ledger.counters["tile_region_normalization_early_hits"] > before


def test_authenticated_local_interval_forcing_covers_growth_interior() -> None:
    ledger = ResourceLedger()
    source_values = (18, 18, 18, 18)
    target, growth = pair_step(source_values, 10)
    assert growth == 1
    source = SourceGeometry(
        ledger,
        ExactSource(source_values, 10, blank=19, extent=4, alphabet_size=19),
    )
    with build_tile_projection(BaseBlockEffect(10), source) as projection:
        application = projection._application
        observed = observe_reverse_interval_forcing(application, 1, 2)
        for sector in observed.sectors:
            assert sector.output == _reduce(target[1:3], sector.classes)
        assert ledger.counters["reverse_interval_observation_requests"] == 1
        assert ledger.counters["reverse_interval_observation_evaluations"] == 1
        with pytest.raises(ValueError, match="special endpoint"):
            observe_reverse_interval_forcing(application, 0, 2)
        assert ledger.counters["reverse_interval_observation_requests"] == 2
        assert ledger.counters["reverse_interval_observation_failures"] == 1


def test_sector_observation_rejects_malformed_and_foreign_action() -> None:
    with pytest.raises(TypeError, match="tile application"):
        observe_reverse_sector_product(object())  # type: ignore[arg-type]

    first_ledger, second_ledger = ResourceLedger(), ResourceLedger()
    with (
        build_tile_projection(BaseBlockEffect(10), _source(first_ledger)) as first,
        build_tile_projection(BaseBlockEffect(10), _source(second_ledger)) as second,
    ):
        application = first._application
        original = application.action
        object.__setattr__(application, "action", second._application.action)
        try:
            with pytest.raises(ValueError):
                observe_reverse_sector_product(application)
        finally:
            object.__setattr__(application, "action", original)


@pytest.mark.parametrize("steps", (1, 2, 4, 8))
def test_digit_terminal_interface_exposes_exact_width_without_output(
    monkeypatch: pytest.MonkeyPatch,
    steps: int,
) -> None:
    ledger = ResourceLedger()
    target: tuple[int, ...] = (7, 18, 7)
    for _ in range(steps):
        target, _growth = pair_step(target, 10)
    expected = len(target) + carry_field(target, base=10)[-1]
    with build_tile_projection(BaseBlockEffect(10), _source(ledger)) as projection:
        primitive = projection._application
        adapter = primitive.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter
        powered = adapter.power(primitive.action, steps)
        terminal = adapter.admit(DigitNormalizeBlockEffect(10))
        action = adapter.compose(powered, terminal)
        application = primitive.scheduler.application(
            action,
            primitive.source,
            adapter.initial_ports(action),
            adapter.wiring(action),
        )

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("terminal width constructed an exact endpoint")

        monkeypatch.setattr(application.scheduler, "complete", forbidden)
        try:
            payload = application.interface()
            monkeypatch.setattr(adapter, "apply_leaf", forbidden)
            observed = reverse_sector_width_from_interface(
                adapter,
                action,
                application.source,
                payload,
                16,
            )
            assert observed == expected
            monkeypatch.setattr(adapter, "_compile_interface", forbidden)
            monkeypatch.setattr(causal_api, "causal_width", forbidden)
            assert application.width(16) == expected
        finally:
            application.close()


def test_digit_terminal_sector_width_declines_noncontiguous_activity() -> None:
    ledger = ResourceLedger()
    with build_tile_projection(BaseBlockEffect(10), _source(ledger)) as projection:
        original = projection._application
        adapter = original.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter
        alphabet = adapter.alphabet(original.action)
        leaves = tuple(
            adapter.tiles.leaf(alphabet, symbol) for symbol in (7, 19, 7, 19)
        )
        left = adapter.tiles.join(leaves[0].tile, leaves[1].tile)
        right = adapter.tiles.join(leaves[2].tile, leaves[3].tile)
        root = adapter.tiles.join(left.tile, right.tile)
        terminal = adapter.admit(DigitNormalizeBlockEffect(10))
        application = original.scheduler.application(
            terminal,
            root.tile,
            adapter.initial_ports(terminal),
            adapter.wiring(terminal),
        )
        try:
            payload = application.interface()
            assert (
                reverse_sector_width_from_interface(
                    adapter,
                    application.action,
                    application.source,
                    payload,
                    4,
                )
                is None
            )
            assert application.width(4) == 1
        finally:
            application.close()
            root.close()
            right.close()
            left.close()
            for leaf in reversed(leaves):
                leaf.close()


def test_digit_terminal_empty_width_uses_quiescent_parent() -> None:
    ledger = ResourceLedger()
    source = SourceGeometry(
        ledger,
        ExactSource((19,), 10, blank=19, extent=16, alphabet_size=20),
    )
    with build_tile_projection(DigitNormalizeBlockEffect(10), source) as projection:
        assert projection._application.width(16) == 0


def test_spatial_quotient_and_memo_reservation_roll_back_together(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    with build_tile_projection(BaseBlockEffect(10), _source(ledger)) as projection:
        application = projection._application
        adapter = application.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter
        alphabet = adapter.alphabet(application.action)
        left_tile = adapter.tiles.leaf(alphabet, 7)
        right_tile = adapter.tiles.leaf(alphabet, 18)
        try:
            left = adapter._compile_interface(
                application.action,
                left_tile.tile,
                application.wiring,
            )
            right = adapter._compile_interface(
                application.action,
                right_tile.tile,
                application.wiring,
            )
            with adapter.quotients.closed_workspace.scope("parent"):
                components = reverse_parent_components(
                    adapter.quotients.resolve(left).components,
                    adapter.quotients.resolve(right).components,
                    ledger,
                )
            record = QuotientRecord(application.wiring.signature, components)
            assert record not in adapter.quotients._keys
            key = SpatialInterfaceKey(left, right, application.wiring)
            before_entries = ledger.entries
            before_nodes = len(adapter.quotients._nodes)
            before_identity = adapter.quotients._next_node
            ledger.max_cache_entries = ledger.entries + 2
            with pytest.raises(BlockContextBudgetExceeded):
                publish_spatial_quotient(application.scheduler.results, key, components)
            assert ledger.entries == before_entries
            assert len(adapter.quotients._nodes) == before_nodes
            assert adapter.quotients._next_node == before_identity
            assert record not in adapter.quotients._keys
            assert key not in application.scheduler.results._memo
            ledger.max_cache_entries = None

            def fail_after_quotient(*_args: object, **_kwargs: object) -> Never:
                raise RuntimeError("injected spatial binding failure")

            monkeypatch.setattr(
                type(application.scheduler.results),
                "_validate_spatial_result",
                fail_after_quotient,
            )
            with pytest.raises(RuntimeError, match="injected spatial"):
                publish_spatial_quotient(application.scheduler.results, key, components)
            assert ledger.entries == before_entries
            assert len(adapter.quotients._nodes) == before_nodes
            assert adapter.quotients._next_node == before_identity + 1
            assert record not in adapter.quotients._keys
            assert key not in application.scheduler.results._memo
        finally:
            ledger.max_cache_entries = None
            right_tile.close()
            left_tile.close()


def test_unissued_sector_rejects_before_quotient_publication() -> None:
    ledger = ResourceLedger()
    with build_tile_projection(BaseBlockEffect(10), _source(ledger)) as projection:
        application = projection._application
        adapter = application.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter
        interface = adapter._compile_interface(
            application.action,
            application.source,
            application.wiring,
        )
        record = adapter.quotients.resolve(interface)
        issued = record.components.reverse_sectors
        assert type(issued) is ReverseCarrySectorTransfer
        forged = object.__new__(ReverseCarrySectorTransfer)
        for name in ("base", "width", "active_width", "carry", "sectors"):
            object.__setattr__(forged, name, getattr(issued, name))
        components = replace(record.components, reverse_sectors=forged)
        before = ledger.snapshot()
        with pytest.raises(TypeError, match="verified leaf or composition"):
            adapter.quotients.intern(record.signature, components)
        after = ledger.snapshot()
        assert (after.entries, after.nodes, after.inventory) == (
            before.entries,
            before.nodes,
            before.inventory,
        )

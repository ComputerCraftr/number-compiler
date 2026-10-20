"""Powered sector requests must not recover an action from its endpoint."""

from collections.abc import MutableMapping
from typing import Never, cast

import pytest

from devtools.experiments.reverse_add.frobenius_sectors import (
    ReverseFrobeniusSectorProduct,
)
from devtools.experiments.reverse_add.tile_sector_observation import (
    observe_reverse_sector_product,
)
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.hashlife.execution.tile_application import TileApplication
from number_compiler.hashlife.observation.tile_projection import (
    build_tile_projection,
    import_exact_source,
)
from number_compiler.hashlife.tiles.tile_causal_interface_memo import (
    causal_interface_key,
)
from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
from number_compiler.resources.construction_scope import RuntimeConstruction
from number_compiler.resources.ledger import ResourceLedger
from tests.support.tile_kernel import powered_application


def test_powered_sector_uses_prior_interface_without_endpoint_materialization(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("sector observation requested endpoint execution")

    ledger = ResourceLedger()
    source = ExactSource((7, 18, 7), 10, blank=19, extent=8, alphabet_size=19)
    with build_tile_projection(
        BaseBlockEffect(10), SourceGeometry(ledger, source)
    ) as projection:
        adapter, _action, application = powered_application(projection)
        try:
            # The existing interface request supplies the final primitive's
            # predecessor transfer. Observation must consume that publication
            # without asking the causal engine to run again.
            application.interface()
            causal_requests = ledger.counters.get("tile_causal_interface_requests", 0)
            monkeypatch.setattr(TileApplication, "interface", forbidden)
            monkeypatch.setattr(TileApplication, "complete", forbidden)
            monkeypatch.setattr(application.scheduler, "complete", forbidden)
            monkeypatch.setattr(adapter, "apply_leaf", forbidden)
            product = observe_reverse_sector_product(application)
            assert product.steps == 4
            assert (
                ledger.counters["reverse_sector_product_observation_evaluations"] == 1
            )
            assert (
                ledger.counters.get("reverse_sector_product_observation_failures", 0)
                == 0
            )
            assert (
                ledger.counters.get("tile_causal_interface_requests", 0)
                == causal_requests
            )
        finally:
            application.close()
    assert not hasattr(ReverseFrobeniusSectorProduct, "from_endpoint_sectors")
    assert not hasattr(ReverseFrobeniusSectorProduct, "from_annihilated_source")


def _causal_work_snapshot(ledger: ResourceLedger) -> dict[str, int]:
    return {
        name: value
        for name, value in ledger.counters.items()
        if name.startswith(("tile_causal_", "causal_interface_result_"))
        or name
        in (
            "completed_result_evaluations",
            "tile_scheduler_leaf_function_applications",
        )
    }


def test_powered_sector_requires_prior_interface_without_starting_work(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("sector observation started interface execution")

    ledger = ResourceLedger()
    source = ExactSource((7, 18, 7), 10, blank=19, extent=8, alphabet_size=19)
    with build_tile_projection(
        BaseBlockEffect(10), SourceGeometry(ledger, source)
    ) as projection:
        adapter, _action, application = powered_application(projection)
        monkeypatch.setattr(TileApplication, "interface", forbidden)
        monkeypatch.setattr(TileApplication, "complete", forbidden)
        monkeypatch.setattr(application.scheduler, "complete", forbidden)
        monkeypatch.setattr(adapter, "apply_leaf", forbidden)
        before = _causal_work_snapshot(ledger)
        try:
            with pytest.raises(ValueError, match="prior interface request"):
                observe_reverse_sector_product(application)
            assert _causal_work_snapshot(ledger) == before
            assert ledger.counters["reverse_sector_product_observation_failures"] == 1
        finally:
            application.close()


def test_powered_sector_rejects_foreign_cached_interface_binding(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("sector observation started interface execution")

    ledger = ResourceLedger()
    source = ExactSource((7, 18, 7), 10, blank=19, extent=8, alphabet_size=19)
    with build_tile_projection(
        BaseBlockEffect(10), SourceGeometry(ledger, source)
    ) as projection:
        adapter, action, application = powered_application(projection)
        ports, wiring = application.ports, application.wiring
        other_source = ExactSource((8, 18, 8), 10, blank=19, extent=8, alphabet_size=19)
        other_geometry = SourceGeometry(ledger, other_source)
        with RuntimeConstruction(ledger):
            other_root = import_exact_source(
                other_source,
                other_geometry,
                adapter.tiles,
                adapter.alphabet(action),
            )
        other_application = application.scheduler.application(
            action, other_root.tile, ports, wiring
        )
        arena = application.scheduler.results
        memo = cast(
            MutableMapping[object, object], object.__getattribute__(arena, "_memo")
        )
        target_key = causal_interface_key(
            PoweredResultKey(action, application.source, ports, wiring)
        )
        foreign_key = causal_interface_key(
            PoweredResultKey(action, other_application.source, ports, wiring)
        )
        try:
            assert target_key != foreign_key
            assert memo.get(target_key) is None
            other_application.interface()
            foreign_record = memo[foreign_key]
            monkeypatch.setattr(TileApplication, "interface", forbidden)
            monkeypatch.setattr(TileApplication, "complete", forbidden)
            monkeypatch.setattr(application.scheduler, "complete", forbidden)
            monkeypatch.setattr(adapter, "apply_leaf", forbidden)
            with ledger.reservation(arena.audit_snapshot().memo_owner, entries=1):
                memo[target_key] = foreign_record
                try:
                    with pytest.raises(
                        ValueError, match="publication metadata was modified"
                    ):
                        observe_reverse_sector_product(application)
                finally:
                    memo.pop(target_key)
        finally:
            other_application.close()
            application.close()
            other_root.close()

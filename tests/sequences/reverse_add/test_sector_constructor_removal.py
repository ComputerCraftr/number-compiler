"""Powered sector requests must not recover an action from its endpoint."""

from typing import Never

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
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.execution.tile_scheduler import TileApplication
from number_compiler.hashlife.observation.tile_projection import build_tile_projection
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.source_images import (
    ReverseCylinderConstructionUnavailable,
)


def test_powered_sector_refuses_before_endpoint_interface(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("sector pullback evaluated its endpoint")

    ledger = ResourceLedger()
    source = ExactSource((7, 18, 7), 10, blank=19, extent=8, alphabet_size=19)
    with build_tile_projection(
        BaseBlockEffect(10), SourceGeometry(ledger, source)
    ) as projection:
        primitive = projection._application
        adapter = primitive.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter
        action = adapter.power(primitive.action, 4)
        application = primitive.scheduler.application(
            action,
            primitive.source,
            adapter.initial_ports(action),
            adapter.wiring(action),
        )
        monkeypatch.setattr(TileApplication, "interface", forbidden)
        try:
            with pytest.raises(ReverseCylinderConstructionUnavailable):
                observe_reverse_sector_product(application)
            assert ledger.counters["reverse_sector_product_observation_failures"] == 1
        finally:
            application.close()
    assert not hasattr(ReverseFrobeniusSectorProduct, "from_endpoint_sectors")
    assert not hasattr(ReverseFrobeniusSectorProduct, "from_annihilated_source")

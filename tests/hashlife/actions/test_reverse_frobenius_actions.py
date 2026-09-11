"""The public tile authority owns scoped reverse source-sector bounds."""

from dataclasses import replace

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.polynomials.frobenius_sector import (
    DECIMAL_REVERSE_GROWTH_CERTIFICATE,
    ReverseFrobeniusPlan,
)
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.observation.tile_projection import build_tile_projection
from number_compiler.resources.ledger import ResourceLedger


def test_public_reverse_action_composes_sector_bounds_before_source_descent(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    source = ExactSource((7, 18, 7), 10, blank=19, extent=4, alphabet_size=19)
    with build_tile_projection(
        BaseBlockEffect(10), SourceGeometry(ledger, source)
    ) as p:
        application = p._application
        adapter = p.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter

        def forbidden(*_args: object, **_kwargs: object) -> None:
            raise AssertionError("temporal sector composition visited source digits")

        monkeypatch.setattr(p.scheduler.tiles, "point", forbidden)
        primitive = application.action
        f16, f4 = adapter.power(primitive, 16), adapter.power(primitive, 4)
        f20 = adapter.compose(f16, f4)
        plan = adapter._action(f20).reverse_frobenius
        assert type(plan) is ReverseFrobeniusPlan
        assert plan.steps == 20
        assert tuple(sector.classes for sector in plan.sectors) == (1, 2, 4, 8)
        # This is the conditional symmetric-field certificate. Application
        # observation must establish its hypotheses before dropping the source.
        assert plan.growth_certificate is DECIMAL_REVERSE_GROWTH_CERTIFICATE
        assert plan.annihilated_sectors == (True, True, True, True)
        assert adapter.compose(f4, f16) == f20
        assert adapter.power(primitive, 1024) == adapter.power(primitive, 1024)
        assert ledger.counters["reverse_frobenius_plan_compositions"] > 0
        assert ledger.counters.get("source_annihilations", 0) == 0
        assert application._root is None


def test_warm_action_rejects_a_frobenius_plan_for_another_depth() -> None:
    ledger = ResourceLedger()
    source = ExactSource((7, 18, 7), 10, blank=19, extent=4, alphabet_size=19)
    with build_tile_projection(
        BaseBlockEffect(10), SourceGeometry(ledger, source)
    ) as p:
        adapter = p.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter
        primitive = p._application.action
        powered = adapter.power(primitive, 8)
        record = adapter._action(powered)
        adapter._actions[powered.local_id] = replace(
            record, reverse_frobenius=adapter._action(primitive).reverse_frobenius
        )
        before = ledger.snapshot()
        with pytest.raises(ValueError, match="differs from its temporal action"):
            adapter.power(powered, 1)
        assert ledger.snapshot() == before
        adapter._actions[powered.local_id] = record


def test_warm_action_rejects_mutated_frobenius_sector_without_a_validation_cache() -> (
    None
):
    ledger = ResourceLedger()
    source = ExactSource((7, 18, 7), 10, blank=19, extent=4, alphabet_size=19)
    with build_tile_projection(
        BaseBlockEffect(10), SourceGeometry(ledger, source)
    ) as projection:
        adapter = projection.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter
        powered = adapter.power(projection._application.action, 8)
        plan = adapter._action(powered).reverse_frobenius
        assert type(plan) is ReverseFrobeniusPlan
        sector = plan.sectors[0]
        original = sector.valuation_lower_bound
        object.__setattr__(sector, "valuation_lower_bound", original + 1)
        before = ledger.snapshot()
        try:
            with pytest.raises(ValueError, match="differs from its temporal action"):
                adapter.validate_action(powered)
            assert ledger.snapshot() == before
        finally:
            object.__setattr__(sector, "valuation_lower_bound", original)


@pytest.mark.parametrize("base", (2, 3, 5))
def test_other_radices_do_not_receive_a_decimal_sector_certificate(base: int) -> None:
    ledger = ResourceLedger()
    blank = 2 * base - 1
    source = ExactSource((1, 1), base, blank=blank, extent=4, alphabet_size=blank)
    with build_tile_projection(
        BaseBlockEffect(base), SourceGeometry(ledger, source)
    ) as p:
        adapter = p.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter
        assert (
            adapter._action(adapter.power(p._application.action, 20)).reverse_frobenius
            is None
        )

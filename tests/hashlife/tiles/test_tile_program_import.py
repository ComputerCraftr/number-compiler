"""Balanced composition syntax imports once into the shared tile scheduler."""

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.hashlife.interfaces.diamond_quotient import DiamondQuotientArena
from number_compiler.hashlife.observation.tile_projection import build_tile_projection
from number_compiler.resources.ledger import ResourceLedger


@pytest.mark.parametrize("exponent,expected", ((4, (2, 0, 0, 4)), (8, (2, 4, 0, 2))))
def test_balanced_program_import_executes_existing_causal_scheduler(
    exponent: int, expected: tuple[int, ...], monkeypatch: pytest.MonkeyPatch
) -> None:
    ledger = ResourceLedger()
    effect = LazyCompiler(ledger).power(BaseBlockEffect(3), exponent).root
    assert effect is not None
    source = ExactSource((0, 0, 0, 1), 3, blank=5, alphabet_size=5)
    geometry = SourceGeometry(ledger, source)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("point query completed the entire temporal endpoint")

    monkeypatch.setattr(TileScheduler, "complete", forbidden)
    with build_tile_projection(effect, geometry) as projection:
        assert (
            ledger.counters["tile_projection_compilation_frames"]
            == 2 * exponent.bit_length() - 1
        )
        assert ledger.counters.get("tile_causal_frames", 0) == 0
        assert tuple(projection.point(i) for i in range(4)) == expected
        assert (
            projection.audit_snapshot().application.audit_snapshot().root_lease is None
        )
        assert ledger.counters["powered_absorption_max_span"] == exponent
    work = [
        item
        for item in ledger.inventory()
        if item.name.startswith("tile-program-import-")
    ]
    assert len(work) == 3
    assert all(item.entries == item.observed_entries == 0 for item in work)


def test_distinct_quotient_arenas_share_a_ledger_without_container_aliasing() -> None:
    ledger = ResourceLedger()
    first = DiamondQuotientArena(SemanticFunctionArena(ledger))
    second = DiamondQuotientArena(SemanticFunctionArena(ledger))
    assert first is not second
    before = ledger.snapshot()
    inventory = ledger.inventory()
    assert all(item.accounting_delta in (None, 0) for item in inventory)
    assert ledger.snapshot() == before


def test_failed_runtime_factory_retires_new_owners_and_preserves_existing_nodes() -> (
    None
):
    ledger = ResourceLedger()
    effect = LazyCompiler(ledger).power(BaseBlockEffect(3), 8).root
    assert effect is not None
    geometry = SourceGeometry(ledger, ExactSource((1,), 3, blank=5, alphabet_size=5))
    before = ledger.snapshot()
    ledger.max_cache_entries = before.entries + 2
    with pytest.raises(BlockContextBudgetExceeded):
        build_tile_projection(effect, geometry)
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    assert after.inventory[: len(before.inventory)] == before.inventory
    assert all(item.disposed for item in after.inventory[len(before.inventory) :])
    assert all(item.accounting_delta in (0, None) for item in after.inventory)
    ledger.max_cache_entries = None
    with build_tile_projection(effect, geometry) as projection:
        assert projection.point(0) >= 0

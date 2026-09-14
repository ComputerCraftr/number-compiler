"""Adversarial inventory checks for the production tile primitive runtime."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import replace
from typing import Never, cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.tile_fused_kernel import LeafProductKey
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.execution.tile_scheduler import TileApplication
from number_compiler.hashlife.interfaces.diamond_kernel import PrimitiveKernel
from number_compiler.hashlife.observation.hashlife_projection import HashLifeBlockIndex
from number_compiler.hashlife.observation.tile_projection import LazyProjection
from number_compiler.hashlife.tiles.tile_result_records import PoweredInterfaceKey
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.stores import LedgerDict, LedgerList
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def _runtime() -> tuple[
    HashLifeBlockIndex,
    PrimitiveTileKernelAdapter,
    TileApplication,
]:
    """Build the tile executor explicitly as the component under audit."""
    term = ReverseAddPoweredTerm(196, 2)
    assert term.effect is not None
    index = HashLifeBlockIndex(
        term.effect,
        term.seed_pair,
        logical_length=term.maximum_width,
        ledger=term._ledger,
        compiler=term._compiler,
        source_construction=term._source_construction,
    )
    projection = index._lazy_application
    assert type(projection) is LazyProjection
    application = projection._application
    assert type(application) is TileApplication
    adapter = application.scheduler.adapter
    assert type(adapter) is PrimitiveTileKernelAdapter
    assert adapter._actions and adapter._compositions
    return index, adapter, application


def _primitive_reverse_action(
    adapter: PrimitiveTileKernelAdapter,
) -> FieldCellActionID:
    for local_id, record in adapter._actions.items():
        if (
            record.children is None
            and type(adapter.kernels.kernel(record.kernel).effect) is BaseBlockEffect
        ):
            return FieldCellActionID(
                adapter.owner,
                "field-cell-action",
                local_id,
            )
    raise AssertionError("reverse tile application has no primitive pair action")


def test_primitive_store_audit_rejects_foreign_action_and_integer_aliases() -> None:
    term, adapter, _application = _runtime()
    assert isinstance(adapter._compositions, LedgerDict)
    key, result = next(iter(adapter._compositions.items()))
    foreign = FieldCellActionID(
        ArenaToken("foreign"),
        key[0].kind,
        key[0].local_id,
    )
    corruptions: tuple[
        tuple[object, object],
        ...,
    ] = (
        ((foreign, key[1]), result),
        ((key[0], True), result),
        (key, True),
    )
    raw = cast(dict[object, object], adapter._compositions._data)
    for bad_key, bad_result in corruptions:
        original = dict(raw)
        raw.clear()
        raw[bad_key] = bad_result
        try:
            report = collect_ledger_metrics(term._ledger)
            assert report.forbidden_future_payloads > 0
            assert report.representation_boundary_complete == 0
        finally:
            raw.clear()
            raw.update(original)


def test_primitive_law_rejects_step_and_emit_schema_bounds_before_work() -> None:
    term, adapter, _application = _runtime()
    action = _primitive_reverse_action(adapter)
    kernel = adapter.primitive_law(action)
    before = term._ledger.snapshot()
    invalid_calls: tuple[Callable[[], int], ...] = (
        lambda: kernel.advance(BoundarySide.LEFT, 10**6, 0),
        lambda: kernel.advance(BoundarySide.LEFT, 0, 10**6),
        lambda: kernel.advance(BoundarySide.LEFT, True, 0),
        lambda: kernel.emit(10**6, 0, 0),
        lambda: kernel.emit(0, 10**6, 0),
        lambda: kernel.emit(0, 0, 10**6),
    )
    for invalid in invalid_calls:
        with pytest.raises(ValueError, match="outside primitive interface"):
            invalid()
    assert term._ledger.snapshot() == before


def test_warm_primitive_interface_avoids_recompiling_the_interface(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _term, adapter, application = _runtime()
    expected = application.interface()

    def poisoned(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("warm primitive call recompiled its interface")

    monkeypatch.setattr(adapter, "_compile_interface", poisoned)
    assert application.interface() == expected


def test_primitive_interface_rejects_foreign_warm_alias_before_lookup() -> None:
    term, adapter, application = _runtime()
    application.interface()
    results = adapter._require_results()
    before = term._ledger.snapshot()
    for local in (True, float(application.action.local_id)):
        foreign = FieldCellActionID(
            application.action.owner,
            application.action.kind,
            application.action.local_id,
        )
        object.__setattr__(foreign, "local_id", local)
        key = PoweredInterfaceKey(foreign, application.source, application.wiring)
        with pytest.raises((TypeError, ValueError)):
            results.lookup_interface(key)
    foreign_owner = FieldCellActionID(
        ArenaToken("foreign"),
        application.action.kind,
        application.action.local_id,
    )
    with pytest.raises((TypeError, ValueError)):
        results.lookup_interface(
            PoweredInterfaceKey(
                foreign_owner,
                application.source,
                application.wiring,
            )
        )
    assert term._ledger.snapshot() == before


def test_primitive_inventory_independently_rejects_corrupted_domains() -> None:
    term, adapter, _application = _runtime()
    action = _primitive_reverse_action(adapter)
    record = adapter._action(action)
    kernels = adapter.kernels._kernels
    assert isinstance(kernels, LedgerList)
    raw_kernels: list[PrimitiveKernel] = kernels._data
    original = raw_kernels[record.kernel.local_id]
    assert type(original) is PrimitiveKernel
    for invalid_left in (
        (True, *original.left[1:]),
        (*original.left, original.left[0]),
    ):
        corrupted = replace(original, left=invalid_left)
        # Deliberately bypass the append-only wrapper while retaining its
        # mutation-tracked backing list.  Production callers cannot use this
        # seam; the audit must still reject corrupt retained storage.
        raw_kernels[record.kernel.local_id] = corrupted
        try:
            assert collect_ledger_metrics(term._ledger).forbidden_future_payloads > 0
        finally:
            raw_kernels[record.kernel.local_id] = original


def test_primitive_interface_and_result_reserve_atomically() -> None:
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )

    term, adapter, _application = _runtime()
    cold_action = adapter.admit(BaseBlockEffect(3))
    leaf = adapter.tiles.leaf(adapter.alphabet(cold_action), 0)
    try:
        cold_kernel = adapter._action(cold_action).kernel
        assert not any(
            type(key) is LeafProductKey and key.kernel == cold_kernel
            for key in adapter._leaf_records
        )
        entries = term._ledger.snapshot().entries
        term._ledger.tighten_limits(None, entries + 1)
        before = term._ledger.snapshot()
        with pytest.raises(BlockContextBudgetExceeded):
            adapter.leaf_interface(
                cold_action,
                leaf.tile,
                adapter.wiring(cold_action),
            )
        assert not any(
            type(key) is LeafProductKey and key.kernel == cold_kernel
            for key in adapter._leaf_records
        )
        after = term._ledger.snapshot()
        assert (after.entries, after.nodes, after.inventory) == (
            before.entries,
            before.nodes,
            before.inventory,
        )
    finally:
        leaf.close()

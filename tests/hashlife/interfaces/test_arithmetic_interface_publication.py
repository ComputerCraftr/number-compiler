"""Closed arithmetic interfaces publish atomically through the quotient owner."""

from __future__ import annotations

from dataclasses import replace
from typing import Literal, cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.radix_division import SymbolicBinaryDivisionEffect
from number_compiler.arithmetic.radix_port_functions import RadixPortFunction
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.interfaces.diamond_quotient import (
    DiamondQuotientArena,
    LocalInterfaceID,
    MacroComponents,
    QuotientRecord,
)
from number_compiler.hashlife.observation.tile_projection import build_tile_projection
from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import (
    LedgerDict,
    _TrackedDict,
)
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect


def _retained(
    ledger: ResourceLedger, arena: DiamondQuotientArena
) -> tuple[object, ...]:
    snapshot = ledger.snapshot()
    return (
        tuple(arena._nodes),
        tuple(arena._keys.items()),
        tuple(arena._normalizations.items()),
        tuple(arena._parents.items()),
        snapshot.entries,
        snapshot.nodes,
        snapshot.inventory,
    )


def _candidate(
    arena: DiamondQuotientArena, identity: LocalInterfaceID
) -> tuple[PortSignatureID, MacroComponents]:
    record = arena.resolve(identity)
    output = record.components.output
    assert type(output) is RadixPortFunction
    assert output.kind == "output"
    assert output.value in (0, 1)
    return (
        record.signature,
        replace(
            record.components,
            output=replace(output, value=1 - output.value),
        ),
    )


@pytest.mark.parametrize(
    ("store_kind", "after_insert"),
    tuple((kind, after) for kind in ("node", "key") for after in (False, True)),
)
def test_arithmetic_interface_store_failure_rolls_back_publication(
    monkeypatch: pytest.MonkeyPatch,
    store_kind: Literal["node", "key"],
    after_insert: bool,
) -> None:
    ledger = ResourceLedger()
    source = ExactSource((1,), 2, blank=2, extent=1, alphabet_size=2)
    with build_tile_projection(
        CollatzPhysicalBlockEffect(), SourceGeometry(ledger, source)
    ) as projection:
        adapter = projection.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter
        action = adapter.admit(
            SymbolicBinaryDivisionEffect(257), cocycle=TemporalCocycle()
        )
        interface_id = adapter._compile_interface(
            action, projection._application.source, adapter.wiring(action)
        )
        arena = projection.scheduler.results.interfaces
        signature, components = _candidate(arena, interface_id)
        retained = _retained(ledger, arena)
        peak = ledger.peak_entries, ledger.peak_nodes
        attempted_id = arena._next_node
        retained_record = arena.resolve(interface_id)
        publications = ledger.counters.get("quotient_semantic_interner_evaluations", 0)
        failures = ledger.counters.get("quotient_publication_failures", 0)
        node_store = cast(LedgerDict[int, QuotientRecord], arena._nodes)._data
        key_store = cast(LedgerDict[QuotientRecord, object], arena._keys)._data
        target = node_store if store_kind == "node" else key_store
        failed = False
        setitem = _TrackedDict.__setitem__

        def fail_setitem(
            store: _TrackedDict[object, object], key: object, value: object
        ) -> None:
            nonlocal failed
            if not failed and store is target:
                failed = True
                if after_insert:
                    setitem(store, key, value)
                raise MemoryError("injected quotient publication failure")
            setitem(store, key, value)

        monkeypatch.setattr(_TrackedDict, "__setitem__", fail_setitem)

        with pytest.raises(MemoryError, match="injected quotient publication"):
            arena.intern(signature, components)
        assert failed
        assert _retained(ledger, arena) == retained
        assert ledger.peak_entries >= peak[0]
        assert ledger.peak_nodes >= peak[1]
        assert (
            ledger.counters.get("quotient_semantic_interner_evaluations", 0)
            == publications
        )
        assert ledger.counters.get("quotient_publication_failures", 0) == failures + 1
        assert all(row.accounting_delta == 0 for row in ledger.inventory())
        assert arena.resolve(interface_id) is retained_record
        published = arena.intern(signature, components)
        assert published.local_id > attempted_id
        assert arena.resolve(interface_id) is retained_record


@pytest.mark.parametrize("budget", ("entries", "nodes"))
def test_arithmetic_interface_reservation_failure_cancels_before_publication(
    budget: Literal["entries", "nodes"],
) -> None:
    ledger = ResourceLedger()
    source = ExactSource((1,), 2, blank=2, extent=1, alphabet_size=2)
    with build_tile_projection(
        CollatzPhysicalBlockEffect(), SourceGeometry(ledger, source)
    ) as projection:
        adapter = projection.scheduler.adapter
        assert type(adapter) is PrimitiveTileKernelAdapter
        action = adapter.admit(
            SymbolicBinaryDivisionEffect(257), cocycle=TemporalCocycle()
        )
        interface_id = adapter._compile_interface(
            action, projection._application.source, adapter.wiring(action)
        )
        arena = projection.scheduler.results.interfaces
        signature, components = _candidate(arena, interface_id)
        retained = _retained(ledger, arena)
        next_node = arena._next_node
        failures = ledger.counters.get("quotient_publication_failures", 0)
        ledger.tighten_limits(
            ledger.nodes if budget == "nodes" else None,
            ledger.entries if budget == "entries" else None,
        )
        with pytest.raises(BlockContextBudgetExceeded):
            arena.intern(signature, components)
        assert _retained(ledger, arena) == retained
        assert arena._next_node == next_node
        assert ledger.counters.get("quotient_publication_failures", 0) == failures + 1
        assert all(row.accounting_delta == 0 for row in ledger.inventory())

"""Independent atomicity checks for multi-root Boolean/bit/structure publication."""

from __future__ import annotations

from itertools import product
from typing import TYPE_CHECKING

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FinitePort,
    FunctionSignature,
    SemanticNode,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
    FactoredFunction,
)
from number_compiler.hashlife.interfaces.semantic_structure_publication import (
    prepare_structures,
)
from number_compiler.hashlife.interfaces.semantic_structures import (
    StructureArena,
    StructureBuilder,
    StructuredNode,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import TrackedDict

if TYPE_CHECKING:
    from number_compiler.arithmetic.functions.finite_function_types import (
        SemanticFunctionID,
        SemanticRequest,
    )
    from number_compiler.hashlife.interfaces.semantic_bits import (
        FactoredFunctionID,
    )
    from number_compiler.hashlife.interfaces.semantic_structure_publication import (
        PreparedStructures,
    )
    from number_compiler.resources.ledger import ResourceInventory


def _prepared() -> tuple[
    ResourceLedger,
    StructureArena,
    FactoredFunctionID,
    tuple[FinitePort, FinitePort],
    PreparedStructures,
]:
    ledger = ResourceLedger()
    bits = BitFunctionArena(ledger)
    arena = StructureArena(bits)
    seed = bits.constant(FunctionSignature((), BOOL), 0)
    ports = (
        FinitePort(PortVariable(0, 0, "x", 0), 4),
        FinitePort(PortVariable(0, 0, "y", 0), 2),
    )
    builder = StructureBuilder(arena)
    roots = []
    for port in ports:
        identity = builder.variable(ports, port)
        value = builder.bit(identity)
        roots.append(
            builder.intern(
                StructuredNode(
                    value.signature,
                    "atom",
                    arena.functions._handle(value.valid),
                    atom=bits._handle(identity),
                )
            )
        )
    prepared = prepare_structures(builder, (roots[0], roots[1], roots[0]))
    assert prepared.functions.nodes and prepared.bits and prepared.nodes
    return ledger, arena, seed, ports, prepared


def _retention(
    ledger: ResourceLedger,
    arena: StructureArena,
) -> tuple[
    int,
    int,
    int,
    int,
    tuple[ResourceInventory, ...],
    tuple[SemanticNode, ...],
    tuple[tuple[SemanticNode, int], ...],
    tuple[tuple[SemanticRequest, SemanticFunctionID], ...],
    tuple[FactoredFunction, ...],
    tuple[tuple[FactoredFunction, int], ...],
    tuple[StructuredNode, ...],
    tuple[tuple[StructuredNode, int], ...],
]:
    snapshot = ledger.snapshot()
    return (
        snapshot.entries,
        snapshot.nodes,
        snapshot.peak_entries,
        snapshot.peak_nodes,
        snapshot.inventory,
        tuple(arena.functions.nodes),
        tuple(arena.functions.keys.items()),
        tuple(arena.functions.memo.items()),
        tuple(arena.bits.nodes),
        tuple(arena.bits.keys.items()),
        tuple(arena.nodes),
        tuple(arena.keys.items()),
    )


def test_missing_final_structure_interner_credit_rejects_before_any_boolean_append() -> (
    None
):
    ledger, arena, _, _, prepared = _prepared()
    before = _retention(ledger, arena)
    with pytest.raises(RuntimeError, match="atomic reservation"):
        prepared.publish_reserved()
    assert _retention(ledger, arena) == before
    assert not arena.nodes and not arena.keys
    prepared.cancel()
    assert not prepared.functions.nodes
    assert not prepared.functions.roots
    assert not prepared.bits
    assert not prepared.nodes
    assert not prepared.roots
    assert all(row.accounting_delta == 0 for row in ledger.inventory())


@pytest.mark.parametrize(
    ("key_type", "after_insert"),
    tuple(
        (key_type, after)
        for key_type in (SemanticNode, FactoredFunction, StructuredNode)
        for after in (False, True)
    ),
)
def test_publication_insert_failure_rolls_back_every_arena(
    monkeypatch: pytest.MonkeyPatch,
    key_type: type[object],
    after_insert: bool,
) -> None:
    ledger, arena, _, _, prepared = _prepared()
    retained = _retained_stores(arena)
    prepared.reserve_with()
    original = TrackedDict.__setitem__
    failed = False

    def fail_once(
        store: TrackedDict[object, object], key: object, value: object
    ) -> None:
        nonlocal failed
        if not failed and type(key) is key_type:
            failed = True
            if after_insert:
                original(store, key, value)
            raise MemoryError("injected publication failure")
        original(store, key, value)

    monkeypatch.setattr(TrackedDict, "__setitem__", fail_once)
    with pytest.raises(MemoryError, match="injected publication failure"):
        prepared.publish_reserved()
    prepared.cancel()
    assert failed
    assert retained == _retained_stores(arena)
    _assert_workspace_released(ledger)


def test_function_commit_failure_rolls_back_structures_and_boolean_stores(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, arena, _, _, prepared = _prepared()
    retained = _retained_stores(arena)
    prepared.reserve_with()

    def fail_commit(_prepared: object) -> None:
        raise MemoryError("injected semantic commit failure")

    monkeypatch.setattr(type(prepared.functions), "_commit", fail_commit)
    with pytest.raises(MemoryError, match="injected semantic commit failure"):
        prepared.publish_reserved()
    prepared.cancel()
    assert retained == _retained_stores(arena)
    _assert_workspace_released(ledger)


@pytest.mark.parametrize("budget", ("entries", "nodes"))
def test_failed_multi_root_reservation_keeps_every_actual_store_unchanged(
    budget: str,
) -> None:
    ledger, arena, _, _, prepared = _prepared()
    transaction = prepared.functions.transaction
    assert transaction is not None
    _, workspace_entries, workspace_nodes = transaction.workspace_charge
    forced = ledger.register("forced-semantic-publication", "test_reservation")
    additional = (
        (forced, workspace_entries + 1, 0)
        if budget == "entries"
        else (forced, 0, workspace_nodes + 1)
    )
    ledger.tighten_limits(
        ledger.nodes if budget == "nodes" else None,
        ledger.entries if budget == "entries" else None,
    )
    before = _retention(ledger, arena)
    with pytest.raises(BlockContextBudgetExceeded):
        prepared.reserve_with((additional,))
    assert _retention(ledger, arena) == before
    for root in prepared.roots:
        with pytest.raises(ValueError):
            arena.resolve(root)
    prepared.cancel()


@pytest.mark.parametrize("changed", ("boolean", "bit", "structure"))
def test_interleaved_arena_change_invalidates_prepared_roots_before_publication(
    changed: str,
) -> None:
    ledger, arena, seed, _, prepared = _prepared()
    if changed == "boolean":
        # A new signature ensures this cannot alias the pre-existing constants.
        port = FinitePort(PortVariable(3, 0, "unrelated", 0), 2)
        arena.functions.variable((port,), port, BOOL)
    elif changed == "bit":
        arena.bits.constant(FunctionSignature((), BOOL), 1)
    else:
        arena.atom(seed)
    before = _retention(ledger, arena)
    with pytest.raises(RuntimeError):
        prepared.reservations()
    with pytest.raises(RuntimeError):
        prepared.publish_reserved()
    assert _retention(ledger, arena) == before
    prepared.cancel()


def test_successful_multi_root_publication_shares_roots_and_charges_exact_inventory() -> (
    None
):
    ledger, arena, _, ports, prepared = _prepared()
    assert prepared.roots[0] == prepared.roots[2]
    credits = prepared.reservations()
    transaction = prepared.functions.transaction
    assert transaction is not None
    _, workspace_entries, workspace_nodes = transaction.workspace_charge
    before = ledger.snapshot()
    prepared.reserve_with()
    prepared.publish_reserved()
    after = ledger.snapshot()
    assert (
        after.entries - before.entries
        == sum(entries for _, entries, _ in credits) - workspace_entries
    )
    assert (
        after.nodes - before.nodes
        == sum(nodes for _, _, nodes in credits) - workspace_nodes
    )
    assert all(row.accounting_delta == 0 for row in ledger.inventory())
    for x, y in product(range(4), range(2)):
        inputs = {ports[0].variable: x, ports[1].variable: y}
        assert arena.evaluate_atom(prepared.roots[0], inputs) == x
        assert arena.evaluate_atom(prepared.roots[1], inputs) == y
    snapshot = _retention(ledger, arena)
    with pytest.raises(RuntimeError):
        prepared.publish_reserved()
    assert _retention(ledger, arena) == snapshot


def _retained_stores(arena: StructureArena) -> tuple[object, ...]:
    return (
        tuple(arena.functions.nodes),
        tuple(arena.functions.keys.items()),
        tuple(arena.functions.memo.items()),
        tuple(arena.bits.nodes),
        tuple(arena.bits.keys.items()),
        tuple(arena.nodes),
        tuple(arena.keys.items()),
    )


def _assert_workspace_released(ledger: ResourceLedger) -> None:
    assert all(row.accounting_delta == 0 for row in ledger.inventory())
    workspace = next(
        row for row in ledger.inventory() if row.role == "semantic_function_workspace"
    )
    assert workspace.entries == workspace.nodes == 0

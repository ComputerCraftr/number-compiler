from __future__ import annotations

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.physical_support_payload_audit import (
    audit_physical_support_payloads,
)
from number_compiler.sequences.collatz.physical_support import PhysicalSupportArena


def test_unbalanced_support_concat_accounts_only_retained_entries() -> None:
    ledger = ResourceLedger()
    arena = PhysicalSupportArena(max_nodes=256, ledger=ledger)
    first = arena.event(1)
    second = arena.event(4)
    combined = arena.concat(first, second)
    assert combined.ticks == 7
    assert tuple(combined.tick(index) for index in range(7)) == (
        True,
        False,
        True,
        False,
        False,
        False,
        False,
    )
    physical = tuple(
        item for item in ledger.inventory() if item.role.startswith("physical_shadow")
    )
    assert physical
    assert all(item.entries == item.observed_entries for item in physical)
    assert all(item.nodes == (item.observed_nodes or 0) for item in physical)
    assert not audit_physical_support_payloads(ledger).invalid


def test_support_payload_audit_rejects_modified_program() -> None:
    ledger = ResourceLedger()
    arena = PhysicalSupportArena(max_nodes=64, ledger=ledger)
    support = arena.event(2)
    object.__setattr__(support, "parity", True)
    assert audit_physical_support_payloads(ledger).invalid


def test_support_payload_audit_rejects_redirected_store_ledger() -> None:
    ledger = ResourceLedger()
    arena = PhysicalSupportArena(max_nodes=64, ledger=ledger)
    arena._store_ledger = ResourceLedger()
    assert audit_physical_support_payloads(ledger).invalid


@pytest.mark.parametrize(("entry", "cycle"), ((1, 14), (5, 11), (8, 13)))
def test_certified_tail_is_canonical_input_to_later_concat(
    entry: int, cycle: int
) -> None:
    arena = PhysicalSupportArena(max_nodes=512, ledger=ResourceLedger())
    support = arena._proved_collatz_power_two_tail(entry, cycle)
    word = (False,) * entry + tuple(index % 3 == 0 for index in range(cycle))
    assert tuple(support.tick(index) for index in range(len(word))) == word

    exact = arena.identity
    for parity in word:
        exact = arena.concat(exact, arena.odd if parity else arena.even)
    assert support is exact
    assert arena.concat(support, arena.odd) is arena.concat(exact, arena.odd)


def test_failed_support_join_releases_its_publication_reservation() -> None:
    ledger = ResourceLedger()
    arena = PhysicalSupportArena(max_nodes=3, ledger=ledger)
    before = (ledger.entries, ledger.nodes)
    with pytest.raises(BlockContextBudgetExceeded, match="node budget exceeded"):
        arena.run(True, 2)
    assert (ledger.entries, ledger.nodes) == before
    assert all(row.entries == row.observed_entries for row in ledger.inventory())
    assert not audit_physical_support_payloads(ledger).invalid

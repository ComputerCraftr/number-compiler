from __future__ import annotations

from typing import cast

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp import SLPNode
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.resources.stores import LedgerDict, LedgerList


def _arena() -> tuple[ResourceLedger, LedgerSLPArena]:
    ledger = ResourceLedger()
    arena = LedgerSLPArena(ledger, "slp-audit", "test_slp")
    leaf = arena.word((2, 7, 2))
    arena.repeat(leaf, 5)
    return ledger, arena


def test_registered_finite_slp_nodes_and_interners_are_structurally_audited() -> None:
    ledger, arena = _arena()
    try:
        report = audit_registered_payloads(ledger, fresh=True)
        assert report.forbidden_future_payloads == 0
        assert report.unbounded_future_integers == 0
        assert report.unknown_payloads == 0
    finally:
        arena.dispose()


def test_slp_audit_rejects_wrong_child_length() -> None:
    ledger, arena = _arena()
    try:
        concat = next(node for node in arena.nodes if node.kind == "CONCAT")
        object.__setattr__(concat, "length", concat.length + 1)
        report = audit_registered_payloads(ledger, fresh=True)
        assert report.forbidden_future_payloads > 0
    finally:
        arena.dispose()


def test_slp_audit_rejects_interner_id_mismatch() -> None:
    ledger, arena = _arena()
    try:
        term_table = cast(LedgerDict[int, int], arena._term_store._data)
        term_table._data[2] = len(arena.nodes) + 100
        report = audit_registered_payloads(ledger, fresh=True)
        assert report.forbidden_future_payloads > 0
    finally:
        arena.dispose()


def test_slp_audit_rejects_owner_rebinding() -> None:
    ledger, arena = _arena()
    owners = arena.owners
    try:
        arena.owners = (owners[0], owners[2], owners[1], owners[3])
        report = audit_registered_payloads(ledger, fresh=True)
        assert report.forbidden_future_payloads > 0
    finally:
        arena.owners = owners
        arena.dispose()


def test_slp_audit_rejects_partial_interner_disposal() -> None:
    ledger, arena = _arena()
    try:
        arena._rep_store.dispose()
        report = audit_registered_payloads(ledger, fresh=True)
        assert report.forbidden_future_payloads > 0
    finally:
        arena.dispose()


def test_slp_audit_rejects_node_id_reordering() -> None:
    ledger, arena = _arena()
    try:
        terminal = next(node for node in arena.nodes if node.kind == "TERM")
        object.__setattr__(terminal, "id", terminal.id + 1)
        report = audit_registered_payloads(ledger, fresh=True)
        assert report.forbidden_future_payloads > 0
    finally:
        arena.dispose()


def test_unregistered_slp_node_and_disposed_stale_node_are_not_approved() -> None:
    ledger = ResourceLedger()
    arena = LedgerSLPArena(ledger, "slp-unregistered", "test_slp")
    arena.terminal(4)
    stale_node = arena.nodes[1]
    arena.dispose()
    owner = ledger.register("unowned-slp", "arbitrary_payload")
    store: LedgerList[object] = ledger.make_list(owner)
    ledger.reserve(owner, entries=1, nodes=1)
    store.append(stale_node)
    report = audit_registered_payloads(ledger, fresh=True)
    assert report.forbidden_future_payloads > 0 or report.unknown_payloads > 0


def test_slp_node_class_alone_does_not_grant_payload_approval() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("unregistered-slp-node", "arbitrary_payload")
    store: LedgerList[object] = ledger.make_list(owner)
    ledger.reserve(owner, entries=1, nodes=1)
    store.append(SLPNode(0, "TERM", 1, symbol=4))
    report = audit_registered_payloads(ledger, fresh=True)
    assert report.forbidden_future_payloads > 0 or report.unknown_payloads > 0

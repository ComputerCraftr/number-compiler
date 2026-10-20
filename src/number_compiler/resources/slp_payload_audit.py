"""Structural audit for retained ledger-owned straight-line programs."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from typing import cast

from number_compiler.arithmetic.automata.ledgered_slp import (
    LedgerSLPArena,
    LedgerSLPArenaAuditSnapshot,
)
from number_compiler.arithmetic.automata.slp import SLPNode
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.payload_containers import audit_mapping_items
from number_compiler.resources.stores import (
    LedgerDict,
    LedgerList,
    TrackedDict,
)


@dataclass(frozen=True, slots=True)
class SLPPayloadAudit:
    """The exact owner-qualified members validated by the SLP audit."""

    approved: frozenset[tuple[int, int]]
    invalid: frozenset[tuple[int, int]]

    def approves(self, owner: int, value: object) -> bool:
        return (owner, id(value)) in self.approved


def _node_shape(node: object, index: int, nodes: Sequence[object]) -> bool:
    if type(node) is not SLPNode:
        return False
    record = node
    if type(record.kind) is not str or any(
        type(value) is not int
        for value in (
            record.id,
            record.length,
            record.symbol,
            record.left,
            record.right,
            record.child,
            record.count,
        )
    ):
        return False
    if record.id != index or record.length < 0:
        return False
    if record.kind == "EMPTY":
        return (
            index == 0
            and record.length == 0
            and (record.symbol, record.left, record.right, record.child, record.count)
            == (-1, -1, -1, -1, 0)
        )
    if record.kind == "TERM":
        return (
            record.length == 1
            and 0 <= record.symbol < 1 << 64
            and (record.left, record.right, record.child, record.count)
            == (-1, -1, -1, 0)
        )
    if record.kind == "CONCAT":
        if (
            record.symbol != -1
            or record.child != -1
            or record.count != 0
            or not 0 < record.left < index
            or not 0 < record.right < index
        ):
            return False
        left, right = nodes[record.left], nodes[record.right]
        return (
            type(left) is SLPNode
            and type(right) is SLPNode
            and record.length == left.length + right.length
        )
    if record.kind == "REPEAT":
        if (
            record.symbol != -1
            or record.left != -1
            or record.right != -1
            or record.count < 2
            or not 0 < record.child < index
        ):
            return False
        child = nodes[record.child]
        return (
            type(child) is SLPNode
            and child.kind not in ("EMPTY", "REPEAT")
            and child.length > 0
            and record.length == child.length * record.count
        )
    return False


def _interner_rows(
    memo: object,
    ledger: ResourceLedger,
    owner: int,
    container: object,
    kind: str,
) -> tuple[tuple[object, object], ...] | None:
    if type(memo) is not OwnedMemo or type(container) is not LedgerDict:
        return None
    retained_memo = cast(OwnedMemo[object, object], memo)
    store = cast(LedgerDict[object, object], container)
    memo_state = retained_memo.audit_snapshot()
    backing_store: Mapping[object, object] = store.backing_store
    tracked_store = cast(TrackedDict[object, object], backing_store)
    if (
        memo_state.ledger is not ledger
        or type(memo_state.owner) is not int
        or memo_state.owner != owner
        or type(memo_state.nodes_per_entry) is not int
        or memo_state.nodes_per_entry != 0
        or retained_memo.node_cost is not None
        or memo_state.container is not store
        or type(memo_state.dynamic_nodes) is not int
        or memo_state.dynamic_nodes != 0
        or type(memo_state.pending_clear_entries) is not int
        or memo_state.pending_clear_entries != 0
        or type(memo_state.pending_clear_nodes) is not int
        or memo_state.pending_clear_nodes != 0
        or type(memo_state.disposed) is not bool
        or store.ledger is not ledger
        or type(store.owner) is not int
        or store.owner != owner
        or type(store.nodes_per_entry) is not int
        or store.nodes_per_entry != 0
        or type(store.write_once) is not bool
        or store.write_once
        or type(store.sealed) is not bool
        or not store.sealed
        or not ledger.is_factory_container(store)
        or type(backing_store) is not TrackedDict
        or not tracked_store.belongs_to(ledger)
    ):
        return None
    try:
        memo_rows = audit_mapping_items(retained_memo)
    except (KeyError, TypeError, ValueError, RuntimeError):
        return None
    rows: list[tuple[object, object]] = []
    for key, local_id in memo_rows:
        row_key: object = key
        if type(local_id) is not int or local_id < 0:
            return None
        if kind == "term" and (type(key) is not int or not 0 <= key < 1 << 64):
            return None
        if kind in ("concat", "repeat"):
            if type(key) is not tuple:
                return None
            parts: tuple[object, ...] = cast(tuple[object, ...], key)
            if len(parts) != 2 or any(
                type(part) is not int or part < 0 for part in parts
            ):
                return None
        rows.append((row_key, local_id))
    return tuple(rows)


def audit_ledger_slp_payloads(
    ledger: ResourceLedger,
    roots: Sequence[object],
    containers: Mapping[int, object],
) -> SLPPayloadAudit:
    """Validate SLP root, nodes and interners before numeric payload scanning.

    An ``SLPNode`` class or local integer ID alone grants no exemption. The exact
    arena root and all four stores must still be ledger registered and agree.
    """
    approved: set[tuple[int, int]] = set()
    invalid: set[tuple[int, int]] = set()
    inventory = {row.owner: row for row in ledger.inventory()}
    for arena_value in roots:
        if type(arena_value) is not LedgerSLPArena:
            continue
        arena = arena_value
        owners_value = arena.owners
        fallback_owner = (
            owners_value[0]
            if type(owners_value) is tuple
            and owners_value
            and type(owners_value[0]) is int
            else 0
        )
        try:
            snapshot = arena.audit_snapshot()
            if type(snapshot) is not LedgerSLPArenaAuditSnapshot:
                raise AttributeError("SLP arena has a foreign audit snapshot")
            nodes = snapshot.node_store
            memos = (snapshot.term_memo, snapshot.concat_memo, snapshot.repeat_memo)
            if type(nodes) is not LedgerList or any(
                type(memo) is not OwnedMemo for memo in memos
            ):
                raise AttributeError("SLP arena has a foreign retained store")
            if not snapshot.node_store_alias_matches or not all(
                (
                    snapshot.term_alias_matches,
                    snapshot.concat_alias_matches,
                    snapshot.repeat_alias_matches,
                )
            ):
                raise AttributeError("SLP arena has a rebound public store")
            owners = (nodes.owner, *(memo.owner for memo in memos))
            stores: tuple[object, ...] = (
                nodes,
                *(memo.audit_snapshot().container for memo in memos),
            )
        except AttributeError:
            invalid.add((fallback_owner, id(arena)))
            continue
        malformed_owners = (
            type(owners_value) is not tuple
            or len(owners_value) != 4
            or any(type(owner) is not int for owner in owners_value)
            or any(type(owner) is not int for owner in owners)
        )
        if malformed_owners:
            invalid.update((owner, id(arena)) for owner in owners if type(owner) is int)
            invalid.add((fallback_owner, id(arena)))
            continue
        node_rows = snapshot.node_rows
        entries = tuple(
            _interner_rows(memo, ledger, owner, store, kind)
            for memo, owner, store, kind in zip(
                memos,
                owners[1:],
                stores[1:],
                ("term", "concat", "repeat"),
                strict=True,
            )
        )
        valid = (
            snapshot.ledger is ledger
            and owners_value == owners
            and len(set(owners)) == 4
            and type(snapshot.empty_id) is int
            and snapshot.empty_id == 0
            and type(snapshot.closed) is bool
            and type(snapshot.cleanup_complete) is bool
            and type(snapshot.nodes_released) is bool
            and type(nodes) is LedgerList
            and nodes.ledger is ledger
            and type(nodes.owner) is int
            and nodes.owner == owners[0]
            and type(nodes.nodes_per_entry) is int
            and nodes.nodes_per_entry == 1
            and type(nodes.append_only) is bool
            and nodes.append_only
            and type(nodes.sealed) is bool
            and nodes.sealed
            and nodes.has_tracked_backing_store
            and ledger.is_factory_container(nodes)
            and all(rows is not None for rows in entries)
            and all(owner in inventory for owner in owners)
            and all(
                containers.get(owner) is store
                for owner, store in zip(owners, stores, strict=True)
            )
        )
        if valid:
            first = inventory[owners[0]]
            owner_kind = first.role.lower().replace("-", "_").removesuffix("_grammar")
            suffixes = (
                ("-slp-nodes", owner_kind + "_grammar"),
                ("-slp-terminals", owner_kind + "_interner"),
                ("-slp-concats", owner_kind + "_interner"),
                ("-slp-repeats", owner_kind + "_interner"),
            )
            prefix = first.name.removesuffix(suffixes[0][0])
            valid = bool(owner_kind) and all(
                inventory[owner].name == prefix + suffix
                and inventory[owner].role.lower().replace("-", "_") == role
                and inventory[owner].scope == first.scope
                for owner, (suffix, role) in zip(owners, suffixes, strict=True)
            )
        closed = snapshot.closed is True and snapshot.cleanup_complete is True
        valid &= all(
            inventory[owner].disposed == closed
            for owner in owners
            if owner in inventory
        )
        valid &= all(
            type(memo) is OwnedMemo
            and type(memo.audit_snapshot().disposed) is bool
            and memo.audit_snapshot().disposed == closed
            for memo in memos
        )
        valid &= snapshot.nodes_released == closed
        if any(rows is None for rows in entries):
            valid = False
        if valid and closed:
            valid &= (
                not node_rows
                and all(not rows for rows in entries if rows is not None)
                and all(
                    inventory[owner].entries == 0
                    and inventory[owner].nodes == 0
                    and inventory[owner].observed_entries == 0
                    and inventory[owner].observed_nodes == 0
                    for owner in owners
                )
            )
        elif valid:
            valid &= not snapshot.closed and not snapshot.cleanup_complete
            valid &= (
                inventory[owners[0]].entries == len(node_rows)
                and inventory[owners[0]].nodes == len(node_rows)
                and inventory[owners[0]].observed_entries == len(node_rows)
                and inventory[owners[0]].observed_nodes == len(node_rows)
                and all(
                    inventory[owner].entries == len(entry_rows)
                    and inventory[owner].nodes == 0
                    and inventory[owner].observed_entries == len(entry_rows)
                    and inventory[owner].observed_nodes == 0
                    for owner, entry_rows in zip(owners[1:], entries, strict=True)
                    if entry_rows is not None
                )
                and len(node_rows) >= 1
                and sum(
                    type(node) is SLPNode and node.kind == "EMPTY" for node in node_rows
                )
                == 1
                and all(
                    _node_shape(node, index, node_rows)
                    for index, node in enumerate(node_rows)
                )
            )
        if valid and not closed:
            term_rows, concat_rows, repeat_rows = entries
            assert (
                term_rows is not None
                and concat_rows is not None
                and repeat_rows is not None
            )
            typed_nodes: list[SLPNode] = []
            for candidate in node_rows:
                if type(candidate) is not SLPNode:
                    valid = False
                    continue
                typed_nodes.append(candidate)
            term_index = dict(term_rows)
            concat_index = dict(concat_rows)
            repeat_index = dict(repeat_rows)
            valid &= (
                len(term_index) == len(term_rows)
                and len(concat_index) == len(concat_rows)
                and len(repeat_index) == len(repeat_rows)
                and len(term_rows) == sum(node.kind == "TERM" for node in typed_nodes)
                and len(concat_rows)
                == sum(node.kind == "CONCAT" for node in typed_nodes)
                and len(repeat_rows)
                == sum(node.kind == "REPEAT" for node in typed_nodes)
            )
            for node in typed_nodes:
                if node.kind == "TERM":
                    valid &= term_index.get(node.symbol) == node.id
                elif node.kind == "CONCAT":
                    valid &= concat_index.get((node.left, node.right)) == node.id
                elif node.kind == "REPEAT":
                    valid &= repeat_index.get((node.child, node.count)) == node.id
            for entry_rows, table, kind in zip(
                (term_rows, concat_rows, repeat_rows),
                (term_index, concat_index, repeat_index),
                ("TERM", "CONCAT", "REPEAT"),
                strict=True,
            ):
                valid &= all(
                    type(local_id) is int
                    and 0 <= local_id < len(typed_nodes)
                    and typed_nodes[local_id].kind == kind
                    and table.get(key) == local_id
                    for key, local_id in entry_rows
                )

        destination = approved if valid else invalid
        for owner, store in zip(owners, stores, strict=True):
            destination.add((owner, id(store)))
        for retained_node in node_rows:
            destination.add((owners[0], id(retained_node)))
        for owner, maybe_rows in zip(owners[1:], entries, strict=True):
            if maybe_rows is not None:
                for key, value in maybe_rows:
                    destination.update(((owner, id(key)), (owner, id(value))))
        if not valid:
            invalid.add((owners[0], id(arena)))
    return SLPPayloadAudit(frozenset(approved), frozenset(invalid))


__all__ = ["SLPPayloadAudit", "audit_ledger_slp_payloads"]

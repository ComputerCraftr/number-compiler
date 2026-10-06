"""Independent shape/ownership checks for completed decimal pair grammars."""

from __future__ import annotations

from collections.abc import Mapping, Sequence, Sized

from number_compiler.arithmetic.automata.slp import SLPNode
from number_compiler.resources.ledger import (
    OwnedMemo,
    ResourceInventory,
    ResourceLedger,
)
from number_compiler.resources.stores import LedgerDict, LedgerList


def _node_shape(node: SLPNode, index: int, nodes: Sequence[SLPNode]) -> bool:
    if type(node) is not SLPNode or node.id != index or type(node.length) is not int:
        return False
    if node.kind == "EMPTY":
        return index == 0 and node.length == 0
    if node.kind == "TERM":
        return node.length == 1 and type(node.symbol) is int and 0 <= node.symbol <= 21
    if node.kind == "CONCAT":
        return (
            type(node.left) is int
            and type(node.right) is int
            and 0 <= node.left < index
            and 0 <= node.right < index
            and node.length == nodes[node.left].length + nodes[node.right].length
        )
    if node.kind == "REPEAT":
        return (
            type(node.child) is int
            and 0 <= node.child < index
            and type(node.count) is int
            and node.count >= 2
            and node.length == nodes[node.child].length * node.count
        )
    return False


def _store_shape(
    ledger: ResourceLedger,
    containers: Mapping[int, object],
    store: object,
    owner: int,
    role: str,
) -> bool:
    if type(store) not in (LedgerList, LedgerDict, OwnedMemo) or not isinstance(
        store, Sized
    ):
        return False
    inventory = next((item for item in ledger.inventory() if item.owner == owner), None)
    container = store._data if type(store) is OwnedMemo else store
    nodes = 0 if role == "reverse_pair_output_interner" else len(store)
    return (
        type(inventory) is ResourceInventory
        and containers.get(owner) is container
        and inventory.role == role
        and not inventory.disposed
        and inventory.payloads_registered
        and inventory.entries == len(store)
        and inventory.observed_entries == len(store)
        and inventory.nodes == nodes
    )


def _summary_matches(root: object, index: int) -> bool:
    from number_compiler.sequences.reverse_add.q19_output import (
        _Q19,
        ReversePairQ19OutputOwner,
        _WordSummary,
    )

    if type(root) is not ReversePairQ19OutputOwner:
        return False
    node = root.arena.nodes[index]
    value = root._summaries[index]
    identity = _Q19.identity()
    if node.kind == "EMPTY" or node.kind == "TERM" and node.symbol > 18:
        expected = _WordSummary(0, identity, identity, identity, identity)
    elif node.kind == "TERM":
        atom = _Q19.atom(node.symbol)
        expected = _WordSummary(1, atom, atom, identity, identity)
    elif node.kind == "CONCAT":
        left = root._summaries[node.left]
        right = root._summaries[node.right]
        prefix = (left.prefix_forward, left.prefix_reverse)
        if right.symbols:
            prefix = (
                left.forward.then(right.prefix_forward),
                right.prefix_reverse.then(left.reverse),
            )
        expected = _WordSummary(
            left.symbols + right.symbols,
            left.forward.then(right.forward),
            right.reverse.then(left.reverse),
            *prefix,
        )
    elif node.kind == "REPEAT":
        child = root._summaries[node.child]
        expected = _WordSummary(
            child.symbols * node.count,
            child.forward.repeat(node.count),
            child.reverse.repeat(node.count),
            child.forward.repeat(node.count - 1).then(child.prefix_forward),
            child.prefix_reverse.then(child.reverse.repeat(node.count - 1)),
        )
    else:
        return False
    return value == expected


def _occurrence_summary_matches(
    root: object, grammar_root: int
) -> tuple[int, int, int]:
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )

    if type(root) is not ReversePairQ19OutputOwner:
        raise TypeError("expected the exact reverse pair output owner")
    summary = root._summaries[grammar_root]
    node = root.arena.nodes[grammar_root]
    while node.kind in ("CONCAT", "REPEAT"):
        node = root.arena.nodes[node.left if node.kind == "CONCAT" else node.child]
    parity = node.symbol - 19
    if node.kind != "TERM" or parity not in (0, 1):
        raise ValueError("issued pair grammar lacks its parity header")
    tail = summary.prefix_reverse if parity else summary.reverse
    full = summary.forward.then(tail)
    if full.length != 2 * summary.symbols - parity:
        raise ValueError("issued pair grammar has inconsistent symmetry")
    return full.length, full.domain, full.f9


def audit_reverse_pair_output_roots(
    ledger: ResourceLedger,
    roots: tuple[object, ...],
    containers: Mapping[int, object],
) -> tuple[set[int], set[int], set[tuple[int, int]]]:
    """Inspect completed records without invoking a projector or point evaluator."""
    from number_compiler.sequences.reverse_add.q19_output import (
        _Q19,
        ReversePairOutputOccurrence,
        ReversePairQ19OutputOwner,
        _FrozenPairStepLaw,
        _LedgerSLPArena,
        _WordSummary,
    )

    approved: set[int] = set()
    recognized: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    for root in roots:
        if type(root) is not ReversePairQ19OutputOwner or root._disposed:
            continue
        recognized.add(id(root))
        arena = root.arena
        owner = root._issued_owner
        valid = (
            root.ledger is ledger
            and not root._disposed
            and type(arena) is _LedgerSLPArena
            and arena.ledger is ledger
            and root.projector.arena is arena
            and root.projector.machine is root.machine
            and root.base == 10
            and root.machine.base == 10
            and type(root.machine) is _FrozenPairStepLaw
            and type(root._binding) is tuple
            and len(root._binding) == 7
            and root._binding[0] is ledger
            and root._binding[1] is root._digits
            and root._binding[2] == 10
            and root._binding[3] is root._authority
            and root._binding[4] is arena
            and root._binding[5] is root.projector
            and root._binding[6] is root.machine
        )
        stores = (
            (arena.nodes, arena.owners[0], "reverse_pair_output_grammar"),
            (arena._term, arena.owners[1], "reverse_pair_output_interner"),
            (arena._cat, arena.owners[2], "reverse_pair_output_interner"),
            (arena._rep, arena.owners[3], "reverse_pair_output_interner"),
            (root._summaries, root._summary_owner, "reverse_pair_q19_summary"),
            (root._issued, owner, "reverse_pair_output_occurrence"),
            *(
                (store, store_owner, "reverse_pair_projector_memo")
                for store, store_owner in zip(
                    (
                        root.projector._fwd,
                        root.projector._rev,
                        root.projector._block,
                        root.projector._fwd_power,
                        root.projector._rev_power,
                    ),
                    root._projector_owners,
                    strict=True,
                )
            ),
        )
        ledger.bump(
            "reverse_pair_output_audit_entries",
            sum(len(store) for store, _, _ in stores if isinstance(store, Sized)),
        )
        valid &= all(_store_shape(ledger, containers, *item) for item in stores)
        valid &= arena.empty_id == 0 and all(
            _node_shape(node, index, arena.nodes)
            for index, node in enumerate(arena.nodes)
        )
        if not valid:
            invalid.add((owner, id(root)))
            continue
        size = len(arena.nodes)
        for symbol_key, index in arena._term.items():
            valid &= (
                type(index) is int
                and 0 <= index < size
                and arena.nodes[index].kind == "TERM"
                and arena.nodes[index].symbol == symbol_key
            )
        for interner, kind in ((arena._cat, "CONCAT"), (arena._rep, "REPEAT")):
            for node_key, index in interner.items():
                if type(index) is not int or not 0 <= index < size:
                    valid = False
                    continue
                node = arena.nodes[index]
                expected = (
                    (node.left, node.right)
                    if kind == "CONCAT"
                    else (node.child, node.count)
                )
                valid &= node.kind == kind and node_key == expected
        for index, summary in root._summaries.items():
            valid &= type(index) is int and 0 <= index < size
            if type(summary) is not _WordSummary:
                valid = False
                continue
            for folded in (
                summary.forward,
                summary.reverse,
                summary.prefix_forward,
                summary.prefix_reverse,
            ):
                valid &= (
                    type(folded) is _Q19
                    and type(folded.length) is int
                    and folded.length >= 0
                    and type(folded.domain) is int
                    and folded.domain in (-1, 0, 1)
                    and type(folded.f9) is int
                    and 0 <= folded.f9 < 9
                )
            valid &= summary.symbols == summary.forward.length == summary.reverse.length
            try:
                valid &= _summary_matches(root, index)
            except (KeyError, IndexError, TypeError, ValueError, AttributeError):
                valid = False
        for occurrence_key, occurrence in root._issued.items():
            recognized.add(id(occurrence))
            if type(occurrence) is not ReversePairOutputOccurrence:
                valid = False
                continue
            try:
                occurrence.__post_init__()
            except (TypeError, ValueError):
                valid = False
                continue
            try:
                valid &= _occurrence_summary_matches(root, occurrence.root) == (
                    occurrence.pair_width,
                    occurrence.q19_domain,
                    occurrence.q19_f9,
                )
            except (KeyError, IndexError, TypeError, ValueError, AttributeError):
                valid = False
            valid &= (
                occurrence.owner is root._authority
                and occurrence_key == (occurrence.root, occurrence.temporal_steps)
                and 0 <= occurrence.root < size
                and occurrence.root in root._summaries
                and occurrence.output_width
                == occurrence.pair_width + int(occurrence.q19_domain == 1)
                and occurrence.growth == occurrence.output_width - len(root._digits)
                and 0 <= occurrence.growth <= occurrence.temporal_steps
            )
        left_states, right_states = root.machine.left.states, root.machine.right.states
        for store, states, arity in (
            (root.projector._fwd, left_states, 2),
            (root.projector._rev, right_states, 2),
            (root.projector._fwd_power, left_states, 3),
            (root.projector._rev_power, right_states, 3),
        ):
            for memo_key, result in store.items():
                valid &= (
                    type(memo_key) is tuple
                    and len(memo_key) == arity
                    and all(type(part) is int for part in memo_key)
                    and 0 <= memo_key[0] < size
                    and memo_key[1] in states
                    and (arity == 2 or memo_key[-1] >= 0)
                    and (result is None or type(result) is int and result in states)
                )
        for block_key, result in root.projector._block.items():
            valid &= (
                type(block_key) is tuple
                and len(block_key) == 3
                and all(type(part) is int for part in block_key)
                and 0 <= block_key[0] < size
                and block_key[1] in left_states
                and block_key[2] in right_states
                and type(result) is int
                and 0 <= result < size
            )
        if valid:
            approved.update((id(root), id(arena), id(root.projector)))
            approved.update(id(node) for node in arena.nodes)
            approved.update(id(store) for store, _, _ in stores)
            approved.update(
                id(store._data) for store, _, _ in stores if type(store) is OwnedMemo
            )
            for retained_store, _, _ in stores:
                if isinstance(retained_store, Mapping):
                    approved.update(
                        id(key) for key in retained_store if type(key) is tuple
                    )
            approved.update(id(summary) for summary in root._summaries.values())
            approved.update(id(occurrence) for occurrence in root._issued.values())
        else:
            invalid.add((owner, id(root)))
    return approved, recognized, invalid

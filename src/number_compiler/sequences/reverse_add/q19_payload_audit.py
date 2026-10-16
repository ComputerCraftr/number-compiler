"""Independent shape/ownership checks for completed decimal pair grammars."""

from __future__ import annotations

from collections.abc import Mapping, Sequence, Sized
from itertools import chain

from number_compiler.arithmetic.automata.slp import SLPNode
from number_compiler.resources.ledger import (
    OwnedMemo,
    ResourceInventory,
    ResourceLedger,
)
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditEntry,
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
    inventory: Mapping[int, ResourceInventory],
    store: object,
    owner: int,
    role: str,
) -> bool:
    if type(store) not in (LedgerList, LedgerDict, OwnedMemo) or not isinstance(
        store, Sized
    ):
        return False
    item = inventory.get(owner)
    container = store._data if type(store) is OwnedMemo else store
    if role == "reverse_pair_output_interner":
        nodes = 0
    elif type(store) is OwnedMemo and store.node_cost is not None:
        nodes = 0
        try:
            for key, wrapped in store._data.items():
                payload = wrapped.value
                retained = wrapped.nodes
                if type(retained) is not int or retained != store._entry_nodes(
                    key, payload
                ):
                    return False
                nodes += retained
        except (AttributeError, KeyError, TypeError, ValueError):
            return False
    elif type(store) is OwnedMemo:
        nodes = len(store) * store.nodes_per_entry
    else:
        nodes = len(store)
    return (
        type(item) is ResourceInventory
        and containers.get(owner) is container
        and item.role == role
        and not item.disposed
        and item.payloads_registered
        and item.entries == len(store)
        and item.observed_entries == len(store)
        and item.nodes == nodes
    )


def _summary_matches(root: object, index: int) -> bool:
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )
    from number_compiler.sequences.reverse_add.q19_word_summary import (
        _Q19,
        _WordSummary,
    )

    if type(root) is not ReversePairQ19OutputOwner:
        return False
    node = root.arena.nodes[index]
    value = root._summaries[index]
    identity = _Q19.identity()
    if node.kind == "EMPTY" or node.kind == "TERM" and node.symbol > 18:
        expected = _WordSummary(
            0, identity, identity, identity, identity, None, None, 0
        )
    elif node.kind == "TERM":
        atom = _Q19.atom(node.symbol)
        expected = _WordSummary(
            1, atom, atom, identity, identity, node.symbol, node.symbol, 1
        )
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
            left.first_symbol if left.symbols else right.first_symbol,
            right.last_symbol if right.symbols else left.last_symbol,
            left.runs
            + right.runs
            - int(
                left.last_symbol is not None and left.last_symbol == right.first_symbol
            ),
        )
    elif node.kind == "REPEAT":
        child = root._summaries[node.child]
        if child.symbols == 0:
            expected = _WordSummary(
                0, identity, identity, identity, identity, None, None, 0
            )
        else:
            expected = _WordSummary(
                child.symbols * node.count,
                child.forward.repeat(node.count),
                child.reverse.repeat(node.count),
                child.forward.repeat(node.count - 1).then(child.prefix_forward),
                child.prefix_reverse.then(child.reverse.repeat(node.count - 1)),
                child.first_symbol,
                child.last_symbol,
                child.runs * node.count
                - (node.count - 1 if child.first_symbol == child.last_symbol else 0),
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
    from number_compiler.sequences.reverse_add.border_carry_safety import BorderTile
    from number_compiler.sequences.reverse_add.diagonal_growth_bank import (
        CertifiedDiagonalComparison,
    )
    from number_compiler.sequences.reverse_add.q19_border_control import (
        CertifiedBorderGrowth,
    )
    from number_compiler.sequences.reverse_add.q19_controlled_gt_bank import (
        SourceGuardedGTBankAction,
    )
    from number_compiler.sequences.reverse_add.q19_occurrence import (
        _occurrence_publication_binding,
    )
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairOutputOccurrence,
        ReversePairQ19OutputOwner,
        _LedgerSLPArena,
    )
    from number_compiler.sequences.reverse_add.q19_spatial_bank_morphism import (
        ReverseAddSpatialBankMorphism,
    )
    from number_compiler.sequences.reverse_add.q19_word_summary import (
        _Q19,
        _FrozenPairStepLaw,
        _WordSummary,
    )
    from number_compiler.sequences.reverse_add.temporal_ring_harmonics import (
        ReverseAddTemporalRingBank,
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
            and len(root._binding) == 13
            and root._binding[0] is ledger
            and root._binding[1] is root._digits
            and root._binding[2] == 10
            and root._binding[3] is root._authority
            and root._binding[4] is arena
            and root._binding[5] is root.projector
            and root._binding[6] is root.machine
            and root._binding[7] is root._border_certificates
            and root._binding[8] is root._controlled_gt_banks
            and root._binding[9] is root._issuance_registry
            and root._binding[10] is root._spatial_bank_windows
            and root._binding[11] is root._temporal_ring_banks
            and root._binding[12] is root._diagonal_comparisons
            and root._issuance_registry.diagonal_comparisons
            is root._diagonal_comparisons
            and root._issuance_registry.diagonal_comparison_next
            == len(root._diagonal_comparisons)
            and root._issuance_registry.spatial_bank_windows
            is root._spatial_bank_windows
            and root._issuance_registry.spatial_bank_window_next
            == len(root._spatial_bank_windows)
            and root._issuance_registry.temporal_ring_banks is root._temporal_ring_banks
            and root._issuance_registry.temporal_ring_bank_next
            == len(root._temporal_ring_banks)
        )
        stores = (
            (arena.nodes, arena.owners[0], "reverse_pair_output_grammar"),
            (arena._term, arena.owners[1], "reverse_pair_output_interner"),
            (arena._cat, arena.owners[2], "reverse_pair_output_interner"),
            (arena._rep, arena.owners[3], "reverse_pair_output_interner"),
            (root._summaries, root._summary_owner, "reverse_pair_q19_summary"),
            (root._issued, owner, "reverse_pair_output_occurrence"),
            (
                root._border_certificates,
                root._border_certificates_owner,
                "reverse_pair_q19_border_certificate",
            ),
            (
                root._controlled_gt_banks,
                root._controlled_gt_banks_owner,
                "reverse_pair_q19_conditional_gt_bank",
            ),
            (
                root._spatial_bank_windows,
                root._spatial_bank_windows_owner,
                "reverse_pair_q19_spatial_bank_window",
            ),
            (
                root._temporal_ring_banks,
                root._temporal_ring_banks_owner,
                "reverse_pair_q19_temporal_ring_bank",
            ),
            (
                root._diagonal_comparisons,
                root._diagonal_comparisons_owner,
                "reverse_pair_q19_directed_diagonal_comparison",
            ),
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
        owners = {store_owner for _, store_owner, _ in stores}
        inventory: dict[int, ResourceInventory] = {}
        for store_owner in owners:
            try:
                inventory[store_owner] = ledger.inventory_owner(store_owner)
            except (IndexError, TypeError, ValueError):
                continue
        root_containers = {
            store_owner: containers.get(store_owner) for store_owner in owners
        }
        ledger.bump(
            _reverse_add_keys.REVERSE_PAIR_OUTPUT_AUDIT_ENTRIES,
            sum(len(store) for store, _, _ in stores if isinstance(store, Sized)),
        )
        valid &= all(
            _store_shape(ledger, root_containers, inventory, *item) for item in stores
        )
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
                type(symbol_key) is int
                and type(index) is int
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
                valid &= (
                    type(node_key) is tuple
                    and all(type(part) is int for part in node_key)
                    and node.kind == kind
                    and node_key == expected
                )
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
            valid &= occurrence._publication_binding == (
                _occurrence_publication_binding(occurrence)
            )
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
                and type(occurrence_key) is tuple
                and all(type(part) is int for part in occurrence_key)
                and occurrence_key == (occurrence.root, occurrence.temporal_steps)
                and 0 <= occurrence.root < size
                and occurrence.root in root._summaries
                and occurrence.output_width
                == occurrence.pair_width + int(occurrence.q19_domain == 1)
                and occurrence.growth == occurrence.output_width - len(root._digits)
                and 0 <= occurrence.growth <= occurrence.temporal_steps
            )
        for certificate_key, border_issued in root._border_certificates.items():
            recognized.update((id(certificate_key), id(border_issued)))
            if type(border_issued) is not tuple or len(border_issued) != 2:
                valid = False
                invalid.add((root._border_certificates_owner, id(border_issued)))
                continue
            certificate, certificate_binding = border_issued
            recognized.update((id(certificate), id(certificate_binding)))
            if type(certificate) is not CertifiedBorderGrowth:
                valid = False
                invalid.add((root._border_certificates_owner, id(certificate)))
                continue
            certificate_valid = (
                type(certificate_binding) is tuple
                and certificate_binding == certificate._snapshot()
                and type(certificate_key) is tuple
                and certificate_key
                == (
                    certificate.source.root,
                    certificate.source.temporal_steps,
                    len(certificate.growth_word),
                    certificate.window_digits,
                )
                and certificate.owner is root
                and certificate.source.owner is root._authority
                and root._issued.get(
                    (certificate.source.root, certificate.source.temporal_steps)
                )
                is certificate.source
                and type(certificate.growth_word) is tuple
                and all(
                    type(bit) is int and bit in (0, 1)
                    for bit in certificate.growth_word
                )
                and type(certificate.max_visited_states) is int
                and certificate.max_visited_states >= 1
                and type(certificate.source_pair_inspections) is int
                and certificate.source_pair_inspections >= 0
                and type(certificate.outer_pairs) is tuple
                and (
                    not certificate.outer_pairs
                    or len(certificate.outer_pairs) == len(certificate.growth_word) + 1
                )
                and all(
                    pair is None
                    or (
                        type(pair) is tuple
                        and len(pair) == 2
                        and type(pair[0]) is int
                        and type(pair[1]) is int
                        and 1 <= pair[0] <= 9
                        and 0 <= pair[1] <= 9
                    )
                    for pair in certificate.outer_pairs
                )
                and type(certificate.window_tiles) is tuple
                and (
                    not certificate.window_tiles
                    or len(certificate.window_tiles) == len(certificate.growth_word) + 1
                )
                and all(
                    tile is None
                    or (
                        type(tile) is BorderTile and tile.k == certificate.window_digits
                    )
                    for tile in certificate.window_tiles
                )
            )
            if certificate_valid:
                try:
                    certificate.validate(root, certificate.source)
                except (AttributeError, TypeError, ValueError):
                    certificate_valid = False
            valid &= certificate_valid
            if not certificate_valid:
                invalid.add((root._border_certificates_owner, id(certificate)))
        for action_key, bank_issued in root._controlled_gt_banks.items():
            recognized.update((id(action_key), id(bank_issued)))
            if type(bank_issued) is not tuple or len(bank_issued) != 2:
                valid = False
                invalid.add((root._controlled_gt_banks_owner, id(bank_issued)))
                continue
            bank_action, action_binding = bank_issued
            recognized.update((id(bank_action), id(action_binding)))
            if type(bank_action) is not SourceGuardedGTBankAction:
                valid = False
                invalid.add((root._controlled_gt_banks_owner, id(bank_action)))
                continue
            action_valid = (
                type(action_binding) is tuple
                and action_binding == bank_action._snapshot()
                and type(action_key) is int
                and action_key == bank_action._registry_key
                and bank_action.owner is root
                and bank_action.source.owner is root._authority
                and root._issued.get(
                    (bank_action.source.root, bank_action.source.temporal_steps)
                )
                is bank_action.source
                and type(bank_action.period) is tuple
                and bool(bank_action.period)
                and all(
                    type(value) is int and 0 <= value <= 18
                    for value in bank_action.period
                )
                and type(bank_action.growth_control) is tuple
                and type(bank_action.steps) is int
                and bank_action.steps >= 1
                and bank_action.coordinate >= 0
            )
            if action_valid:
                try:
                    bank_action._validate()
                except (AttributeError, TypeError, ValueError):
                    action_valid = False
            valid &= action_valid
            if not action_valid:
                invalid.add((root._controlled_gt_banks_owner, id(bank_action)))
        for window_key, window_issued in root._spatial_bank_windows.items():
            recognized.update((id(window_key), id(window_issued)))
            if type(window_issued) is not tuple or len(window_issued) != 2:
                valid = False
                invalid.add((root._spatial_bank_windows_owner, id(window_issued)))
                continue
            window, window_binding = window_issued
            recognized.update((id(window), id(window_binding)))
            if type(window) is not ReverseAddSpatialBankMorphism:
                valid = False
                invalid.add((root._spatial_bank_windows_owner, id(window)))
                continue
            window_valid = (
                type(window_binding) is tuple
                and window_binding == window._snapshot()
                and type(window_key) is int
                and window_key == window._registry_key
                and window.action.owner is root
                and window.action.source.owner is root._authority
                and root._controlled_gt_banks.get(window.action._registry_key)
                is not None
            )
            if window_valid:
                try:
                    window._validate()
                except (AttributeError, TypeError, ValueError):
                    window_valid = False
            valid &= window_valid
            if not window_valid:
                invalid.add((root._spatial_bank_windows_owner, id(window)))
        for ring_key, ring_issued in root._temporal_ring_banks.items():
            recognized.update((id(ring_key), id(ring_issued)))
            if type(ring_issued) is not tuple or len(ring_issued) != 2:
                valid = False
                invalid.add((root._temporal_ring_banks_owner, id(ring_issued)))
                continue
            ring, ring_binding = ring_issued
            recognized.update((id(ring), id(ring_binding)))
            if type(ring) is not ReverseAddTemporalRingBank:
                valid = False
                invalid.add((root._temporal_ring_banks_owner, id(ring)))
                continue
            try:
                ring_valid = (
                    type(ring_binding) is tuple
                    and ring_binding == ring._snapshot()
                    and type(ring_key) is int
                    and ring_key == ring._registry_key
                    and ring.certificate.owner is root
                    and ring.certificate.source.owner is root._authority
                    and root._border_certificates.get(
                        (
                            ring.certificate.source.root,
                            ring.certificate.source.temporal_steps,
                            len(ring.certificate.growth_word),
                            ring.certificate.window_digits,
                        )
                    )
                    is not None
                )
                if ring_valid:
                    ring._check()
            except (AttributeError, IndexError, TypeError, ValueError):
                ring_valid = False
            valid &= ring_valid
            if not ring_valid:
                invalid.add((root._temporal_ring_banks_owner, id(ring)))
        for diagonal_key, diagonal_issued in root._diagonal_comparisons.items():
            recognized.update((id(diagonal_key), id(diagonal_issued)))
            if type(diagonal_issued) is not tuple or len(diagonal_issued) != 2:
                valid = False
                invalid.add((root._diagonal_comparisons_owner, id(diagonal_issued)))
                continue
            comparison, comparison_binding = diagonal_issued
            recognized.update((id(comparison), id(comparison_binding)))
            if type(comparison) is not CertifiedDiagonalComparison:
                valid = False
                invalid.add((root._diagonal_comparisons_owner, id(comparison)))
                continue
            try:
                comparison_valid = (
                    type(comparison_binding) is tuple
                    and comparison_binding == comparison._snapshot()
                    and type(diagonal_key) is int
                    and diagonal_key == comparison._registry_key
                    and comparison.certificate.owner is root
                    and comparison.certificate.source.owner is root._authority
                    and root._issued.get(
                        (
                            comparison.certificate.source.root,
                            comparison.certificate.source.temporal_steps,
                        )
                    )
                    is comparison.certificate.source
                    and root._border_certificates.get(
                        (
                            comparison.certificate.source.root,
                            comparison.certificate.source.temporal_steps,
                            len(comparison.certificate.growth_word),
                            comparison.certificate.window_digits,
                        )
                    )
                    is not None
                )
                if comparison_valid:
                    comparison._validate()
            except (AttributeError, IndexError, TypeError, ValueError):
                comparison_valid = False
            valid &= comparison_valid
            if not comparison_valid:
                invalid.add((root._diagonal_comparisons_owner, id(comparison)))
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
            approved.update(
                (id(root), id(arena), id(root.projector), id(root._issuance_registry))
            )
            approved.update(id(node) for node in arena.nodes)
            approved.update(id(store) for store, _, _ in stores)
            approved.update(
                id(store._data) for store, _, _ in stores if type(store) is OwnedMemo
            )
            for retained_store, _, _ in stores:
                if isinstance(retained_store, Mapping):
                    # Keys and scalar results are independently checked local
                    # indices/ports above. Approve those exact store members,
                    # not an opaque container that could hide unchecked data.
                    approved.update(
                        id(value) for pair in retained_store.items() for value in pair
                    )
            approved.update(id(summary) for summary in root._summaries.values())
            approved.update(id(occurrence) for occurrence in root._issued.values())
            for retained_issue in chain(
                root._border_certificates.values(),
                root._controlled_gt_banks.values(),
                root._spatial_bank_windows.values(),
                root._temporal_ring_banks.values(),
                root._diagonal_comparisons.values(),
            ):
                if type(retained_issue) is tuple and len(retained_issue) == 2:
                    retained_record, retained_binding = retained_issue
                    approved.update(
                        (id(retained_issue), id(retained_record), id(retained_binding))
                    )
                    approved.update(id(value) for value in retained_binding)
        else:
            invalid.add((owner, id(root)))
    return approved, recognized, invalid


def audit_reverse_pair_output_owner(
    ledger: object, root: object
) -> PayloadAuditContribution:
    """Return only Q19 audit evidence that is a direct member of bound stores."""
    if type(ledger) is not ResourceLedger:
        raise TypeError("Q19 payload audit requires its resource ledger")
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )

    if type(root) is not ReversePairQ19OutputOwner:
        return PayloadAuditContribution()
    owners = (
        *root.arena.owners,
        root._summary_owner,
        root._issued_owner,
        root._border_certificates_owner,
        root._controlled_gt_banks_owner,
        root._spatial_bank_windows_owner,
        root._temporal_ring_banks_owner,
        root._diagonal_comparisons_owner,
        *root._projector_owners,
    )
    containers: dict[int, object] = {}
    for owner in owners:
        try:
            containers[owner] = ledger.registered_container(owner)
        except (IndexError, RuntimeError, TypeError, ValueError):
            continue
    approved_ids, _recognized, invalid_rows = audit_reverse_pair_output_roots(
        ledger, (root,), containers
    )
    bindings = (
        ("_audit_nodes", "reverse_pair_output_grammar", root.arena.owners[0]),
        ("_audit_terms", "reverse_pair_output_interner", root.arena.owners[1]),
        ("_audit_concats", "reverse_pair_output_interner", root.arena.owners[2]),
        ("_audit_repeats", "reverse_pair_output_interner", root.arena.owners[3]),
        ("_audit_summaries", "reverse_pair_q19_summary", root._summary_owner),
        (
            "_audit_issued",
            "reverse_pair_output_occurrence",
            root._issued_owner,
        ),
        (
            "_audit_border_certificates",
            "reverse_pair_q19_border_certificate",
            root._border_certificates_owner,
        ),
        (
            "_audit_controlled_gt_banks",
            "reverse_pair_q19_conditional_gt_bank",
            root._controlled_gt_banks_owner,
        ),
        (
            "_audit_spatial_bank_windows",
            "reverse_pair_q19_spatial_bank_window",
            root._spatial_bank_windows_owner,
        ),
        (
            "_audit_temporal_ring_banks",
            "reverse_pair_q19_temporal_ring_bank",
            root._temporal_ring_banks_owner,
        ),
        (
            "_audit_diagonal_comparisons",
            "reverse_pair_q19_directed_diagonal_comparison",
            root._diagonal_comparisons_owner,
        ),
        *(
            (attribute, "reverse_pair_projector_memo", owner)
            for attribute, owner in zip(
                (
                    "_audit_projector_forward",
                    "_audit_projector_reverse",
                    "_audit_projector_block",
                    "_audit_projector_forward_power",
                    "_audit_projector_reverse_power",
                ),
                root._projector_owners,
                strict=True,
            )
        ),
    )
    approved: list[PayloadAuditEntry] = []
    invalid: list[PayloadAuditEntry] = []
    for attribute, _role, owner in bindings:
        store = getattr(root, attribute)
        memo_attribute = {
            "_audit_border_certificates": "_border_certificates",
            "_audit_controlled_gt_banks": "_controlled_gt_banks",
            "_audit_spatial_bank_windows": "_spatial_bank_windows",
            "_audit_temporal_ring_banks": "_temporal_ring_banks",
            "_audit_diagonal_comparisons": "_diagonal_comparisons",
        }.get(attribute)
        if memo_attribute is not None:
            memo = getattr(root, memo_attribute)
            if type(memo) is OwnedMemo and memo._data is store:
                # The contract binds the exact backing map, but OwnedMemo's
                # public items view unwraps its accounting envelope. The
                # contract index explicitly recognizes that semantic value as
                # the memo's retained payload after this family audit validates
                # its exact certificate/action and the wrapper's node cost.
                store = memo
        values: tuple[object, ...]
        if isinstance(store, Mapping):
            values = tuple(item for pair in store.items() for item in pair)
        elif isinstance(store, Sequence) and not isinstance(
            store, (str, bytes, bytearray)
        ):
            values = tuple(store)
        else:
            values = ()
        approved.extend(
            PayloadAuditEntry(owner, value)
            for value in values
            if id(value) in approved_ids
        )
        invalid.extend(
            PayloadAuditEntry(owner, value)
            for value in values
            if (owner, id(value)) in invalid_rows
        )
    if invalid_rows and not invalid:
        # A failed binding is reported against the exact issued-store owner;
        # the contract layer permits the root itself only as invalid evidence.
        invalid.append(PayloadAuditEntry(root._issued_owner, root))
    return PayloadAuditContribution(tuple(approved), tuple(invalid))

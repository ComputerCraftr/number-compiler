"""Independent shape/ownership checks for completed decimal pair grammars."""

from __future__ import annotations

from collections.abc import Iterator, Mapping, Sequence
from itertools import chain
from typing import TypeGuard, TypeVar, cast

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp import SLPNode
from number_compiler.arithmetic.contracts.input_validation import (
    is_exact_object_tuple,
    object_mapping,
)
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import (
    OwnedMemo,
    ResourceInventory,
    ResourceLedger,
)
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys
from number_compiler.resources.owned_memo import (
    DynamicMemoValue,
    OwnedMemoAuditSnapshot,
)
from number_compiler.resources.stores import LedgerDict, LedgerList
from number_compiler.sequences.reverse_add.q19_summary_audit import (
    occurrence_summary,
    summary_matches,
)

_MemoKey = TypeVar("_MemoKey")
_MemoValue = TypeVar("_MemoValue")


def _object_memo_snapshot(
    value: object,
) -> OwnedMemoAuditSnapshot[object, object] | None:
    """Erase memo generics only at an exact, read-only audit boundary."""
    if type(value) is OwnedMemoAuditSnapshot:
        return cast(OwnedMemoAuditSnapshot[object, object], value)
    if type(value) is not OwnedMemo:
        return None
    memo = cast(OwnedMemo[object, object], value)
    snapshot: object = memo.audit_snapshot()
    if type(snapshot) is not OwnedMemoAuditSnapshot:
        return None
    return snapshot


def _is_int_triple(value: object) -> TypeGuard[tuple[int, int, int]]:
    if not is_exact_object_tuple(value) or len(value) != 3:
        return False
    return all(type(part) is int for part in value)


def _is_exact_int_tuple(value: object, size: int) -> TypeGuard[tuple[int, ...]]:
    return (
        is_exact_object_tuple(value)
        and len(value) == size
        and all(type(part) is int for part in value)
    )


def _is_object_pair(value: object) -> TypeGuard[tuple[object, object]]:
    return is_exact_object_tuple(value) and len(value) == 2


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
    snapshot = _object_memo_snapshot(store)
    item = inventory.get(owner)
    container_identity: object
    if snapshot is not None:
        container_identity = snapshot.container
        memo_container: Mapping[object, object] = snapshot.container
        if (
            snapshot.ledger is not ledger
            or snapshot.owner != owner
            or snapshot.disposed
        ):
            return False
        if role == "reverse_pair_output_interner":
            nodes = 0
        elif snapshot.dynamic_cost:
            nodes = 0
            for raw_value in memo_container.values():
                wrapped: object = raw_value
                if (
                    type(wrapped) is not DynamicMemoValue
                    or type(wrapped.nodes) is not int
                    or wrapped.nodes < 1
                ):
                    return False
                nodes += wrapped.nodes
            if nodes != snapshot.dynamic_nodes:
                return False
        else:
            nodes = len(memo_container) * snapshot.nodes_per_entry
        entries = len(memo_container)
    elif isinstance(store, (LedgerList, LedgerDict)):
        container_identity = cast(object, store)
        if store.owner != owner or store.ledger is not ledger:
            return False
        if isinstance(store, LedgerList):
            entries = len(cast(Sequence[object], store.audit_view()))
        else:
            entries = len(cast(Mapping[object, object], store.audit_view()))
        nodes = entries * store.nodes_per_entry
    else:
        return False
    return (
        type(item) is ResourceInventory
        and containers.get(owner) is container_identity
        and item.role == role
        and not item.disposed
        and item.payloads_registered
        and item.entries == entries
        and item.observed_entries == entries
        and item.nodes == nodes
    )


def memo_payload_items(
    snapshot: OwnedMemoAuditSnapshot[_MemoKey, _MemoValue],
) -> Iterator[tuple[_MemoKey, object]]:
    """Expose live payloads without hiding malformed dynamic-cost wrappers."""
    view = snapshot.payload_view
    for key in snapshot.container:
        try:
            payload: object = view[key]
            yield key, payload
        except TypeError:
            # The raw value remains visible so the enclosing exact-shape audit
            # can reject malformed wrappers without losing their identity.
            payload = snapshot.container[key]
            yield key, payload


def memo_payload_objects(snapshot: object) -> Iterator[tuple[object, object]]:
    """Erase memo key types only after exact snapshot admission.

    Owner-binding audits inspect heterogeneous backing stores collected in
    ``tuple[object, ...]``.  This boundary preserves the complete key and
    payload objects while keeping the generic runtime internals out of that
    erased inspection surface.
    """
    if type(snapshot) is not OwnedMemoAuditSnapshot:
        raise TypeError("expected an owned-memo audit snapshot")
    object_snapshot = cast(OwnedMemoAuditSnapshot[object, object], snapshot)
    view = object_snapshot.payload_view
    for raw_key in object_snapshot.container:
        key: object = raw_key
        try:
            payload: object = view[raw_key]
        except TypeError:
            # Preserve malformed wrapper visibility for the exact shape check.
            payload = object_snapshot.container[raw_key]
        yield key, payload


def _memo_get(
    snapshot: OwnedMemoAuditSnapshot[_MemoKey, _MemoValue], key: _MemoKey
) -> object:
    if key not in snapshot.container:
        return _MISSING
    try:
        return snapshot.payload_view[key]
    except TypeError:
        return snapshot.container[key]


def _memo_values(
    snapshot: OwnedMemoAuditSnapshot[_MemoKey, _MemoValue],
) -> Iterator[object]:
    for _key, value in memo_payload_items(snapshot):
        yield value


def _audit_mapping_items(
    mapping: Mapping[_MemoKey, object],
) -> tuple[tuple[tuple[_MemoKey, object], ...], bool]:
    """Read a cache audit view and reject malformed dynamic-cost entries."""
    items: list[tuple[_MemoKey, object]] = []
    valid = True
    try:
        for key in mapping:
            try:
                items.append((key, mapping[key]))
            except (KeyError, TypeError, ValueError):
                valid = False
    except (KeyError, RuntimeError, TypeError, ValueError):
        valid = False
    return tuple(items), valid


_MISSING = object()


def _store_length(store: object) -> int:
    snapshot = _object_memo_snapshot(store)
    if snapshot is not None:
        container: Mapping[object, object] = snapshot.container
        return len(container)
    mapping = object_mapping(store)
    if mapping is not None:
        return len(mapping)
    if isinstance(store, Sequence):
        sequence: Sequence[object] = cast(Sequence[object], store)
        return len(sequence)
    return 0


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
        occurrence_publication_snapshot,
    )
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairOutputOccurrence,
        ReversePairQ19OutputOwner,
    )
    from number_compiler.sequences.reverse_add.q19_spatial_bank_morphism import (
        ReverseAddSpatialBankMorphism,
    )
    from number_compiler.sequences.reverse_add.q19_word_summary import (
        FrozenPairStepLaw,
        Q19Summary,
        WordSummary,
    )
    from number_compiler.sequences.reverse_add.temporal_ring_harmonics import (
        ReverseAddTemporalRingBank,
    )

    approved: set[int] = set()
    recognized: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    for root in roots:
        if type(root) is not ReversePairQ19OutputOwner:
            continue
        state = root.audit_snapshot()
        if state.disposed:
            continue
        recognized.add(id(root))
        arena = state.arena
        owner = state.issued_owner
        expected_audit_bindings = (
            arena.nodes,
            *arena.audit_interner_stores,
            state.summaries.container,
            state.issued.container,
            state.word_fibers.container,
            state.border_certificates.container,
            state.controlled_gt_banks.container,
            state.spatial_bank_windows.container,
            state.temporal_ring_banks.container,
            state.diagonal_comparisons.container,
            state.projector_forward.container,
            state.projector_reverse.container,
            state.projector_block.container,
            state.projector_forward_power.container,
            state.projector_reverse_power.container,
        )
        valid = (
            state.ledger is ledger
            and not state.disposed
            and type(arena) is LedgerSLPArena
            and arena.ledger is ledger
            and state.projector.arena is arena
            and state.projector.machine is state.machine
            and state.base == 10
            and state.machine.base == 10
            and type(state.machine) is FrozenPairStepLaw
            and type(state.binding) is tuple
            and len(state.binding) == 14
            and state.binding[0] is ledger
            and state.binding[1] is state.digits
            and state.binding[2] == 10
            and state.binding[3] is state.authority
            and state.binding[4] is arena
            and state.binding[5] is state.projector
            and state.binding[6] is state.machine
            and state.binding[7] is state.border_certificates_binding
            and state.binding[8] is state.controlled_gt_banks_binding
            and state.binding[9] is state.issuance_registry
            and state.binding[10] is state.spatial_bank_windows_binding
            and state.binding[11] is state.temporal_ring_banks_binding
            and state.binding[12] is state.diagonal_comparisons_binding
            and state.binding[13] is state.word_fibers_binding
            and type(state.audit_bindings) is tuple
            and len(state.audit_bindings) == len(expected_audit_bindings)
            and all(
                actual is expected
                for actual, expected in zip(
                    state.audit_bindings, expected_audit_bindings, strict=True
                )
            )
            and state.projector.has_exact_owned_cache_binding(
                forward=state.projector_forward.container,
                reverse=state.projector_reverse.container,
                block=state.projector_block.container,
                forward_power=state.projector_forward_power.container,
                reverse_power=state.projector_reverse_power.container,
            )
            and state.issuance_registry.diagonal_comparisons
            is state.diagonal_comparisons_binding
            and state.issuance_registry.diagonal_comparison_next
            == len(state.diagonal_comparisons.container)
            and state.issuance_registry.spatial_bank_windows
            is state.spatial_bank_windows_binding
            and state.issuance_registry.spatial_bank_window_next
            == len(state.spatial_bank_windows.container)
            and state.issuance_registry.temporal_ring_banks
            is state.temporal_ring_banks_binding
            and state.issuance_registry.temporal_ring_bank_next
            == len(state.temporal_ring_banks.container)
        )
        stores = (
            (arena.nodes, arena.owners[0], "reverse_pair_output_grammar"),
            (
                arena.audit_interner_stores[0],
                arena.owners[1],
                "reverse_pair_output_interner",
            ),
            (
                arena.audit_interner_stores[1],
                arena.owners[2],
                "reverse_pair_output_interner",
            ),
            (
                arena.audit_interner_stores[2],
                arena.owners[3],
                "reverse_pair_output_interner",
            ),
            (state.summaries, state.summary_owner, "reverse_pair_q19_summary"),
            (state.issued, owner, "reverse_pair_output_occurrence"),
            (
                state.word_fibers,
                state.word_fibers_owner,
                "observation_memo",
            ),
            (
                state.border_certificates,
                state.border_certificates_owner,
                "reverse_pair_q19_border_certificate",
            ),
            (
                state.controlled_gt_banks,
                state.controlled_gt_banks_owner,
                "reverse_pair_q19_conditional_gt_bank",
            ),
            (
                state.spatial_bank_windows,
                state.spatial_bank_windows_owner,
                "reverse_pair_q19_spatial_bank_window",
            ),
            (
                state.temporal_ring_banks,
                state.temporal_ring_banks_owner,
                "reverse_pair_q19_temporal_ring_bank",
            ),
            (
                state.diagonal_comparisons,
                state.diagonal_comparisons_owner,
                "reverse_pair_q19_directed_diagonal_comparison",
            ),
            *(
                (store, store_owner, "reverse_pair_projector_memo")
                for store, store_owner in zip(
                    (
                        state.projector_forward,
                        state.projector_reverse,
                        state.projector_block,
                        state.projector_forward_power,
                        state.projector_reverse_power,
                    ),
                    state.projector_owners,
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
            sum(_store_length(store) for store, _, _ in stores),
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
        term_store, concat_store, repeat_store = arena.audit_interner_stores
        for symbol_key, index in term_store.items():
            valid &= (
                type(symbol_key) is int
                and type(index) is int
                and 0 <= index < size
                and arena.nodes[index].kind == "TERM"
                and arena.nodes[index].symbol == symbol_key
            )
        for interner, kind in ((concat_store, "CONCAT"), (repeat_store, "REPEAT")):
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
                    is_exact_object_tuple(node_key)
                    and all(type(part) is int for part in node_key)
                    and node.kind == kind
                    and node_key == expected
                )
        for index, summary in memo_payload_items(state.summaries):
            if type(index) is not int or not 0 <= index < size:
                valid = False
                continue
            if type(summary) is not WordSummary:
                valid = False
                continue
            for folded in (
                summary.forward,
                summary.reverse,
                summary.prefix_forward,
                summary.prefix_reverse,
            ):
                valid &= (
                    type(folded) is Q19Summary
                    and type(folded.length) is int
                    and folded.length >= 0
                    and type(folded.domain) is int
                    and folded.domain in (-1, 0, 1)
                    and type(folded.f9) is int
                    and 0 <= folded.f9 < 9
                )
            valid &= summary.symbols == summary.forward.length == summary.reverse.length
            try:
                valid &= summary_matches(root, index)
            except (KeyError, IndexError, TypeError, ValueError, AttributeError):
                valid = False
        for occurrence_key, occurrence in memo_payload_items(state.issued):
            recognized.add(id(occurrence))
            if type(occurrence) is not ReversePairOutputOccurrence:
                valid = False
                continue
            try:
                occurrence.__post_init__()
            except (TypeError, ValueError):
                valid = False
                continue
            valid &= occurrence.publication_binding == occurrence_publication_snapshot(
                occurrence
            )
            try:
                valid &= occurrence_summary(root, occurrence.root) == (
                    occurrence.pair_width,
                    occurrence.q19_domain,
                    occurrence.q19_f9,
                )
            except (KeyError, IndexError, TypeError, ValueError, AttributeError):
                valid = False
            valid &= (
                occurrence.owner is state.authority
                and is_exact_object_tuple(occurrence_key)
                and all(type(part) is int for part in occurrence_key)
                and occurrence_key == (occurrence.root, occurrence.temporal_steps)
                and 0 <= occurrence.root < size
                and occurrence.root in state.summaries.container
                and occurrence.output_width
                == occurrence.pair_width + int(occurrence.q19_domain == 1)
                and occurrence.growth == occurrence.output_width - len(state.digits)
                and 0 <= occurrence.growth <= occurrence.temporal_steps
            )
        from number_compiler.sequences.reverse_add.temporal_seed_morphism import (
            Q19WordFiber,
        )

        checked_seeds: dict[int, bool] = {}
        for fiber_key, cached in memo_payload_items(state.word_fibers):
            recognized.update((id(fiber_key), id(cached)))
            if not _is_int_triple(fiber_key):
                valid = False
                invalid.add((state.word_fibers_owner, id(cached)))
                continue
            fiber_root, fiber_steps, seed = fiber_key
            if not _is_object_pair(cached):
                valid = False
                invalid.add((state.word_fibers_owner, id(cached)))
                continue
            fiber_value, fiber_binding_value = cached
            if type(fiber_value) is not Q19WordFiber or not is_exact_object_tuple(
                fiber_binding_value
            ):
                valid = False
                invalid.add((state.word_fibers_owner, id(cached)))
                continue
            fiber = fiber_value
            fiber_binding = fiber_binding_value
            recognized.update((id(fiber), id(fiber_binding)))
            occurrence = fiber.occurrence
            if seed not in checked_seeds:
                checked_seeds[seed] = seed >= 0 and digits_lsd(seed, 10) == state.digits
            fiber_valid = (
                fiber_binding == fiber.audit_binding()
                and type(occurrence) is ReversePairOutputOccurrence
                and (fiber_root, fiber_steps)
                == (occurrence.root, occurrence.temporal_steps)
                and seed >= 0
                and checked_seeds[seed]
                and _memo_get(
                    state.issued, (occurrence.root, occurrence.temporal_steps)
                )
                is occurrence
                and fiber.generation == occurrence.temporal_steps
                and fiber.root == occurrence.root
                and fiber.width == occurrence.output_width
                and fiber.pair_width == occurrence.pair_width
                and type(fiber.center) is tuple
                and len(fiber.center) == (1 if fiber.width & 1 else 2)
                and all(
                    type(digit) is int and 0 <= digit <= 9 for digit in fiber.center
                )
                and type(fiber.residue99) is int
                and 0 <= fiber.residue99 < 99
                and type(fiber.residue198) is int
                and 0 <= fiber.residue198 < 198
                and type(fiber.exterior99) is int
                and 0 <= fiber.exterior99 < 99
                and type(fiber.exterior198) is int
                and 0 <= fiber.exterior198 < 198
                and type(fiber.middle_carry_map) is tuple
                and fiber.middle_carry_map in ((0, 0), (0, 1), (1, 1))
            )
            valid &= fiber_valid
            if fiber_valid:
                approved.update(
                    (id(fiber_key), id(cached), id(fiber), id(fiber_binding))
                )
                approved.update(id(value) for value in fiber.audit_binding())
            else:
                invalid.add((state.word_fibers_owner, id(fiber)))
        for certificate_key, border_issued in memo_payload_items(
            state.border_certificates
        ):
            recognized.update((id(certificate_key), id(border_issued)))
            if not _is_object_pair(border_issued):
                valid = False
                invalid.add((state.border_certificates_owner, id(border_issued)))
                continue
            certificate, certificate_binding = border_issued
            recognized.update((id(certificate), id(certificate_binding)))
            if type(certificate) is not CertifiedBorderGrowth:
                valid = False
                invalid.add((state.border_certificates_owner, id(certificate)))
                continue
            certificate_valid = (
                type(certificate_binding) is tuple
                and certificate_binding == certificate.publication_snapshot()
                and type(certificate_key) is tuple
                and certificate_key
                == (
                    certificate.source.root,
                    certificate.source.temporal_steps,
                    len(certificate.growth_word),
                    certificate.window_digits,
                )
                and certificate.owner is root
                and certificate.source.owner is state.authority
                and _memo_get(
                    state.issued,
                    ((certificate.source.root, certificate.source.temporal_steps)),
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
                invalid.add((state.border_certificates_owner, id(certificate)))
        for action_key, bank_issued in memo_payload_items(state.controlled_gt_banks):
            recognized.update((id(action_key), id(bank_issued)))
            if not _is_object_pair(bank_issued):
                valid = False
                invalid.add((state.controlled_gt_banks_owner, id(bank_issued)))
                continue
            bank_action, action_binding = bank_issued
            recognized.update((id(bank_action), id(action_binding)))
            if type(bank_action) is not SourceGuardedGTBankAction:
                valid = False
                invalid.add((state.controlled_gt_banks_owner, id(bank_action)))
                continue
            action_valid = (
                type(action_binding) is tuple
                and action_binding == bank_action.publication_snapshot()
                and type(action_key) is int
                and action_key == bank_action.registry_key
                and bank_action.owner is root
                and bank_action.source.owner is state.authority
                and _memo_get(
                    state.issued,
                    ((bank_action.source.root, bank_action.source.temporal_steps)),
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
                    bank_action.validate_source_authority()
                except (AttributeError, TypeError, ValueError):
                    action_valid = False
            valid &= action_valid
            if not action_valid:
                invalid.add((state.controlled_gt_banks_owner, id(bank_action)))
        for window_key, window_issued in memo_payload_items(state.spatial_bank_windows):
            recognized.update((id(window_key), id(window_issued)))
            if not _is_object_pair(window_issued):
                valid = False
                invalid.add((state.spatial_bank_windows_owner, id(window_issued)))
                continue
            window, window_binding = window_issued
            recognized.update((id(window), id(window_binding)))
            if type(window) is not ReverseAddSpatialBankMorphism:
                valid = False
                invalid.add((state.spatial_bank_windows_owner, id(window)))
                continue
            window_valid = (
                type(window_binding) is tuple
                and window_binding == window.publication_snapshot()
                and type(window_key) is int
                and window_key == window.registry_key
                and window.action.owner is root
                and window.action.source.owner is state.authority
                and _memo_get(state.controlled_gt_banks, window.action.registry_key)
                is not None
            )
            if window_valid:
                try:
                    window.validate_source_authority()
                except (AttributeError, TypeError, ValueError):
                    window_valid = False
            valid &= window_valid
            if not window_valid:
                invalid.add((state.spatial_bank_windows_owner, id(window)))
        for ring_key, ring_issued in memo_payload_items(state.temporal_ring_banks):
            recognized.update((id(ring_key), id(ring_issued)))
            if not _is_object_pair(ring_issued):
                valid = False
                invalid.add((state.temporal_ring_banks_owner, id(ring_issued)))
                continue
            ring, ring_binding = ring_issued
            recognized.update((id(ring), id(ring_binding)))
            if type(ring) is not ReverseAddTemporalRingBank:
                valid = False
                invalid.add((state.temporal_ring_banks_owner, id(ring)))
                continue
            try:
                ring_valid = (
                    type(ring_binding) is tuple
                    and ring_binding == ring.publication_snapshot()
                    and type(ring_key) is int
                    and ring_key == ring.registry_key
                    and ring.certificate.owner is root
                    and ring.certificate.source.owner is state.authority
                    and _memo_get(
                        state.border_certificates,
                        (
                            (
                                ring.certificate.source.root,
                                ring.certificate.source.temporal_steps,
                                len(ring.certificate.growth_word),
                                ring.certificate.window_digits,
                            )
                        ),
                    )
                    is not None
                )
                if ring_valid:
                    ring.validate()
            except (AttributeError, IndexError, TypeError, ValueError):
                ring_valid = False
            valid &= ring_valid
            if not ring_valid:
                invalid.add((state.temporal_ring_banks_owner, id(ring)))
        for diagonal_key, diagonal_issued in memo_payload_items(
            state.diagonal_comparisons
        ):
            recognized.update((id(diagonal_key), id(diagonal_issued)))
            if not _is_object_pair(diagonal_issued):
                valid = False
                invalid.add((state.diagonal_comparisons_owner, id(diagonal_issued)))
                continue
            comparison, comparison_binding = diagonal_issued
            recognized.update((id(comparison), id(comparison_binding)))
            if type(comparison) is not CertifiedDiagonalComparison:
                valid = False
                invalid.add((state.diagonal_comparisons_owner, id(comparison)))
                continue
            try:
                comparison_valid = (
                    type(comparison_binding) is tuple
                    and comparison_binding == comparison.publication_snapshot()
                    and type(diagonal_key) is int
                    and diagonal_key == comparison.registry_key
                    and comparison.certificate.owner is root
                    and comparison.certificate.source.owner is state.authority
                    and _memo_get(
                        state.issued,
                        (
                            (
                                comparison.certificate.source.root,
                                comparison.certificate.source.temporal_steps,
                            )
                        ),
                    )
                    is comparison.certificate.source
                    and _memo_get(
                        state.border_certificates,
                        (
                            (
                                comparison.certificate.source.root,
                                comparison.certificate.source.temporal_steps,
                                len(comparison.certificate.growth_word),
                                comparison.certificate.window_digits,
                            )
                        ),
                    )
                    is not None
                )
                if comparison_valid:
                    comparison.validate_source_authority()
            except (AttributeError, IndexError, TypeError, ValueError):
                comparison_valid = False
            valid &= comparison_valid
            if not comparison_valid:
                invalid.add((state.diagonal_comparisons_owner, id(comparison)))
        left_states, right_states = root.machine.left.states, root.machine.right.states
        forward_entries = _audit_mapping_items(state.projector_cache_stores[0])
        reverse_entries = _audit_mapping_items(state.projector_cache_stores[1])
        forward_power_entries = _audit_mapping_items(state.projector_cache_stores[3])
        reverse_power_entries = _audit_mapping_items(state.projector_cache_stores[4])
        for (entries, entries_valid), states, arity in (
            (forward_entries, left_states, 2),
            (reverse_entries, right_states, 2),
            (forward_power_entries, left_states, 3),
            (reverse_power_entries, right_states, 3),
        ):
            valid &= entries_valid
            for memo_key, result in entries:
                if not _is_exact_int_tuple(memo_key, arity):
                    valid = False
                    continue
                valid &= (
                    0 <= memo_key[0] < size
                    and memo_key[1] in states
                    and (arity == 2 or memo_key[-1] >= 0)
                    and (result is None or type(result) is int and result in states)
                )
        block_entries, block_entries_valid = _audit_mapping_items(
            state.projector_cache_stores[2]
        )
        valid &= block_entries_valid
        for block_key, result in block_entries:
            if not _is_int_triple(block_key):
                valid = False
                continue
            valid &= (
                0 <= block_key[0] < size
                and block_key[1] in left_states
                and block_key[2] in right_states
                and type(result) is int
                and 0 <= result < size
            )
        if valid:
            approved.update(
                (id(root), id(arena), id(state.projector), id(state.issuance_registry))
            )
            approved.update(id(node) for node in arena.nodes)
            approved.update(id(store) for store, _, _ in stores)
            approved.update(
                id(store.container)
                for store, _, _ in stores
                if type(store) is OwnedMemoAuditSnapshot
            )
            for retained_store, _, _ in stores:
                if type(retained_store) is OwnedMemoAuditSnapshot:
                    retained_mapping = retained_store.container
                elif isinstance(retained_store, Mapping):
                    retained_mapping = retained_store
                else:
                    retained_mapping = None
                if retained_mapping is not None:
                    # Keys and scalar results are independently checked local
                    # indices/ports above. Approve those exact store members,
                    # not an opaque container that could hide unchecked data.
                    approved.update(
                        id(value) for pair in retained_mapping.items() for value in pair
                    )
            approved.update(id(summary) for summary in _memo_values(state.summaries))
            approved.update(id(occurrence) for occurrence in _memo_values(state.issued))
            for retained_issue in chain(
                _memo_values(state.border_certificates),
                _memo_values(state.controlled_gt_banks),
                _memo_values(state.spatial_bank_windows),
                _memo_values(state.temporal_ring_banks),
                _memo_values(state.diagonal_comparisons),
                _memo_values(state.word_fibers),
            ):
                if _is_object_pair(retained_issue):
                    retained_record, retained_binding = retained_issue
                    approved.update(
                        (id(retained_issue), id(retained_record), id(retained_binding))
                    )
                    if is_exact_object_tuple(retained_binding):
                        approved.update(id(value) for value in retained_binding)
        else:
            invalid.add((owner, id(root)))
    return approved, recognized, invalid

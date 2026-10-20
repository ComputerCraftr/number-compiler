"""Read-only payload validation for source-free symbolic innovation DAGs."""

from __future__ import annotations

from collections.abc import Sequence
from typing import TYPE_CHECKING, cast

from number_compiler.arithmetic.contracts.input_validation import (
    is_exact_object_tuple,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.physical_support_payload_audit import (
    PhysicalSupportPayloadAudit,
)

if TYPE_CHECKING:
    from number_compiler.arithmetic.fields.symbolic_innovation import (
        SymbolicInnovationArena,
    )
    from number_compiler.resources.field_image_audit_contracts import (
        SymbolicInnovationAuditSnapshot,
    )


def audit_symbolic_innovation_payloads(
    ledger: ResourceLedger,
) -> PhysicalSupportPayloadAudit:
    """Authenticate exact arena stores, handles, and local normal-form nodes."""
    if not any(
        type(root).__module__ == "number_compiler.arithmetic.fields.symbolic_innovation"
        for root in ledger.iter_execution_roots()
    ):
        return PhysicalSupportPayloadAudit(frozenset(), frozenset())

    from number_compiler.arithmetic.fields.symbolic_innovation import (
        SymbolicInnovationArena,
    )
    from number_compiler.resources.stores import LedgerDict, LedgerList

    containers = dict(ledger.iter_containers())
    inventory = {row.owner: row for row in ledger.inventory()}
    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    for root in ledger.iter_execution_roots():
        if type(root) is not SymbolicInnovationArena:
            continue
        try:
            snapshot = root.audit_snapshot()
            projection = snapshot.projection
            projection_snapshot = projection.audit_snapshot()
            nodes_object: object = snapshot.nodes
            keys_object: object = snapshot.keys
            projection_store_object: object = projection_snapshot.container
            owners = snapshot.node_owner, snapshot.key_owner, projection.owner
        except AttributeError:
            invalid.add((-1, id(root)))
            continue
        if any(type(owner) is not int for owner in owners):
            invalid.add((-1, id(root)))
            continue
        if (
            type(nodes_object) is not LedgerList
            or type(keys_object) is not LedgerDict
            or type(projection_store_object) is not LedgerDict
        ):
            invalid.update((owner, id(root)) for owner in owners)
            continue
        nodes = cast(LedgerList[object], nodes_object)
        keys = cast(LedgerDict[object, object], keys_object)
        projection_store = cast(LedgerDict[object, object], projection_store_object)
        node_owner, key_owner, projection_owner = owners
        node_row = inventory.get(node_owner)
        key_row = inventory.get(key_owner)
        projection_row = inventory.get(projection_owner)
        root_approved = {
            id(nodes),
            id(keys),
            id(projection_store),
        }
        valid = (
            root.ledger is ledger
            and type(snapshot.closed) is bool
            and set(vars(root))
            == {
                "ledger",
                "owner",
                "_closed",
                "_node_owner",
                "_key_owner",
                "_projection",
                "_f5_compositions",
                "_f5_composition_owner",
                "_nodes",
                "_keys",
                "zero",
            }
            and len(set(owners)) == 3
            and nodes.ledger is keys.ledger is projection.ledger is ledger
            and nodes.owner == node_owner
            and keys.owner == key_owner
            and projection.owner == projection_owner
            and nodes.nodes_per_entry == 1
            and keys.nodes_per_entry == projection.nodes_per_entry == 0
            and nodes.append_only
            and ledger.is_factory_container(nodes)
            and ledger.is_factory_container(keys)
            and ledger.is_factory_container(projection_store)
            and containers.get(node_owner) is nodes
            and containers.get(key_owner) is keys
            and containers.get(projection_owner) is projection_store
            and node_row is not None
            and key_row is not None
            and projection_row is not None
            and node_row.role == "innovation_action"
            and key_row.role == "reverse_action_interner"
            and projection_row.role == "query_memo"
            and node_row.accounting_delta == key_row.accounting_delta == 0
            and projection_row.accounting_delta == 0
            and projection_row.entries == projection_row.nodes == 0
            and len(projection_store) == 0
        )
        memo_valid, memo_approved = _valid_f5_memo(root, ledger, snapshot)
        valid &= memo_valid
        root_approved.update(memo_approved)
        if snapshot.closed:
            valid &= (
                node_row is not None
                and key_row is not None
                and projection_row is not None
                and projection.audit_snapshot().disposed
                and node_row.disposed
                and key_row.disposed
                and projection_row.disposed
                and len(nodes) == len(keys) == 0
                and node_row.entries == node_row.nodes == 0
                and key_row.entries == key_row.nodes == 0
            )
        else:
            valid &= (
                node_row is not None
                and key_row is not None
                and projection_row is not None
                and not projection.audit_snapshot().disposed
                and not node_row.disposed
                and not key_row.disposed
                and not projection_row.disposed
                and node_row.entries == len(nodes)
                and node_row.nodes
                == sum(_innovation_node_units(node) for node in nodes)
                and key_row.entries == len(keys)
                and key_row.nodes == 0
                and len(nodes) == len(keys)
                and len(nodes) > 0
                and _valid_handle(root.zero, root, expected=0)
            )
            try:
                node_ids = {id(node): index for index, node in enumerate(nodes)}
                keyed_nodes: set[int] = set()
                keyed_indexes: set[int] = set()
                for node, reference in keys.items():
                    index = node_ids.get(id(node))
                    bound = (
                        index is not None
                        and id(node) not in keyed_nodes
                        and index not in keyed_indexes
                        and _valid_handle(reference, root, expected=index)
                    )
                    valid &= bound
                    if bound and index is not None:
                        keyed_nodes.add(id(node))
                        keyed_indexes.add(index)
                        root_approved.add(id(reference))
                valid &= len(keyed_nodes) == len(nodes) and keyed_indexes == set(
                    range(len(nodes))
                )
                for index, node in enumerate(nodes):
                    node_valid, metadata = _valid_node(node, root, index, nodes)
                    valid &= node_valid and id(node) in keyed_nodes
                    if node_valid:
                        root_approved.add(id(node))
                        root_approved.update(metadata)
            except (AttributeError, IndexError, KeyError, TypeError, ValueError):
                valid = False
        if valid:
            approved.update(root_approved)
        else:
            invalid.update((owner, id(root)) for owner in owners)
    return PhysicalSupportPayloadAudit(frozenset(approved), frozenset(invalid))


def _valid_f5_memo(
    root: SymbolicInnovationArena,
    ledger: ResourceLedger,
    snapshot: SymbolicInnovationAuditSnapshot,
) -> tuple[bool, set[int]]:
    """Validate arithmetic handles and charged key metadata without evaluation."""
    from number_compiler.resources.ledger import OwnedMemo
    from number_compiler.resources.stores import LedgerDict

    memo = snapshot.f5_compositions
    if memo is None:
        return snapshot.f5_composition_owner is None, set()
    memo_snapshot = memo.audit_snapshot()
    memo_store_object: object = memo_snapshot.container
    if type(memo_store_object) is not LedgerDict:
        return False, set()
    memo_store = cast(LedgerDict[object, object], memo_store_object)
    if (
        snapshot.closed
        or type(snapshot.f5_composition_owner) is not int
        or snapshot.f5_composition_owner != memo.owner
        or type(memo) is not OwnedMemo
        or memo.ledger is not ledger
        or type(memo.owner) is not int
        or type(memo.nodes_per_entry) is not int
        or memo.nodes_per_entry < 1
        or memo_snapshot.disposed
        or memo_store.ledger is not ledger
        or memo_store.owner != memo.owner
        or memo_store.nodes_per_entry != memo.nodes_per_entry
        or not ledger.is_factory_container(memo_store)
    ):
        return False, set()
    row = next((row for row in ledger.inventory() if row.owner == memo.owner), None)
    if (
        row is None
        or row.disposed
        or row.role != "query_memo"
        or row.name != f"innovation-F5-{id(root.owner):x}-{memo.owner}"
        or not row.evictable
        or row.accounting_delta != 0
        or dict(ledger.iter_containers()).get(memo.owner) is not memo_store
        or row.entries != len(memo_store)
        or row.nodes != row.entries * memo.nodes_per_entry
    ):
        return False, set()
    approved = {id(memo_store)}
    for key, result in memo_store.items():
        if (
            not is_exact_object_tuple(key)
            or len(key) != 4
            or not _valid_child(key[0], root, len(snapshot.nodes))
            or not _valid_child(key[1], root, len(snapshot.nodes))
            or not _valid_child(result, root, len(snapshot.nodes))
            or type(key[2]) is not int
            or key[2] < 0
            or type(key[3]) is not int
            or key[3] < 0
        ):
            return False, set()
        bits = max(1, key[2].bit_length()) + max(1, key[3].bit_length())
        if bits > 64 * memo.nodes_per_entry:
            return False, set()
        approved.update((id(key), *(id(item) for item in key), id(result)))
    return True, approved


def _valid_handle(
    reference: object, root: SymbolicInnovationArena, *, expected: int
) -> bool:
    from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
    from number_compiler.arithmetic.fields.radial_innovation import InnovationID

    return (
        type(root.owner) is ArenaToken
        and root.owner.label == "symbolic-innovation"
        and type(reference) is InnovationID
        and reference.owner is root.owner
        and reference.kind == "symbolic-innovation"
        and type(reference.local_id) is int
        and reference.local_id == expected
        and type(reference.seal) is str
        and reference.seal == f"{id(root.owner):x}:{expected}"
    )


def _valid_child(reference: object, root: SymbolicInnovationArena, parent: int) -> bool:
    local_id = getattr(reference, "local_id", -1)
    return (
        type(local_id) is int
        and 0 <= local_id < parent
        and _valid_handle(reference, root, expected=local_id)
    )


def _valid_node(
    node: object,
    root: SymbolicInnovationArena,
    index: int,
    nodes: Sequence[object],
) -> tuple[bool, set[int]]:
    from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
    from number_compiler.arithmetic.fields.radial_innovation import (
        InnovationAdd,
        InnovationAtom,
        InnovationCharted,
        InnovationInterval,
        InnovationRadial,
        InnovationScale,
        InnovationZero,
        RadialMultiplier,
    )

    metadata: set[int] = set()
    if type(node) is InnovationZero:
        return index == 0, metadata
    if type(node) is InnovationAtom:
        valid, semantic_metadata = _semantic_metadata(node.semantic)
        return valid, semantic_metadata
    if type(node) is InnovationInterval:
        return type(node.length) is int and node.length > 0, metadata
    if type(node) is InnovationRadial:
        multiplier = node.multiplier
        child = getattr(node.child, "local_id", -1)
        valid = (
            type(multiplier) is RadialMultiplier
            and type(multiplier.no_growth) is int
            and type(multiplier.growth) is int
            and multiplier.no_growth >= 0
            and multiplier.growth >= 0
            and not multiplier.is_identity
            and _valid_child(node.child, root, index)
            and type(nodes[child]) not in (InnovationZero, InnovationRadial)
        )
        return bool(valid), {id(multiplier), id(node.child)}
    if type(node) is InnovationCharted:
        chart = node.chart
        child = getattr(node.child, "local_id", -1)
        valid = (
            type(chart) is CylinderChart
            and type(chart.slope) is int
            and type(chart.offset) is int
            and type(chart.extent_scale) is int
            and type(chart.growth_scale) is int
            and chart.slope in (-1, 1)
            and chart.extent_scale == chart.growth_scale == 0
            and (chart.slope, chart.offset) != (1, 0)
            and _valid_child(node.child, root, index)
            and type(nodes[child])
            not in (InnovationZero, InnovationRadial, InnovationCharted)
        )
        return valid, {id(chart), id(node.child)}
    if type(node) is InnovationScale:
        child = getattr(node.child, "local_id", -1)
        valid = (
            type(node.coefficient) is int
            and node.coefficient not in (0, 1)
            and _valid_child(node.child, root, index)
            and type(nodes[child]) not in (InnovationZero, InnovationScale)
        )
        return valid, {id(node.child)}
    if isinstance(node, InnovationAdd):
        if type(node) is not InnovationAdd:
            return False, metadata
        valid = (
            _valid_child(node.left, root, index)
            and _valid_child(node.right, root, index)
            and node.left.local_id < node.right.local_id
            and type(nodes[node.left.local_id]) is not InnovationZero
            and type(nodes[node.right.local_id]) is not InnovationZero
        )
        return valid, {id(node.left), id(node.right)}
    return False, metadata


def _innovation_node_units(node: object) -> int:
    from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
    from number_compiler.arithmetic.fields.radial_innovation import (
        InnovationCharted,
        InnovationInterval,
        InnovationRadial,
        InnovationScale,
        RadialMultiplier,
    )

    def integer_limb_units(*values: int) -> int:
        retained_bits = sum(max(1, abs(value).bit_length()) for value in values)
        return max(1, (retained_bits + 63) // 64)

    if (
        type(node) is InnovationInterval
        and type(node.length) is int
        and node.length >= 0
    ):
        return integer_limb_units(node.length)
    if type(node) is InnovationRadial:
        multiplier = node.multiplier
        if (
            type(multiplier) is not RadialMultiplier
            or type(multiplier.no_growth) is not int
            or type(multiplier.growth) is not int
        ):
            return 1
        return integer_limb_units(multiplier.no_growth, multiplier.growth)
    if type(node) is InnovationCharted:
        chart = node.chart
        if type(chart) is not CylinderChart or any(
            type(value) is not int
            for value in (
                chart.slope,
                chart.offset,
                chart.extent_scale,
                chart.growth_scale,
            )
        ):
            return 1
        return integer_limb_units(
            chart.slope,
            chart.offset,
            chart.extent_scale,
            chart.growth_scale,
        )
    if type(node) is InnovationScale and type(node.coefficient) is int:
        return integer_limb_units(node.coefficient)
    return 1


def _semantic_metadata(value: object) -> tuple[bool, set[int]]:
    from number_compiler.arithmetic.contracts.semantic_identity import (
        SemanticIdentity,
        SemanticIdentityValidator,
    )
    from number_compiler.arithmetic.fields.symbolic_innovation import (
        MAX_PRIMITIVE_IDENTITY_DEPTH,
        MAX_PRIMITIVE_IDENTITY_UNITS,
    )

    if type(value) is not SemanticIdentity:
        return False, set()
    validator = SemanticIdentityValidator()
    try:
        validator.validate(value)
        validator.finish()
    except (TypeError, ValueError, AttributeError):
        return False, set()
    approved: set[int] = set()
    seen: set[int] = set()
    pending: list[tuple[object, int]] = [(value, 0)]
    units = 0
    while pending:
        item, depth = pending.pop()
        units += 1
        if units > MAX_PRIMITIVE_IDENTITY_UNITS or depth > MAX_PRIMITIVE_IDENTITY_DEPTH:
            return False, set()
        if item is None or type(item) is bool:
            continue
        if type(item) is int:
            if abs(item).bit_length() > 64:
                return False, set()
            continue
        if isinstance(item, (str, bytes)):
            if len(item) > 256:
                return False, set()
            continue
        identity = id(item)
        if identity in seen:
            continue
        seen.add(identity)
        if is_exact_object_tuple(item):
            approved.add(identity)
            pending.extend((child, depth + 1) for child in item)
        elif type(item) is SemanticIdentity:
            approved.add(identity)
            pending.append((item.behavior, depth + 1))
        else:
            return False, set()
    return True, approved


__all__ = ["audit_symbolic_innovation_payloads"]

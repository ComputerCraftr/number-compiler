"""Read-only payload validation for source-free symbolic innovation DAGs."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.physical_support_payload_audit import (
    PhysicalSupportPayloadAudit,
)

if TYPE_CHECKING:
    from number_compiler.arithmetic.fields.symbolic_innovation import (
        SymbolicInnovationArena,
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
    from number_compiler.resources.ledger import OwnedMemo
    from number_compiler.resources.stores import LedgerDict, LedgerList

    containers = dict(ledger.iter_containers())
    inventory = {row.owner: row for row in ledger.inventory()}
    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    for root in ledger.iter_execution_roots():
        if type(root) is not SymbolicInnovationArena:
            continue
        try:
            owners = root._node_owner, root._key_owner, root._projection.owner
        except AttributeError:
            invalid.add((-1, id(root)))
            continue
        if any(type(owner) is not int for owner in owners):
            invalid.add((-1, id(root)))
            continue
        node_owner, key_owner, projection_owner = owners
        node_row = inventory.get(node_owner)
        key_row = inventory.get(key_owner)
        projection_row = inventory.get(projection_owner)
        root_approved = {
            id(root._nodes),
            id(root._keys),
            id(root._projection._data),
        }
        valid = (
            root.ledger is ledger
            and type(root._closed) is bool
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
            and type(root._nodes) is LedgerList
            and type(root._keys) is LedgerDict
            and type(root._projection) is OwnedMemo
            and type(root._projection._data) is LedgerDict
            and len(set(owners)) == 3
            and root._nodes.ledger
            is root._keys.ledger
            is root._projection.ledger
            is ledger
            and root._nodes.owner == node_owner
            and root._keys.owner == key_owner
            and root._projection.owner == projection_owner
            and root._nodes.nodes_per_entry == 1
            and root._keys.nodes_per_entry == root._projection.nodes_per_entry == 0
            and root._nodes.append_only
            and ledger.is_factory_container(root._nodes)
            and ledger.is_factory_container(root._keys)
            and ledger.is_factory_container(root._projection._data)
            and containers.get(node_owner) is root._nodes
            and containers.get(key_owner) is root._keys
            and containers.get(projection_owner) is root._projection._data
            and node_row is not None
            and key_row is not None
            and projection_row is not None
            and node_row.role == "innovation_action"
            and key_row.role == "reverse_action_interner"
            and projection_row.role == "query_memo"
            and node_row.accounting_delta == key_row.accounting_delta == 0
            and projection_row.accounting_delta == 0
            and projection_row.entries == projection_row.nodes == 0
            and len(root._projection._data) == 0
        )
        memo_valid, memo_approved = _valid_f5_memo(root, ledger)
        valid &= memo_valid
        root_approved.update(memo_approved)
        if root._closed:
            valid &= (
                node_row is not None
                and key_row is not None
                and projection_row is not None
                and root._projection._disposed
                and node_row.disposed
                and key_row.disposed
                and projection_row.disposed
                and len(root._nodes) == len(root._keys) == 0
                and node_row.entries == node_row.nodes == 0
                and key_row.entries == key_row.nodes == 0
            )
        else:
            valid &= (
                node_row is not None
                and key_row is not None
                and projection_row is not None
                and not root._projection._disposed
                and not node_row.disposed
                and not key_row.disposed
                and not projection_row.disposed
                and node_row.entries == len(root._nodes)
                and node_row.nodes
                == sum(_innovation_node_units(node) for node in root._nodes)
                and key_row.entries == len(root._keys)
                and key_row.nodes == 0
                and len(root._nodes) == len(root._keys)
                and len(root._nodes) > 0
                and _valid_handle(root.zero, root, expected=0)
            )
            try:
                node_ids = {id(node): index for index, node in enumerate(root._nodes)}
                keyed_nodes: set[int] = set()
                keyed_indexes: set[int] = set()
                for node, reference in root._keys.items():
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
                valid &= len(keyed_nodes) == len(root._nodes) and keyed_indexes == set(
                    range(len(root._nodes))
                )
                for index, node in enumerate(root._nodes):
                    node_valid, metadata = _valid_node(node, root, index)
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
    root: SymbolicInnovationArena, ledger: ResourceLedger
) -> tuple[bool, set[int]]:
    """Validate arithmetic handles and charged key metadata without evaluation."""
    from number_compiler.resources.ledger import OwnedMemo
    from number_compiler.resources.stores import LedgerDict

    try:
        memo = root._f5_compositions
    except AttributeError:
        return False, set()
    if memo is None:
        return root._f5_composition_owner is None, set()
    if (
        root._closed
        or type(root._f5_composition_owner) is not int
        or root._f5_composition_owner != memo.owner
        or type(memo) is not OwnedMemo
        or memo.ledger is not ledger
        or type(memo.owner) is not int
        or type(memo.nodes_per_entry) is not int
        or memo.nodes_per_entry < 1
        or memo._disposed
        or type(memo._data) is not LedgerDict
        or memo._data.ledger is not ledger
        or memo._data.owner != memo.owner
        or memo._data.nodes_per_entry != memo.nodes_per_entry
        or not ledger.is_factory_container(memo._data)
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
        or dict(ledger.iter_containers()).get(memo.owner) is not memo._data
        or row.entries != len(memo._data)
        or row.nodes != row.entries * memo.nodes_per_entry
    ):
        return False, set()
    approved = {id(memo._data)}
    for key, result in memo._data.items():
        if (
            type(key) is not tuple
            or len(key) != 4
            or not _valid_child(key[0], root, len(root._nodes))
            or not _valid_child(key[1], root, len(root._nodes))
            or not _valid_child(result, root, len(root._nodes))
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
        and reference.kind == root._KIND == "symbolic-innovation"
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
    node: object, root: SymbolicInnovationArena, index: int
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
            and type(root._nodes[child]) not in (InnovationZero, InnovationRadial)
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
            and type(root._nodes[child])
            not in (InnovationZero, InnovationRadial, InnovationCharted)
        )
        return valid, {id(chart), id(node.child)}
    if type(node) is InnovationScale:
        child = getattr(node.child, "local_id", -1)
        valid = (
            type(node.coefficient) is int
            and node.coefficient not in (0, 1)
            and _valid_child(node.child, root, index)
            and type(root._nodes[child]) not in (InnovationZero, InnovationScale)
        )
        return valid, {id(node.child)}
    if isinstance(node, InnovationAdd):
        if type(node) is not InnovationAdd:
            return False, metadata
        valid = (
            _valid_child(node.left, root, index)
            and _valid_child(node.right, root, index)
            and node.left.local_id < node.right.local_id
            and type(root._nodes[node.left.local_id]) is not InnovationZero
            and type(root._nodes[node.right.local_id]) is not InnovationZero
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
        if type(item) is tuple:
            approved.add(identity)
            pending.extend((child, depth + 1) for child in item)
        elif type(item) is SemanticIdentity:
            approved.add(identity)
            pending.append((item.behavior, depth + 1))
        else:
            return False, set()
    return True, approved


__all__ = ["audit_symbolic_innovation_payloads"]

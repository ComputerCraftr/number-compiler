"""Read-only ledger contract for retained fresh-prime action state."""

from __future__ import annotations

from collections.abc import Hashable
from typing import TYPE_CHECKING

from number_compiler.hashlife.execution.source_image_inventory import SourceImageBinding

if TYPE_CHECKING:
    from number_compiler.sequences.prime.successor_action import (
        PrimeSuccessorActionArena,
    )
    from number_compiler.sequences.prime.successor_action_contracts import (
        PrimeSuccessorImagePayload,
    )
    from number_compiler.sequences.prime.successor_image_adapter import (
        PrimeSuccessorImageAdapter,
    )

from math import prod

from number_compiler.arithmetic.contracts.input_validation import is_object_tuple
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditEntry,
)


def audit_prime_action_arena(ledger: object, root: object) -> PayloadAuditContribution:
    """Validate one arena's exact action stores, without traversing image records."""
    from number_compiler.sequences.prime.coprime_rank import (
        CoprimeRankDAG,
        PrimeFactorSourceIdentity,
    )
    from number_compiler.sequences.prime.successor_action import (
        PrimeSuccessorActionArena,
    )
    from number_compiler.sequences.prime.successor_action_contracts import (
        PrimeSuccessorActionDescriptor,
        PrimeSuccessorActionID,
        PrimeSuccessorActionNode,
        PrimeSuccessorDescriptorID,
        PrimeSuccessorPortEffect,
    )

    if (
        type(ledger) is not ResourceLedger
        or type(root) is not PrimeSuccessorActionArena
    ):
        raise TypeError("prime action audit requires its exact ledger-owned arena")
    arena = root
    snapshot = arena.audit_snapshot()
    approved: list[PayloadAuditEntry] = []
    invalid: list[PayloadAuditEntry] = []

    def approve(owner: int, value: object) -> None:
        approved.append(PayloadAuditEntry(owner, value))

    def reject(owner: int, value: object) -> None:
        invalid.append(PayloadAuditEntry(owner, value))

    if (
        snapshot.ledger is not ledger
        or type(snapshot.rank) is not CoprimeRankDAG
        or snapshot.rank.ledger is not ledger
        or snapshot.closed
        or not snapshot.stores_valid
    ):
        reject(snapshot.node_owner, arena)
        return PayloadAuditContribution((), tuple(invalid))

    rank_authority = snapshot.rank_authority
    if not is_object_tuple(rank_authority) or len(rank_authority) != 3:
        reject(snapshot.node_owner, arena)
        return PayloadAuditContribution((), tuple(invalid))
    rank, rank_ledger, factor_source = rank_authority
    if type(rank) is not CoprimeRankDAG:
        reject(snapshot.node_owner, arena)
        return PayloadAuditContribution((), tuple(invalid))
    descriptor = snapshot.descriptor
    if type(descriptor) is not PrimeSuccessorActionDescriptor:
        reject(snapshot.node_owner, arena)
        return PayloadAuditContribution((), tuple(invalid))
    parent = descriptor.parent_factors
    q = descriptor.fresh_prime
    descriptor_authority = snapshot.descriptor_authority
    descriptor_valid = not (
        not is_object_tuple(descriptor_authority)
        or len(descriptor_authority) != 5
        or descriptor_authority[0] is not descriptor
        or descriptor_authority[1:]
        != (parent, descriptor.parent_period, q, descriptor.forbidden_residues)
        or snapshot.rank is not rank
        or rank_ledger is not ledger
        or type(factor_source) is not PrimeFactorSourceIdentity
        or not rank.validates_factor_source(factor_source)
        or type(snapshot.parent_depth) is not int
        or snapshot.parent_depth < 0
        or snapshot.parent_depth != len(parent)
        or type(snapshot.admitted_successor) is not bool
        or type(parent) is not tuple
        or any(type(value) is not int or value < 2 for value in parent)
        or parent != rank.primes[: snapshot.parent_depth]
        or descriptor.parent_period != prod(parent)
        or type(q) is not int
        or q < 2
        or type(descriptor.forbidden_residues) is not tuple
        or not descriptor.forbidden_residues
        or any(
            type(value) is not int or not 0 <= value < q
            for value in descriptor.forbidden_residues
        )
        or descriptor.forbidden_residues
        != tuple(sorted(set(descriptor.forbidden_residues)))
        or (
            snapshot.admitted_successor
            and (
                len(rank.primes) <= snapshot.parent_depth
                or rank.primes[snapshot.parent_depth] != q
            )
        )
    )
    try:
        if type(snapshot.descriptor_id) is not PrimeSuccessorDescriptorID:
            raise TypeError("prime arena has another descriptor handle sort")
        arena.validate_descriptor(snapshot.descriptor_id)
    except (TypeError, ValueError, AttributeError):
        descriptor_valid = False
    if not descriptor_valid:
        reject(snapshot.node_owner, arena)
        return PayloadAuditContribution((), tuple(invalid))

    nodes = snapshot.nodes
    normal_forms = snapshot.normal_forms
    node_index_valid = (
        type(snapshot.next_node) is int
        and snapshot.next_node == len(nodes)
        and all(type(key) is int for key, _ in nodes)
        and tuple(key for key, _ in nodes) == tuple(range(len(nodes)))
    )
    if not node_index_valid:
        reject(snapshot.node_owner, arena)
        return PayloadAuditContribution((), tuple(invalid))

    normal_ids: set[int] = set()
    canonical_actions: dict[int, PrimeSuccessorActionID] = {}
    for width, action in normal_forms:
        try:
            if type(width) is not int or width < 0:
                raise ValueError("prime normal form has an invalid width")
            if type(action) is not PrimeSuccessorActionID:
                raise TypeError("prime normal form has another handle sort")
            arena.validate_action_handle(action, size=len(nodes))
            if nodes[action.local_id][1].width != width:
                raise ValueError("prime normal form has another node width")
        except (TypeError, ValueError, IndexError, AttributeError):
            reject(snapshot.normal_form_owner, action)
        else:
            normal_ids.add(action.local_id)
            canonical_actions[action.local_id] = action
            approve(snapshot.normal_form_owner, action)

    width = descriptor.parent_period
    if snapshot.identity is not canonical_actions.get(
        0
    ) or snapshot.base is not canonical_actions.get(1):
        reject(snapshot.normal_form_owner, arena)
    for local_id, node in nodes:
        valid = (
            type(node) is PrimeSuccessorActionNode
            and type(node.copies) is int
            and type(node.width) is int
            and node.width >= 0
            and type(node.phase_shift) is int
            and node.phase_shift == node.width % q
            and node.copies == (node.width // width if node.width % width == 0 else -1)
            and local_id in normal_ids
            and (node.before is None) == (node.after is None)
        )
        if valid and node.before is None:
            valid = node.width in (0, 1, width)
        elif valid:
            before, after = node.before, node.after
            valid = (
                type(before) is PrimeSuccessorActionID
                and type(after) is PrimeSuccessorActionID
                and type(before.local_id) is int
                and type(after.local_id) is int
                and before is canonical_actions.get(before.local_id)
                and after is canonical_actions.get(after.local_id)
                and before.local_id < local_id
                and after.local_id < local_id
                and nodes[before.local_id][1].width + nodes[after.local_id][1].width
                == node.width
            )
        if valid:
            approve(snapshot.node_owner, node)
        else:
            reject(snapshot.node_owner, node)

    for key, effect in snapshot.ports:
        valid = (
            type(key) is tuple
            and len(key) == 2
            and type(key[0]) is PrimeSuccessorActionID
            and type(key[1]) is int
            and 0 <= key[1] < q
            and type(key[0].local_id) is int
            and 0 <= key[0].local_id < len(nodes)
            and key[0] is canonical_actions.get(key[0].local_id)
            and type(effect) is PrimeSuccessorPortEffect
            and all(
                type(value) is int
                for value in (
                    effect.entering_phase,
                    effect.outgoing_phase,
                    effect.parent_survivors,
                    effect.deleted_survivors,
                    effect.surviving_values,
                )
            )
            and effect.entering_phase == key[1]
            and effect.outgoing_phase == (key[1] + nodes[key[0].local_id][1].width) % q
            and min(
                effect.parent_survivors,
                effect.deleted_survivors,
                effect.surviving_values,
            )
            >= 0
            and effect.deleted_survivors + effect.surviving_values
            == effect.parent_survivors
            and effect.parent_survivors <= nodes[key[0].local_id][1].width
        )
        if valid:
            approve(snapshot.port_owner, key)
            approve(snapshot.port_owner, effect)
        else:
            reject(snapshot.port_owner, effect)

    return PayloadAuditContribution(tuple(approved), tuple(invalid))


__all__ = ["audit_prime_action_arena"]


def audit_prime_image_binding(
    adapter: PrimeSuccessorImageAdapter,
    binding: SourceImageBinding,
    payload: object,
    failure_prefix: Hashable | None,
) -> None:
    """Check one published image binding without charging or mutating state."""
    from number_compiler.sequences.prime.successor_action_contracts import (
        PrimeSuccessorActionID,
        PrimeSuccessorActionNode,
        PrimeSuccessorImagePayload,
        PrimeSuccessorSource,
    )

    if failure_prefix is not None:
        raise ValueError("prime images cannot publish a failure prefix")

    if type(binding) is not SourceImageBinding:
        raise TypeError("prime image audit requires an exact binding")
    arena = adapter.arena
    if (
        binding.family != adapter.family
        or binding.semantic_version != adapter.semantic_version
        or type(binding.source) is not PrimeSuccessorSource
        or binding.source.descriptor is not arena.descriptor_id
        or type(binding.source.entering_phase) is not int
        or not 0 <= binding.source.entering_phase < arena.descriptor.fresh_prime
        or type(binding.action) is not PrimeSuccessorActionID
    ):
        raise ValueError("prime image binding has another source or action")
    node = arena.audit_action_node(binding.action)
    if (
        type(node) is not PrimeSuccessorActionNode
        or type(payload) is not PrimeSuccessorImagePayload
        or payload.descriptor is not arena.descriptor_id
        or payload.action is not binding.action
        or payload.entering_phase != binding.source.entering_phase
        or payload.outgoing_phase
        != (payload.entering_phase + binding.extent) % arena.descriptor.fresh_prime
        or binding.extent != node.width
        or binding.boundary_ports != (payload.entering_phase, payload.outgoing_phase)
        or binding.orientation != 1
        or binding.precision is not None
    ):
        raise ValueError("prime image binding differs from its retained payload")
    validate_prime_payload_fields(payload, node.width, arena.descriptor.fresh_prime)


def register_prime_action_audit(arena: PrimeSuccessorActionArena) -> None:
    from number_compiler.resources.payload_contracts import (
        PayloadAuditStoreBinding,
    )

    arena.rank.ledger.register_execution_root(arena)
    snapshot = arena.audit_snapshot()
    arena.rank.ledger.register_payload_audit_contract(
        arena,
        "prime",
        (
            PayloadAuditStoreBinding(
                snapshot.node_owner,
                "_audit_nodes",
                "fresh-prime chronological action nodes",
            ),
            PayloadAuditStoreBinding(
                snapshot.normal_form_owner,
                "_audit_normal_forms",
                "fresh-prime action normal forms",
            ),
            PayloadAuditStoreBinding(
                snapshot.port_owner,
                "_audit_ports",
                "demanded fresh-prime port effects",
            ),
        ),
        audit_prime_action_arena,
    )


def validate_prime_payload_fields(
    payload: PrimeSuccessorImagePayload, width: int, q: int
) -> None:
    if (
        any(
            type(value) is not int
            for value in (
                payload.entering_phase,
                payload.outgoing_phase,
                payload.parent_survivors,
                payload.deleted_survivors,
                payload.surviving_values,
            )
        )
        or not 0 <= payload.entering_phase < q
        or not 0 <= payload.outgoing_phase < q
        or payload.outgoing_phase != (payload.entering_phase + width) % q
        or payload.parent_survivors > width
        or min(
            payload.parent_survivors,
            payload.deleted_survivors,
            payload.surviving_values,
        )
        < 0
        or payload.deleted_survivors + payload.surviving_values
        != payload.parent_survivors
    ):
        raise ValueError("invalid prime successor image payload")

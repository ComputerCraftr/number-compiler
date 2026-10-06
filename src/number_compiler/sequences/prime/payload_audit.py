"""Read-only ledger contract for retained fresh-prime action state."""

from __future__ import annotations

from collections.abc import Hashable
from typing import TYPE_CHECKING

from number_compiler.hashlife.execution.source_bound_images import SourceImageBinding

if TYPE_CHECKING:
    from number_compiler.sequences.prime.successor_action import (
        PrimeSuccessorActionArena,
        PrimeSuccessorImageAdapter,
        PrimeSuccessorImagePayload,
    )

from math import prod

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditEntry,
)


def audit_prime_action_arena(ledger: object, root: object) -> PayloadAuditContribution:
    """Validate one arena's exact action stores, without traversing image records."""
    from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG
    from number_compiler.sequences.prime.successor_action import (
        PrimeSuccessorActionArena,
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
    approved: list[PayloadAuditEntry] = []
    invalid: list[PayloadAuditEntry] = []

    def approve(owner: int, value: object) -> None:
        approved.append(PayloadAuditEntry(owner, value))

    def reject(owner: int, value: object) -> None:
        invalid.append(PayloadAuditEntry(owner, value))

    stores = (arena._nodes, arena._normal_forms, arena._ports)
    if (
        arena.rank.ledger is not ledger
        or type(arena.rank) is not CoprimeRankDAG
        or arena._closed
        or arena._audit_nodes is not stores[0]._data
        or arena._audit_normal_forms is not stores[1]._data
        or arena._audit_ports is not stores[2]._data
    ):
        reject(arena._nodes.owner, arena)
        return PayloadAuditContribution((), tuple(invalid))

    rank, rank_ledger, factors = arena._rank_authority
    descriptor = arena.descriptor
    if type(descriptor) is not PrimeSuccessorActionDescriptor:
        reject(arena._nodes.owner, arena)
        return PayloadAuditContribution((), tuple(invalid))
    parent = descriptor.parent_factors
    q = descriptor.fresh_prime
    descriptor_authority = getattr(arena, "_descriptor_authority", None)
    descriptor_valid = not (
        type(descriptor_authority) is not tuple
        or len(descriptor_authority) != 5
        or descriptor_authority[0] is not descriptor
        or descriptor_authority[1:]
        != (parent, descriptor.parent_period, q, descriptor.forbidden_residues)
        or arena.rank is not rank
        or rank_ledger is not ledger
        or arena.rank._factor_store_authority is not factors
        or type(arena._parent_depth) is not int
        or arena._parent_depth < 0
        or arena._parent_depth != len(parent)
        or type(arena._admitted_successor) is not bool
        or type(parent) is not tuple
        or any(type(value) is not int or value < 2 for value in parent)
        or parent != arena.rank.primes[: arena._parent_depth]
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
            arena._admitted_successor
            and (
                len(arena.rank.primes) <= arena._parent_depth
                or arena.rank.primes[arena._parent_depth] != q
            )
        )
    )
    try:
        if type(arena.descriptor_id) is not PrimeSuccessorDescriptorID:
            raise TypeError("prime arena has another descriptor handle sort")
        arena.descriptor_id.validate(arena._owner, "prime-successor-descriptor", size=1)
    except (TypeError, ValueError, AttributeError):
        descriptor_valid = False
    if not descriptor_valid:
        reject(arena._nodes.owner, arena)
        return PayloadAuditContribution((), tuple(invalid))

    nodes = tuple(arena._nodes.items())
    normal_forms = tuple(arena._normal_forms.items())
    node_index_valid = (
        type(arena._next_node) is int
        and arena._next_node == len(nodes)
        and all(type(key) is int for key, _ in nodes)
        and tuple(key for key, _ in nodes) == tuple(range(len(nodes)))
    )
    if not node_index_valid:
        reject(arena._nodes.owner, arena._audit_nodes)
        return PayloadAuditContribution((), tuple(invalid))

    normal_ids: set[int] = set()
    canonical_actions: dict[int, PrimeSuccessorActionID] = {}
    for width, action in normal_forms:
        try:
            if type(width) is not int or width < 0:
                raise ValueError("prime normal form has an invalid width")
            if type(action) is not PrimeSuccessorActionID:
                raise TypeError("prime normal form has another handle sort")
            action.validate(arena._owner, "prime-successor-action", size=len(nodes))
            if nodes[action.local_id][1].width != width:
                raise ValueError("prime normal form has another node width")
        except (TypeError, ValueError, IndexError, AttributeError):
            reject(arena._normal_forms.owner, action)
        else:
            normal_ids.add(action.local_id)
            canonical_actions[action.local_id] = action
            approve(arena._normal_forms.owner, action)

    width = descriptor.parent_period
    if arena.identity is not canonical_actions.get(
        0
    ) or arena.base is not canonical_actions.get(1):
        reject(arena._normal_forms.owner, arena)
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
            approve(arena._nodes.owner, node)
        else:
            reject(arena._nodes.owner, node)

    for key, effect in arena._ports.items():
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
            approve(arena._ports.owner, key)
            approve(arena._ports.owner, effect)
        else:
            reject(arena._ports.owner, effect)

    return PayloadAuditContribution(tuple(approved), tuple(invalid))


__all__ = ["audit_prime_action_arena"]


def audit_prime_image_binding(
    adapter: PrimeSuccessorImageAdapter,
    binding: SourceImageBinding,
    payload: object,
    failure_prefix: Hashable | None,
) -> None:
    """Check one published image binding without charging or mutating state."""
    from number_compiler.sequences.prime.successor_action import (
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
    try:
        binding.action.validate(
            arena._owner, "prime-successor-action", size=len(arena._nodes)
        )
    except (TypeError, ValueError) as error:
        raise ValueError("prime image binding has a foreign action") from error
    node = arena._nodes._data.get(binding.action.local_id)
    if (
        type(node) is not PrimeSuccessorActionNode
        or arena._normal_forms._data.get(node.width) is not binding.action
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
    arena.rank.ledger.register_payload_audit_contract(
        arena,
        "prime",
        (
            PayloadAuditStoreBinding(
                arena._nodes.owner,
                "_audit_nodes",
                "fresh-prime chronological action nodes",
            ),
            PayloadAuditStoreBinding(
                arena._normal_forms.owner,
                "_audit_normal_forms",
                "fresh-prime action normal forms",
            ),
            PayloadAuditStoreBinding(
                arena._ports.owner,
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

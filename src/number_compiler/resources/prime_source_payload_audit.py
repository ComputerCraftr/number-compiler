"""Read-only retained-shape audit for the source-bound Prime action arena."""

from __future__ import annotations

from collections.abc import Mapping
from math import prod

from number_compiler.resources.ledger import ResourceLedger


def audit_prime_source_adapter(
    adapter: object,
    ledger: ResourceLedger,
    containers: Mapping[int, object],
    records: tuple[object, ...],
    image_owner: int,
) -> tuple[frozenset[int], frozenset[int], frozenset[tuple[int, int]]]:
    """Admit owned records; this does not prove counts equal Legendre Phi."""
    from number_compiler.hashlife.execution.source_bound_images import _ImageRecord
    from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG
    from number_compiler.sequences.prime.successor_action import (
        PrimeSuccessorActionArena,
        PrimeSuccessorActionDescriptor,
        PrimeSuccessorActionID,
        PrimeSuccessorActionNode,
        PrimeSuccessorDescriptorID,
        PrimeSuccessorImageAdapter,
        PrimeSuccessorImagePayload,
        PrimeSuccessorPortEffect,
        PrimeSuccessorSource,
    )

    if type(adapter) is not PrimeSuccessorImageAdapter:
        return frozenset(), frozenset(), frozenset()
    arena = adapter.arena
    approved: set[int] = set()
    recognized: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    if type(arena) is not PrimeSuccessorActionArena:
        return frozenset(), frozenset(), frozenset({(image_owner, id(adapter))})
    stores = (arena._nodes, arena._normal_forms, arena._ports)
    if (
        adapter.ledger is not ledger
        or type(arena.rank) is not CoprimeRankDAG
        or arena.rank.ledger is not ledger
        or arena._closed
        or any(
            store._disposed or containers.get(store.owner) is not store._data
            for store in stores
        )
    ):
        invalid.add((arena._nodes.owner, id(arena)))
        return frozenset(), frozenset(), frozenset(invalid)
    rank, rank_ledger, factors = arena._rank_authority
    descriptor = arena.descriptor
    if type(descriptor) is not PrimeSuccessorActionDescriptor:
        invalid.add((arena._nodes.owner, id(descriptor)))
        return frozenset(), frozenset(), frozenset(invalid)
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
    if not descriptor_valid:
        invalid.add((arena._nodes.owner, id(descriptor)))
    try:
        if type(arena.descriptor_id) is not PrimeSuccessorDescriptorID:
            raise TypeError("prime arena has another descriptor handle sort")
        arena.descriptor_id.validate(arena._owner, "prime-successor-descriptor", size=1)
    except (TypeError, ValueError, AttributeError):
        invalid.add((arena._nodes.owner, id(arena.descriptor_id)))
    if not descriptor_valid:
        return frozenset(), frozenset(), frozenset(invalid)
    nodes = tuple(arena._nodes.items())
    normal_forms = tuple(arena._normal_forms.items())
    node_index_valid = (
        type(arena._next_node) is int
        and arena._next_node == len(nodes)
        and all(type(key) is int for key, _ in nodes)
        and tuple(key for key, _ in nodes) == tuple(range(len(nodes)))
    )
    if not node_index_valid:
        invalid.add((arena._nodes.owner, id(arena._nodes)))
        return frozenset(), frozenset(), frozenset(invalid)
    normal_ids: set[int] = set()
    canonical_actions: dict[int, PrimeSuccessorActionID] = {}
    for width, action in normal_forms:
        recognized.add(id(action))
        try:
            if type(width) is not int or width < 0:
                raise ValueError("prime normal form has an invalid width")
            if type(action) is not PrimeSuccessorActionID:
                raise TypeError("prime normal form has another handle sort")
            action.validate(arena._owner, "prime-successor-action", size=len(nodes))
            if nodes[action.local_id][1].width != width:
                raise ValueError("prime normal form has another node width")
        except (TypeError, ValueError, IndexError, AttributeError):
            invalid.add((arena._normal_forms.owner, id(action)))
        else:
            normal_ids.add(action.local_id)
            canonical_actions[action.local_id] = action
            approved.add(id(action))
    W = descriptor.parent_period
    if arena.identity is not canonical_actions.get(
        0
    ) or arena.base is not canonical_actions.get(1):
        invalid.add((arena._normal_forms.owner, id(arena)))
    for local_id, node in nodes:
        recognized.add(id(node))
        valid = (
            type(node) is PrimeSuccessorActionNode
            and type(node.copies) is int
            and type(node.width) is int
            and node.width >= 0
            and type(node.phase_shift) is int
            and node.phase_shift == node.width % q
            and node.copies == (node.width // W if node.width % W == 0 else -1)
            and local_id in normal_ids
            and (node.before is None) == (node.after is None)
        )
        if valid and node.before is None:
            valid = node.width in (0, 1, W)
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
            approved.add(id(node))
        else:
            invalid.add((arena._nodes.owner, id(node)))
    for key, effect in arena._ports.items():
        recognized.update((id(key), id(effect)))
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
            approved.update((id(key), id(effect)))
        else:
            invalid.add((arena._ports.owner, id(effect)))
    for record in records:
        if type(record) is not _ImageRecord or record.adapter_key != (
            adapter.family,
            adapter.semantic_version,
        ):
            continue
        source, image_action, payload = (
            record.binding.source,
            record.binding.action,
            record.payload,
        )
        valid = (
            type(source) is PrimeSuccessorSource
            and source.descriptor is arena.descriptor_id
            and type(source.entering_phase) is int
            and 0 <= source.entering_phase < q
            and type(image_action) is PrimeSuccessorActionID
            and type(image_action.local_id) is int
            and image_action is canonical_actions.get(image_action.local_id)
            and type(payload) is PrimeSuccessorImagePayload
            and payload.descriptor is arena.descriptor_id
            and payload.action is image_action
            and all(
                type(value) is int
                for value in (
                    payload.entering_phase,
                    payload.outgoing_phase,
                    payload.parent_survivors,
                    payload.deleted_survivors,
                    payload.surviving_values,
                )
            )
            and payload.entering_phase == source.entering_phase
            and payload.outgoing_phase
            == (payload.entering_phase + record.binding.extent) % q
            and min(
                payload.parent_survivors,
                payload.deleted_survivors,
                payload.surviving_values,
            )
            >= 0
            and payload.deleted_survivors + payload.surviving_values
            == payload.parent_survivors
            and payload.parent_survivors <= record.binding.extent
            and record.binding.extent == nodes[image_action.local_id][1].width
            and record.binding.boundary_ports
            == (payload.entering_phase, payload.outgoing_phase)
            and record.failure_prefix is None
        )
        if not valid:
            invalid.add((image_owner, id(record)))
    return frozenset(approved), frozenset(recognized), frozenset(invalid)


__all__ = ["audit_prime_source_adapter"]

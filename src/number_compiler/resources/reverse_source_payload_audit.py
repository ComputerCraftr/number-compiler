"""Independent retained-payload audit for the reverse/add source adapter."""

from __future__ import annotations

from collections.abc import Mapping, Sized
from dataclasses import dataclass
from typing import cast

from number_compiler.resources.ledger import (
    OwnedMemo,
    ResourceInventory,
    ResourceLedger,
)


@dataclass(frozen=True, slots=True)
class ReverseSourcePayloadAudit:
    """Objects admitted by the reverse/add source-image owner."""

    approved: frozenset[int]
    recognized: frozenset[int]
    invalid: frozenset[tuple[int, int]]

    def recognizes(self, value: object) -> bool:
        from number_compiler.sequences.reverse_add.source_images import (
            ReverseActionID,
            ReverseImagePayload,
            ReverseSource,
        )

        return (
            type(value) in (ReverseActionID, ReverseSource, ReverseImagePayload)
            or id(value) in self.recognized
        )

    def valid(self, value: object) -> bool:
        return id(value) in self.approved


def _store_valid(
    owner: object,
    store: object,
    expected_role: str,
    containers: Mapping[int, object],
    inventory: Mapping[int, object],
) -> bool:
    if type(owner) is not int:
        return False
    data = getattr(store, "_data", None)
    if not isinstance(data, Sized):
        return False
    item = inventory.get(owner)
    if type(item) is not ResourceInventory:
        return False
    typed_item = item
    is_memo = type(store) is OwnedMemo
    nodes_per_entry = getattr(store, "nodes_per_entry", 0)
    expected_nodes = len(data) * nodes_per_entry if is_memo else len(data)
    owned_container = data if is_memo else store
    return (
        data is not None
        and containers.get(owner) is owned_container
        and item is not None
        and typed_item.role == expected_role
        and typed_item.entries == len(data)
        and typed_item.nodes == expected_nodes
    )


def audit_reverse_source_payloads(
    ledger: ResourceLedger,
    roots: tuple[object, ...],
    containers: Mapping[int, object],
) -> ReverseSourcePayloadAudit:
    """Validate reverse source records without constructing or evaluating images."""
    from number_compiler.arithmetic.carry.carry_monoid import CarryFn
    from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
    from number_compiler.hashlife.execution.source_bound_images import (
        SourceBoundSchedulerCore,
        SourceImageID,
        _ImageRecord,
    )
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
    from number_compiler.sequences.reverse_add.source_images import (
        ReverseActionArena,
        ReverseActionID,
        ReverseActionNode,
        ReverseSource,
        ReverseSourceImageWorkspace,
        _ReverseSourceImageAdapter,
        _ReverseSourceRecord,
    )
    from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts

    inventory = {item.owner: item for item in ledger.inventory()}
    approved: set[int] = set()
    recognized: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    # Spatial carry products are projections, not source or successor identities.
    # Audit geometry and source ownership without invoking any runtime evaluator.
    for ports in roots:
        if type(ports) is not SourceCarryPorts or ports._closed:
            continue
        owner = getattr(ports._cache, "owner", -1)
        port_authority = ports._authority
        port_source = ports._source
        valid_ports = (
            type(port_authority) is tuple
            and len(port_authority) == 10
            and port_authority[0] is port_source
            and type(port_source) is ExactSource
            and port_source.digits is port_authority[1]
            and port_source.base == port_authority[2]
            and port_source.orbit == port_authority[3]
            and port_source.blank == port_authority[4]
            and port_source.extent == port_authority[5]
            and port_source.alphabet_size == port_authority[6]
            and ports._ledger is ledger
            and port_authority[7] is ledger
            and port_authority[8] is ports._cache
            and port_authority[9] == owner
            and ports._workspace_owner == ports._workspace_authority
            and ports._width == len(port_source.digits)
            and _store_valid(
                owner,
                ports._cache,
                "reverse_source_carry_interval",
                containers,
                inventory,
            )
        )
        recognized.add(id(ports))
        for key, value in ports._cache.items():
            recognized.add(id(key))
            geometry_valid = (
                type(key) is tuple
                and len(key) == 3
                and all(type(item) is int for item in key)
                and key[0] in (1, 2)
                and key[1] >= 0
                and key[2] > 0
                and key[2] & (key[2] - 1) == 0
                and key[1] % key[2] == 0
                and key[1] + key[2] <= ports._width + int(key[0] == 2)
                and type(value) is CarryFn
            )
            if valid_ports and geometry_valid:
                approved.add(id(key))
            else:
                invalid.add((owner, id(key)))
        if valid_ports:
            approved.update((id(ports), id(ports._cache._data)))
        else:
            invalid.add((owner, id(ports)))
    for root in roots:
        if type(root) is not ReverseSourceImageWorkspace:
            continue
        actions = root.actions
        owner = getattr(getattr(actions, "_nodes", None), "owner", -1)
        if type(actions) is not ReverseActionArena or actions.ledger is not ledger:
            invalid.add((owner, id(root)))
            continue
        valid = (
            root.ledger is ledger
            and type(root._disposed) is bool
            and not root._disposed
            and type(actions._closed) is bool
            and not actions._closed
        )
        authority = getattr(root, "_authority", None)
        valid &= (
            type(authority) is tuple
            and len(authority) == 8
            and authority[0] is ledger
            and authority[1] is actions
            and authority[2] is root.source
            and authority[3] is root.root_action
            and authority[4] is root.scheduler
            and authority[5] is root.adapter
            and authority[6] == root.steps
            and authority[7] == root.base
        )
        stores = (
            (actions._nodes, "reverse_source_action"),
            (actions._normal, "reverse_source_action_normal_form"),
            (actions._sources, "reverse_original_source"),
            (actions._workspace, "reverse_source_action_workspace"),
        )
        stores_valid = True
        for store, role in stores:
            store_owner = getattr(store, "owner", None)
            if not _store_valid(store_owner, store, role, containers, inventory):
                stores_valid = False
            else:
                data = getattr(store, "_data", None)
                if data is not None:
                    approved.add(id(data) if type(store) is OwnedMemo else id(store))
        valid &= stores_valid
        action_size = len(actions._nodes)

        def action_handle_valid(
            value: object,
            *,
            _owner: object = actions.owner,
            _kind: str = actions._KIND,
            _size: int = action_size,
        ) -> bool:
            return (
                type(value) is ReverseActionID
                and value.owner is _owner
                and value.kind == _kind
                and type(value.local_id) is int
                and 0 <= value.local_id < _size
            )

        source = None
        root_action = None
        if (
            type(root.source) is ReverseSource
            and root.source.owner is actions.owner
            and root.source.kind == actions._SOURCE_KIND
            and type(root.source.local_id) is int
        ):
            try:
                source_record = actions._sources[root.source.local_id]
                authority = actions._source_authority
                if (
                    type(root.source.local_id) is int
                    and root.source.local_id == 0
                    and type(source_record) is _ReverseSourceRecord
                    and type(authority) is tuple
                    and len(authority) == 4
                    and authority[0] is source_record
                    and authority[1] is source_record.exact
                    and authority[2] is source_record.exact.digits
                    and authority[3] == source_record.exact.base
                ):
                    source = source_record.exact
            except (TypeError, ValueError, AttributeError, IndexError, KeyError):
                source = None
        if action_handle_valid(root.root_action):
            root_action = actions._nodes[root.root_action.local_id]
        if (
            type(root.source) is not ReverseSource
            or type(root.root_action) is not ReverseActionID
        ):
            valid = False
        if type(root.steps) is not int or root.steps < 0:
            valid = False
        if type(root.base) is not int or root.base < 2:
            valid = False
        if type(root.scheduler) is not TileScheduler or not root.scheduler._source_only:
            valid = False
        if (
            type(root.adapter) is not _ReverseSourceImageAdapter
            or root.adapter.actions is not actions
            or root.adapter.ledger is not ledger
        ):
            valid = False
        if type(source) is not ExactSource or source.orbit != "reverse-add":
            valid = False
        else:
            valid &= (
                source.base == root.base
                and bool(source.digits)
                and all(
                    type(digit) is int and 0 <= digit < source.base
                    for digit in source.digits
                )
                and root.root_action == actions._normal.get(root.steps)
            )
        if root_action is not None:
            valid &= root_action.steps == root.steps

        ports = root.adapter._ports
        if ports is not None:
            valid &= (
                type(ports) is SourceCarryPorts
                and ports._source is source
                and ports._ledger is ledger
                and id(ports) in approved
            )

        for index, node in actions._nodes.items():
            recognized.add(id(node))
            action = ReverseActionID(actions.owner, actions._KIND, index)
            node_valid = (
                type(index) is int and index >= 0 and type(node) is ReverseActionNode
            )
            node_valid &= (
                action_handle_valid(action) and actions._nodes.get(index) is node
            )
            if node_valid and index == 0:
                node_valid &= node == ReverseActionNode(0, None, None, 0)
            elif node_valid and index == 1:
                node_valid &= node == ReverseActionNode(1, None, None, 1)
            elif node_valid:
                before = node.before
                after = node.after
                if not action_handle_valid(before) or not action_handle_valid(after):
                    node_valid = False
                else:
                    before_id = cast(ReverseActionID, before)
                    after_id = cast(ReverseActionID, after)
                    node_valid = (
                        type(node.steps) is int
                        and node.steps >= 2
                        and before_id.local_id < index
                        and after_id.local_id < index
                        and actions._nodes[before_id.local_id].steps
                        + actions._nodes[after_id.local_id].steps
                        == node.steps
                        and node.depth
                        == 1
                        + max(
                            actions._nodes[before_id.local_id].depth,
                            actions._nodes[after_id.local_id].depth,
                        )
                    )
            valid &= node_valid
            if node_valid:
                approved.update((id(node), id(action)))
            else:
                invalid.add((getattr(actions._nodes, "owner", -1), id(node)))

        for steps, action in actions._normal.items():
            recognized.add(id(action))
            action_valid = type(steps) is int and type(action) is ReverseActionID
            if action_valid:
                action_valid = (
                    action_handle_valid(action)
                    and actions._nodes[action.local_id].steps == steps
                )
            valid &= action_valid
            if action_valid:
                approved.add(id(action))
            else:
                invalid.add((getattr(actions._normal, "owner", -1), id(action)))

        for index, record in actions._sources.items():
            recognized.add(id(record))
            record_valid = index == 0 and type(record) is _ReverseSourceRecord
            exact = getattr(record, "exact", None)
            record_valid &= type(exact) is ExactSource and exact is source
            valid &= record_valid
            if record_valid:
                approved.update((id(record), id(exact)))
            else:
                invalid.add((getattr(actions._sources, "owner", -1), id(record)))

        for handle in (
            root.source,
            root.root_action,
            actions.identity,
            actions.primitive,
        ):
            recognized.add(id(handle))
            if (
                type(handle) is ReverseSource and handle is root.source
            ) or action_handle_valid(handle):
                approved.add(id(handle))
        cached_image = root._image
        if cached_image is not None:
            cached_valid = False
            core = getattr(root.scheduler, "_source_images", None)
            if (
                type(core) is SourceBoundSchedulerCore
                and core.ledger is ledger
                and not core._closed
                and type(cached_image) is SourceImageID
                and cached_image.owner is core.owner
                and cached_image.kind == core._KIND
                and type(cached_image.local_id) is int
                and 0 <= cached_image.local_id < len(core._nodes)
            ):
                image_record = core._nodes[cached_image.local_id]
                cached_valid = (
                    type(image_record) is _ImageRecord
                    and image_record.binding.source == root.source
                    and image_record.binding.action == root.root_action
                    and image_record.adapter_key
                    == (root.adapter.family, root.adapter.semantic_version)
                    and core._adapters.get(image_record.adapter_key) is root.adapter
                )
            if not cached_valid:
                valid = False
                invalid.add((owner, id(cached_image)))
        if valid:
            approved.add(id(root))
        else:
            invalid.add((owner, id(root)))
    return ReverseSourcePayloadAudit(
        frozenset(approved), frozenset(recognized), frozenset(invalid)
    )


__all__ = ["ReverseSourcePayloadAudit", "audit_reverse_source_payloads"]

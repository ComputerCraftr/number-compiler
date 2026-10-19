"""Read-only ownership audit for recursive field images and source cells."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from number_compiler.resources.field_image_domain_audit import indexed_record_matches
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_contracts import PayloadAuditContractAudit


@dataclass(frozen=True, slots=True)
class FieldImagePayloadAudit:
    approved: frozenset[int]
    invalid: frozenset[tuple[int, int]]
    virtual_interfaces: frozenset[tuple[int, int]]


def audit_field_image_payloads(
    ledger: ResourceLedger,
    contracts: PayloadAuditContractAudit | None = None,
) -> FieldImagePayloadAudit:
    containers = dict(ledger.iter_containers())
    roots = tuple(ledger.iter_execution_roots())
    legacy_prefixes = (
        "number_compiler.hashlife.execution.continuations.",
        "number_compiler.hashlife.execution.field_images",
        "number_compiler.hashlife.execution.field_transfers",
        "number_compiler.hashlife.execution.recursive_outputs",
    )
    if not any(
        type(root).__module__.startswith(legacy_prefixes)
        or (
            type(root).__module__ == "number_compiler.hashlife.actions.field_actions"
            and type(root).__name__ == "FieldGeometryArena"
        )
        for root in roots
    ):
        from number_compiler.hashlife.interfaces.diamond_quotient import (
            DiamondQuotientArena,
        )
        from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
        from number_compiler.hashlife.tiles.tiles import TileArena
        from number_compiler.resources.quotient_inventory import audit_quotient_arena
        from number_compiler.resources.tile_inventory import audit_tiles
        from number_compiler.resources.tile_result_inventory import audit_tile_results
        from number_compiler.resources.tile_runtime_inventory import audit_tile_runtime

        live_approved, live_invalid = audit_tile_runtime(
            ledger, containers, roots, contracts
        )
        for root in roots:
            if type(root) is TileArena:
                found, rejected = audit_tiles(root, containers)
            elif type(root) is CompletedResultArena:
                found, rejected = audit_tile_results(root, containers)
            elif type(root) is DiamondQuotientArena:
                found, rejected = audit_quotient_arena(root, ledger, containers)
            else:
                continue
            live_approved.update(found)
            live_invalid.update(rejected)
        return FieldImagePayloadAudit(
            frozenset(live_approved), frozenset(live_invalid), frozenset()
        )

    from number_compiler.arithmetic.fields.dyadic_tile import DyadicTile
    from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
    from number_compiler.hashlife.actions.field_actions import (
        FieldCellActionID,
        FieldGeometry,
        FieldGeometryArena,
        FieldGeometryAuditSnapshot,
        FieldGeometryID,
    )
    from number_compiler.hashlife.execution.continuations.concrete_directed_residual import (
        validate_residual,
    )
    from number_compiler.hashlife.execution.continuations.concrete_port_records import (
        ComposedPort,
        PortStateID,
        Residual,
        ResidualBindingID,
        VirtualInterfaceID,
    )
    from number_compiler.hashlife.execution.continuations.concrete_port_records import (
        VirtualBinding as _VirtualBinding,
    )
    from number_compiler.hashlife.execution.continuations.concrete_port_records import (
        VirtualInterface as _VirtualInterface,
    )
    from number_compiler.hashlife.execution.continuations.concrete_port_scheduler import (
        ConcretePortScheduler,
    )
    from number_compiler.hashlife.execution.continuations.higher_values import (
        RuntimeValueID,
    )
    from number_compiler.hashlife.execution.continuations.provider_absorption import (
        ProviderAbsorptionArena,
        ProviderAction,
        ProviderActionID,
        ProviderBindingKey,
        ProviderBoundary,
        ProviderPointKey,
    )
    from number_compiler.hashlife.execution.continuations.provider_fused_transfer import (
        FusedProviderBinding,
        ProviderFusedPointKey,
        ProviderFusedTransfer,
        ProviderFusedWidthKey,
    )
    from number_compiler.hashlife.execution.continuations.provider_image_input import (
        ProviderImageInputArena,
    )
    from number_compiler.hashlife.execution.continuations.provider_layers import (
        ProviderLayerID,
        ProviderLayerNode,
    )
    from number_compiler.hashlife.execution.continuations.virtual_port_transfers import (
        validate_virtual_transfer,
    )
    from number_compiler.hashlife.execution.field_images import (
        RecursiveFieldImageArena,
        SourceCellArena,
        SourceCellID,
        SourceForestID,
        SourceForestRecord,
    )
    from number_compiler.hashlife.execution.field_transfers import (
        FieldTransferArena,
        FieldTransferID,
        FieldTransferKey,
        FieldTransferRecord,
        FieldTransferRequestKey,
    )
    from number_compiler.hashlife.interfaces.diamond_quotient import (
        DiamondQuotientArena,
    )
    from number_compiler.hashlife.interfaces.semantic_structures import (
        DiamondKey,
        LocalInterfaceID,
        MacroComponents,
        MacroInterface,
        QuotientRecord,
    )
    from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
    from number_compiler.hashlife.tiles.tiles import TileArena
    from number_compiler.resources.field_image_audit_contracts import (
        ConcretePortSchedulerAuditSnapshot,
        DiamondQuotientAuditSnapshot,
        FieldTransferAuditSnapshot,
        SourceCellArenaAuditSnapshot,
    )
    from number_compiler.resources.field_image_domain_audit import (
        audit_recursive_field_images,
    )
    from number_compiler.resources.provider_image_payload_audit import (
        audit_provider_image_inputs,
    )
    from number_compiler.resources.tile_inventory import audit_tiles
    from number_compiler.resources.tile_result_inventory import audit_tile_results
    from number_compiler.resources.tile_runtime_inventory import audit_tile_runtime

    def valid_provider_occurrence(
        providers: ProviderAbsorptionArena, binding: ProviderBindingKey
    ) -> bool:
        if type(binding) is not ProviderBindingKey:
            return False
        try:
            providers.validate_binding_authority(binding)
        except (TypeError, ValueError, IndexError, KeyError, AttributeError):
            return False
        return True

    def audit_provider_point(
        key: ProviderPointKey | ProviderFusedPointKey,
        result: object,
        expected_type: type[ProviderPointKey] | type[ProviderFusedPointKey],
        binding_is_present: Callable[[object], bool],
        validate_boundary: Callable[[ProviderBoundary], object],
        owner: int,
    ) -> None:
        valid = (
            type(key) is expected_type
            and binding_is_present(key.binding)
            and type(key.coordinate) is int
            and key.coordinate >= 0
            and type(result) is int
        )
        try:
            validate_boundary(key.left)
            validate_boundary(key.right)
        except (TypeError, ValueError, IndexError, KeyError, AttributeError):
            valid = False
        if valid:
            approved.add(id(key))
        else:
            invalid.add((owner, id(key)))

    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    virtual_interfaces: set[tuple[int, int]] = set()
    valid: bool = False
    runtime_approved, runtime_invalid = audit_tile_runtime(
        ledger,
        containers,
        roots,
        contracts,
    )
    approved.update(runtime_approved)
    invalid.update(runtime_invalid)
    for root in ledger.iter_execution_roots():
        if type(root) is TileArena:
            tile_approved, tile_invalid = audit_tiles(root, containers)
            approved.update(tile_approved)
            invalid.update(tile_invalid)
        if type(root) is CompletedResultArena:
            result_approved, result_invalid = audit_tile_results(root, containers)
            approved.update(result_approved)
            invalid.update(result_invalid)
        if type(root) is SourceCellArena:
            source_state: SourceCellArenaAuditSnapshot = root.audit_snapshot()
            source_stores = (
                (source_state.node_owner, source_state.nodes),
                (source_state.key_owner, source_state.keys),
                (source_state.forest_node_owner, source_state.forests),
                (source_state.forest_key_owner, source_state.forest_keys),
            )
            valid_root = (
                source_state.ledger is ledger
                and source_state.owner is root.owner
                and all(
                    containers.get(owner) is store for owner, store in source_stores
                )
            )
            for index, source_record in enumerate(source_state.nodes):
                valid = valid_root
                try:
                    valid &= (
                        root.resolve(
                            SourceCellID(
                                source_state.owner, source_state.cell_kind, index
                            )
                        )
                        is source_record
                    )
                    source_record.__post_init__()
                    valid &= source_state.keys.get(source_record.source_tile) == index
                    if source_record.level:
                        valid &= 0 <= source_record.left < index
                        valid &= 0 <= source_record.right < index
                        if valid:
                            left = source_state.nodes[source_record.left]
                            right = source_state.nodes[source_record.right]
                            valid &= source_record.source_tile.left is left.source_tile
                            valid &= (
                                source_record.source_tile.right is right.source_tile
                            )
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(source_record))
                else:
                    invalid.add((source_state.node_owner, id(source_record)))
            for key, index in source_state.keys.items():
                valid = (
                    type(key) is DyadicTile
                    and type(index) is int
                    and 0 <= index < len(source_state.nodes)
                )
                if valid:
                    record = source_state.nodes[index]
                    valid &= key is record.source_tile
                if valid:
                    approved.add(id(key))
                else:
                    invalid.add((source_state.key_owner, id(key)))
            for index, forest in enumerate(source_state.forests):
                valid = valid_root and type(forest) is SourceForestRecord
                try:
                    forest.__post_init__()
                    valid &= (
                        root.resolve_forest(
                            SourceForestID(
                                source_state.owner, source_state.forest_kind, index
                            )
                        )
                        is forest
                    )
                    valid &= (
                        sum(root.resolve(cell).width for cell in forest.cells)
                        == forest.extent
                    )
                    forest_key = (
                        tuple(cell.local_id for cell in forest.cells),
                        forest.extent,
                    )
                    valid &= source_state.forest_keys.get(forest_key) == index
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(forest))
                else:
                    invalid.add((source_state.forest_node_owner, id(forest)))
            for forest_key, index in source_state.forest_keys.items():
                valid = (
                    type(forest_key) is tuple
                    and len(forest_key) == 2
                    and type(index) is int
                    and 0 <= index < len(source_state.forests)
                )
                if valid:
                    forest = source_state.forests[index]
                    valid &= forest_key == (
                        tuple(cell.local_id for cell in forest.cells),
                        forest.extent,
                    )
                if valid:
                    approved.add(id(forest_key))
                else:
                    invalid.add((source_state.forest_key_owner, id(forest_key)))
        elif type(root) is FieldGeometryArena:
            geometry_state: FieldGeometryAuditSnapshot = root.audit_snapshot()
            geometry_stores = (
                (geometry_state.node_owner, geometry_state.nodes),
                (geometry_state.key_owner, geometry_state.keys),
            )
            valid_root = (
                geometry_state.ledger is ledger
                and geometry_state.owner is root.owner
                and all(
                    containers.get(owner) is store for owner, store in geometry_stores
                )
            )
            for index, geometry in enumerate(geometry_state.nodes):
                try:
                    geometry.__post_init__()
                    valid = valid_root and (
                        root.resolve(
                            FieldGeometryID(
                                geometry_state.owner, geometry_state.node_kind, index
                            )
                        )
                        is geometry
                    )
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(geometry))
                else:
                    invalid.add((geometry_state.node_owner, id(geometry)))
            for geometry_key, index in geometry_state.keys.items():
                valid = valid_root and type(geometry_key) is FieldGeometry
                valid &= type(index) is int and 0 <= index < len(geometry_state.nodes)
                if valid:
                    valid &= geometry_state.nodes[index] is geometry_key
                if valid:
                    approved.add(id(geometry_key))
                else:
                    invalid.add((geometry_state.key_owner, id(geometry_key)))
        elif type(root) is ConcretePortScheduler:
            state: ConcretePortSchedulerAuditSnapshot = root.audit_snapshot()
            virtual_stores = (
                (state.virtual_owner, state.virtual),
                (state.virtual_key_owner, state.virtual_keys),
                (state.virtual_binding_owner, state.virtual_bindings),
            )
            layer_state = state.layers
            layer_stores = (
                (layer_state.node_owner, layer_state.nodes),
                (layer_state.key_owner, layer_state.keys),
            )
            scheduler_stores = (
                (state.port_owner, state.ports),
                (state.port_key_owner, state.port_keys),
                (state.residual_owner, state.residuals),
                (state.residual_key_owner, state.residual_keys),
                (state.memo_owner, state.memo),
            )
            valid_root = (
                state.ledger is ledger
                and state.owner is root.owner
                and layer_state.ledger is ledger
                and all(
                    containers.get(owner) is store
                    for owner, store in virtual_stores + layer_stores + scheduler_stores
                )
            )
            for port_index, port_record in state.ports.items():
                valid = (
                    valid_root
                    and type(port_index) is int
                    and type(port_record) is ComposedPort
                )
                try:
                    root.adapter.validate_action(port_record.action)
                    root.validate_side(port_record.side)
                    root.validate_atom(port_record.anchor)
                    root.resolve_residual(port_record.residual)
                    valid &= (
                        root.resolve_port(
                            PortStateID(state.owner, state.port_kind, port_index),
                        )
                        is port_record
                    )
                    valid &= state.port_keys.get(port_record) == port_index
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(port_record))
                else:
                    invalid.add((state.port_owner, id(port_record)))
                    valid_root = False
            for port_record, port_index in state.port_keys.items():
                valid = (
                    valid_root
                    and type(port_record) is ComposedPort
                    and type(port_index) is int
                    and state.ports.get(port_index) is port_record
                )
                if valid:
                    approved.add(id(port_record))
                else:
                    invalid.add((state.port_key_owner, id(port_record)))
                    valid_root = False
            for residual_index, residual_record in state.residuals.items():
                valid = (
                    valid_root
                    and type(residual_index) is int
                    and type(residual_record) is Residual
                )
                try:
                    validate_residual(root, residual_record)
                    valid &= (
                        root.resolve_residual(
                            ResidualBindingID(
                                state.owner,
                                state.residual_kind,
                                residual_index,
                            )
                        )
                        is residual_record
                    )
                    valid &= state.residual_keys.get(residual_record) == residual_index
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(residual_record))
                else:
                    invalid.add((state.residual_owner, id(residual_record)))
                    valid_root = False
            for residual_record, residual_index in state.residual_keys.items():
                valid = (
                    valid_root
                    and type(residual_record) is Residual
                    and type(residual_index) is int
                    and state.residuals.get(residual_index) is residual_record
                )
                if valid:
                    approved.add(id(residual_record))
                else:
                    invalid.add((state.residual_key_owner, id(residual_record)))
                    valid_root = False

            def validate_task_item(
                item: object, *, current_root: ConcretePortScheduler = root
            ) -> None:
                if item is None or type(item) in (str, int, bool):
                    return
                if type(item) is SourceCellID:
                    current_root.sources.resolve(item)
                    return
                if type(item) is PortStateID:
                    current_root.resolve_port(item)
                    return
                if type(item) is ResidualBindingID:
                    current_root.resolve_residual(item)
                    return
                if type(item) is ProviderLayerID:
                    current_root.layers.resolve(item)
                    return
                if type(item) is RuntimeValueID:
                    current_root.validate_atom(item)
                    return
                if type(item) is FieldCellActionID:
                    current_root.adapter.validate_action(item)
                    return
                raise TypeError("concrete-port task contains an unknown typed item")

            for task_key, task_value in state.memo.items():
                valid = valid_root and type(task_key) is tuple and bool(task_key)
                try:
                    valid &= type(task_key[0]) is str
                    for task_item in task_key[1:]:
                        validate_task_item(task_item)
                    root.validate_atom(task_value)
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(task_key))
                else:
                    invalid.add((state.memo_owner, id(task_key)))
                    valid_root = False
            for virtual_index, virtual_record in state.virtual.items():
                valid = valid_root and type(virtual_index) is int
                valid &= type(virtual_record) is _VirtualInterface
                try:
                    root.adapter.validate_action(virtual_record.consumer)
                    valid &= type(
                        virtual_record.side
                    ) is int and virtual_record.side in (0, 1)
                    validate_virtual_transfer(
                        root.adapter,
                        virtual_record.consumer,
                        virtual_record.side,
                        virtual_record.outputs,
                    )
                    virtual_id = VirtualInterfaceID(
                        state.owner, state.virtual_kind, virtual_index
                    )
                    valid &= root.resolve_virtual(virtual_id) is virtual_record
                    valid &= state.virtual_keys.get(virtual_record) == virtual_index
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(virtual_record))
                    virtual_interfaces.add((state.virtual_owner, id(virtual_record)))
                else:
                    invalid.add((state.virtual_owner, id(virtual_record)))
                    valid_root = False
            for virtual_record, virtual_index in state.virtual_keys.items():
                valid = (
                    valid_root
                    and type(virtual_record) is _VirtualInterface
                    and type(virtual_index) is int
                    and state.virtual.get(virtual_index) is virtual_record
                )
                if valid:
                    approved.add(id(virtual_record))
                    virtual_interfaces.add(
                        (state.virtual_key_owner, id(virtual_record))
                    )
                else:
                    invalid.add((state.virtual_key_owner, id(virtual_record)))
                    valid_root = False
            for binding, virtual_interface in state.virtual_bindings.items():
                valid = valid_root and type(binding) is _VirtualBinding
                try:
                    root.adapter.validate_action(binding.parent)
                    children = root.adapter.children(binding.parent)
                    valid &= children is not None
                    if children is not None:
                        consumer = children[1]
                        valid &= root.adapter.children(consumer) is None
                        valid &= (
                            root.resolve_virtual(virtual_interface).consumer == consumer
                        )
                    valid &= type(binding.side) is int and binding.side in (0, 1)
                    valid &= type(binding.reverse) is bool
                    root.sources.resolve(binding.cell)
                    root.layers.validate_optional(binding.layer)
                    root.validate_atom(binding.anchor)
                    root.validate_atom(binding.argument)
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(binding))
                else:
                    invalid.add((state.virtual_binding_owner, id(binding)))
                    valid_root = False
            for layer_index, layer_node in layer_state.nodes.items():
                valid = (
                    valid_root
                    and type(layer_index) is int
                    and type(layer_node) is ProviderLayerNode
                )
                try:
                    valid &= (
                        root.layers.resolve(
                            ProviderLayerID(
                                layer_state.owner, layer_state.kind, layer_index
                            )
                        )
                        is layer_node
                    )
                    root.layers.validate_optional(layer_node.previous)
                    root.adapter.validate_action(layer_node.layer.action)
                    root.validate_atom(layer_node.layer.left)
                    root.validate_atom(layer_node.layer.right)
                    valid &= layer_state.keys.get(layer_node) == layer_index
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(layer_node))
                else:
                    invalid.add((layer_state.node_owner, id(layer_node)))
                    valid_root = False
            for layer_node, layer_index in layer_state.keys.items():
                valid = (
                    valid_root
                    and type(layer_node) is ProviderLayerNode
                    and type(layer_index) is int
                    and layer_state.nodes.get(layer_index) is layer_node
                )
                if valid:
                    approved.add(id(layer_node))
                else:
                    invalid.add((layer_state.key_owner, id(layer_node)))
                    valid_root = False
            if valid_root:
                approved.update(
                    id(store)
                    for _, store in virtual_stores + layer_stores + scheduler_stores
                )
        elif type(root) is RecursiveFieldImageArena:
            image_state = root.audit_snapshot()
            _, image_approved, image_invalid = audit_recursive_field_images(
                root, image_state, ledger, containers
            )
            approved.update(image_approved)
            invalid.update(image_invalid)
        elif type(root) is FieldTransferArena:
            transfer_state: FieldTransferAuditSnapshot = root.audit_snapshot()
            transfer_stores = (
                (transfer_state.node_owner, transfer_state.nodes),
                (transfer_state.key_owner, transfer_state.keys),
                (transfer_state.binding_owner, transfer_state.bindings),
                (transfer_state.observation_owner, transfer_state.observation_bindings),
            )
            valid_root = (
                transfer_state.ledger is ledger
                and transfer_state.owner is root.owner
                and all(
                    containers.get(owner) is store for owner, store in transfer_stores
                )
            )
            for transfer_id, transfer_record in transfer_state.nodes.items():
                valid = valid_root and type(transfer_id) is int and transfer_id >= 0
                valid &= type(transfer_record) is FieldTransferRecord
                try:
                    root.validate_record(transfer_record)
                    transfer_handle = FieldTransferID(
                        transfer_state.owner, transfer_state.transfer_kind, transfer_id
                    )
                    valid &= root.resolve(transfer_handle) is transfer_record
                    root.interfaces.resolve(transfer_record.interface)
                    geometry = root.geometries.resolve(transfer_record.geometry)
                    valid &= geometry.spatial_level == transfer_record.level
                    transfer_expected = FieldTransferKey(
                        transfer_record.level,
                        transfer_record.interface,
                        transfer_record.output,
                        transfer_record.geometry,
                    )
                    valid &= transfer_state.keys.get(transfer_expected) == transfer_id
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(transfer_record))
                else:
                    invalid.add((transfer_state.node_owner, id(transfer_record)))
            for transfer_semantic, transfer_id in transfer_state.keys.items():
                valid = (
                    type(transfer_semantic) is FieldTransferKey
                    and type(transfer_id) is int
                )
                valid &= transfer_id in transfer_state.nodes
                if valid:
                    transfer_record = transfer_state.nodes[transfer_id]
                    valid &= transfer_semantic == FieldTransferKey(
                        transfer_record.level,
                        transfer_record.interface,
                        transfer_record.output,
                        transfer_record.geometry,
                    )
                if valid:
                    approved.add(id(transfer_semantic))
                else:
                    invalid.add((transfer_state.key_owner, id(transfer_semantic)))
            for transfer_request, transfer_reference in transfer_state.bindings.items():
                valid = type(transfer_request) is FieldTransferRequestKey
                try:
                    root.validate_request(transfer_request)
                    transfer_record = root.resolve(transfer_reference)
                    valid &= (
                        root.interfaces.resolve(transfer_record.interface).signature
                        == transfer_request.signature
                    )
                    valid &= (
                        transfer_reference,
                        transfer_request.source,
                    ) in transfer_state.observation_bindings
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(transfer_request))
                else:
                    invalid.add((transfer_state.binding_owner, id(transfer_request)))
            for observation_key, marker in transfer_state.observation_bindings.items():
                valid = type(observation_key) is tuple and len(observation_key) == 2
                if valid:
                    transfer_reference, source = observation_key
                    try:
                        root.resolve(transfer_reference)
                        if type(source) is SourceCellID:
                            root.sources.resolve(source)
                        elif type(source) is SourceForestID:
                            root.sources.resolve_forest(source)
                        else:
                            valid = False
                        valid &= marker is None
                        valid &= any(
                            bound == transfer_reference and request.source == source
                            for request, bound in transfer_state.bindings.items()
                        )
                    except (TypeError, ValueError, IndexError, AttributeError):
                        valid = False
                if valid:
                    approved.add(id(observation_key))
                else:
                    invalid.add((transfer_state.observation_owner, id(observation_key)))
        elif type(root) is ProviderAbsorptionArena:
            provider_state = root.audit_snapshot()
            provider_stores = (
                (provider_state.node_owner, provider_state.nodes),
                (provider_state.key_owner, provider_state.keys),
                (provider_state.binding_owner, provider_state.bindings),
                (provider_state.point_owner, provider_state.points),
            )
            valid_root = (
                provider_state.ledger is ledger
                and provider_state.owner is root.owner
                and all(
                    containers.get(owner) is store for owner, store in provider_stores
                )
            )
            for local_id, provider_record in provider_state.nodes.items():
                valid = (
                    valid_root
                    and type(local_id) is int
                    and local_id >= 0
                    and type(provider_record) is ProviderAction
                )
                try:
                    root.validate_action_record(provider_record)
                    provider_id = ProviderActionID(
                        provider_state.owner, provider_state.action_kind, local_id
                    )
                    valid &= indexed_record_matches(
                        provider_id,
                        root.resolve,
                        provider_state.keys,
                        provider_record,
                        local_id,
                    )
                except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(provider_record))
                else:
                    invalid.add((provider_state.node_owner, id(provider_record)))
            for provider_key, local_id in provider_state.keys.items():
                valid = (
                    type(provider_key) is ProviderAction
                    and type(local_id) is int
                    and local_id in provider_state.nodes
                )
                if valid:
                    valid &= provider_state.nodes[local_id] is provider_key
                if valid:
                    approved.add(id(provider_key))
                else:
                    invalid.add((provider_state.key_owner, id(provider_key)))
            for provider_binding, marker in provider_state.bindings.items():
                valid = marker is None and valid_provider_occurrence(
                    root, provider_binding
                )
                if valid:
                    approved.add(id(provider_binding))
                else:
                    invalid.add((provider_state.binding_owner, id(provider_binding)))
            if len(provider_state.points) > 1:
                invalid.add((provider_state.point_owner, id(provider_state.points)))
            for provider_point_key, point_result in provider_state.points.items():
                audit_provider_point(
                    provider_point_key,
                    point_result,
                    ProviderPointKey,
                    provider_state.bindings.__contains__,
                    root.validate_boundary,
                    provider_state.point_owner,
                )
        elif type(root) is ProviderImageInputArena:
            input_approved, input_invalid = audit_provider_image_inputs(
                root,
                ledger,
                containers,
            )
            approved.update(input_approved)
            invalid.update(input_invalid)
        elif type(root) is ProviderFusedTransfer:
            fused_state = root.audit_snapshot()
            fused_stores = (
                (fused_state.binding_owner, fused_state.bindings),
                (fused_state.point_owner, fused_state.points),
                (fused_state.width_owner, fused_state.widths),
            )
            valid_root = fused_state.ledger is ledger and all(
                containers.get(owner) is store for owner, store in fused_stores
            )

            def valid_fused_binding(
                binding: object, *, current_root: ProviderFusedTransfer = root
            ) -> bool:
                if type(binding) is not FusedProviderBinding:
                    return False
                occurrence = binding.occurrence
                try:
                    return (
                        current_root.validate_binding_authority(binding) == occurrence
                    )
                except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                    return False

            for fused_binding, marker in fused_state.bindings.items():
                valid = (
                    valid_root and marker is None and valid_fused_binding(fused_binding)
                )
                if valid:
                    approved.add(id(fused_binding))
                else:
                    invalid.add((fused_state.binding_owner, id(fused_binding)))
            if len(fused_state.points) > 1:
                invalid.add((fused_state.point_owner, id(fused_state.points)))
            for fused_point_key, point_result in fused_state.points.items():
                audit_provider_point(
                    fused_point_key,
                    point_result,
                    ProviderFusedPointKey,
                    fused_state.bindings.__contains__,
                    root.validate_boundary,
                    fused_state.point_owner,
                )
            for width_key, width_result in fused_state.widths.items():
                valid = (
                    type(width_key) is ProviderFusedWidthKey
                    and width_key.binding in fused_state.bindings
                    and type(width_result) is int
                    and width_result >= 0
                )
                try:
                    root.validate_boundary(width_key.left)
                    root.validate_boundary(width_key.right)
                except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(width_key))
                else:
                    invalid.add((fused_state.width_owner, id(width_key)))
        elif type(root) is DiamondQuotientArena:
            diamond_state: DiamondQuotientAuditSnapshot = root.audit_snapshot()
            quotient_stores = (
                (diamond_state.signature_owner, diamond_state.signatures),
                (diamond_state.signature_key_owner, diamond_state.signature_keys),
                (diamond_state.node_owner, diamond_state.nodes),
                (diamond_state.key_owner, diamond_state.keys),
                (diamond_state.normalization_owner, diamond_state.normalizations),
                (diamond_state.binding_owner, diamond_state.parents),
            )
            all_valid = (
                diamond_state.ledger is ledger
                and diamond_state.owner is root.owner
                and type(diamond_state.next_node) is int
                and diamond_state.next_node >= 0
                and len(diamond_state.nodes) <= diamond_state.next_node
                and len(diamond_state.keys) == len(diamond_state.nodes)
                and all(
                    type(local_id) is int and 0 <= local_id < diamond_state.next_node
                    for local_id in diamond_state.nodes
                )
                and all(
                    containers.get(owner) is store for owner, store in quotient_stores
                )
            )
            for index, signature_record in enumerate(diamond_state.signatures):
                valid = type(signature_record) is MacroInterface
                diamond_signature_handle: PortSignatureID | None = None
                retained_handle: object = None
                try:
                    root.validate_interface_record(signature_record)
                    diamond_signature_handle = PortSignatureID(
                        root.owner,
                        root.signature_kind,
                        index,
                    )
                    valid &= (
                        root.interface(diamond_signature_handle) is signature_record
                    )
                    valid &= (
                        diamond_state.signature_keys.get(signature_record)
                        == diamond_signature_handle
                    )
                    retained_handle = diamond_state.signature_keys.get(signature_record)
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid and diamond_signature_handle is not None:
                    approved.update(
                        (
                            id(signature_record),
                            id(diamond_signature_handle),
                            id(retained_handle),
                        )
                    )
                else:
                    invalid.add((diamond_state.signature_owner, id(signature_record)))
                    all_valid = False
            for index, quotient_record in diamond_state.nodes.items():
                valid = type(quotient_record) is QuotientRecord
                quotient_handle: LocalInterfaceID | None = None
                try:
                    valid &= type(quotient_record.components) is MacroComponents
                    root.validate_quotient_record(quotient_record)
                    quotient_handle = LocalInterfaceID(
                        root.owner,
                        root.interface_kind,
                        index,
                    )
                    valid &= root.resolve(quotient_handle) is quotient_record
                    valid &= diamond_state.keys.get(quotient_record) == quotient_handle
                except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                    valid = False
                if valid and quotient_handle is not None:
                    approved.update(
                        (
                            id(quotient_record),
                            id(quotient_record.components),
                            id(quotient_handle),
                            id(quotient_record.signature),
                        )
                    )
                else:
                    invalid.add((diamond_state.node_owner, id(quotient_record)))
                    all_valid = False
            for request, result in diamond_state.normalizations.items():
                valid = type(request) is QuotientRecord
                try:
                    root.validate_quotient_record(request)
                    result_record = root.resolve(result)
                    valid &= result_record.signature == request.signature
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.update((id(request), id(request.components), id(result)))
                else:
                    invalid.add((diamond_state.normalization_owner, id(request)))
                    all_valid = False
            for parent_request, result in diamond_state.parents.items():
                valid = type(parent_request) is DiamondKey
                try:
                    root.validate_parent_key(parent_request)
                    result_record = root.resolve(result)
                    valid &= result_record.signature == parent_request.signature
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.update((id(parent_request), id(result)))
                else:
                    invalid.add((diamond_state.binding_owner, id(parent_request)))
                    all_valid = False
            if all_valid:
                approved.update(id(store) for _, store in quotient_stores)
    return FieldImagePayloadAudit(
        frozenset(approved), frozenset(invalid), frozenset(virtual_interfaces)
    )


__all__ = ["FieldImagePayloadAudit", "audit_field_image_payloads"]

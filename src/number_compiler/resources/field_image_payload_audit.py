"""Read-only ownership audit for recursive field images and source cells."""

from __future__ import annotations

from dataclasses import dataclass
from typing import cast

from number_compiler.resources.field_image_domain_audit import indexed_record_matches
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_contracts import PayloadAuditContractAudit


@dataclass(frozen=True, slots=True)
class FieldImagePayloadAudit:
    approved: frozenset[int]
    invalid: frozenset[tuple[int, int]]


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
        return FieldImagePayloadAudit(frozenset(live_approved), frozenset(live_invalid))

    from number_compiler.arithmetic.fields.dyadic_tile import DyadicTile
    from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
    from number_compiler.hashlife.actions.field_actions import (
        FieldCellActionID,
        FieldGeometry,
        FieldGeometryArena,
    )
    from number_compiler.hashlife.execution.continuations.concrete_directed_residual import (
        validate_residual,
    )
    from number_compiler.hashlife.execution.continuations.concrete_port_records import (
        ComposedPort,
        PortAtom,
        PortStateID,
        Residual,
        ResidualBindingID,
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
        _PointKey,
    )
    from number_compiler.hashlife.execution.continuations.provider_fused_transfer import (
        FusedProviderBinding,
        ProviderFusedTransfer,
        _FusedPointKey,
        _FusedWidthKey,
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
        FieldImageRecord,
        ImageRequestKey,
        RecursiveFieldImageArena,
        SourceCellArena,
        SourceCellID,
        SourceForestID,
        SourceForestRecord,
        _ImageKey,
    )
    from number_compiler.hashlife.execution.field_transfers import (
        FieldTransferArena,
        FieldTransferRecord,
        FieldTransferRequestKey,
        _TransferKey,
    )
    from number_compiler.hashlife.interfaces.diamond_quotient import (
        DiamondKey,
        DiamondQuotientArena,
        LocalInterfaceID,
        MacroComponents,
        MacroInterface,
        QuotientRecord,
    )
    from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
    from number_compiler.hashlife.tiles.tiles import TileArena
    from number_compiler.resources.field_image_domain_audit import (
        audit_field_image_domains,
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
            provider = providers.resolve(binding.provider)
            source_extent = providers.sources.binding_extent(binding.source)
            providers._validate_bound_output(binding.output)
            providers._validate_bound_interface(binding.interface)
            if binding.active_extent is not None and (
                type(binding.active_extent) is not int
                or not 0 <= binding.active_extent <= source_extent
            ):
                return False
            if binding.image is not None:
                providers._validate_image_binding(
                    binding.image,
                    binding.source,
                    provider.action,
                    binding.output,
                    binding.interface,
                    binding.active_extent,
                    binding.context,
                )
            elif binding.active_extent is not None or binding.context is not None:
                return False
        except (TypeError, ValueError, IndexError, KeyError, AttributeError):
            return False
        return True

    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
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
            source_stores = (
                (root._node_owner, root._nodes),
                (root._key_owner, root._keys),
                (root._forest_node_owner, root._forests),
                (root._forest_key_owner, root._forest_keys),
            )
            valid_root = root.ledger is ledger and all(
                containers.get(owner) is store for owner, store in source_stores
            )
            for index, source_record in enumerate(root._nodes):
                valid = valid_root
                try:
                    valid &= root.resolve(root._handle(index)) is source_record
                    source_record.__post_init__()
                    valid &= root._keys.get(source_record.source_tile) == index
                    if source_record.level:
                        valid &= 0 <= source_record.left < index
                        valid &= 0 <= source_record.right < index
                        if valid:
                            left = root._nodes[source_record.left]
                            right = root._nodes[source_record.right]
                            valid &= source_record.source_tile.left is left.source_tile
                            valid &= (
                                source_record.source_tile.right is right.source_tile
                            )
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(source_record))
                else:
                    invalid.add((root._node_owner, id(source_record)))
            for key, index in root._keys.items():
                valid = (
                    type(key) is DyadicTile
                    and type(index) is int
                    and 0 <= index < len(root._nodes)
                )
                if valid:
                    record = root._nodes[index]
                    valid &= key is record.source_tile
                if valid:
                    approved.add(id(key))
                else:
                    invalid.add((root._key_owner, id(key)))
            for index, forest in enumerate(root._forests):
                valid = valid_root and type(forest) is SourceForestRecord
                try:
                    forest.__post_init__()
                    valid &= root.resolve_forest(root._forest_handle(index)) is forest
                    valid &= (
                        sum(root.resolve(cell).width for cell in forest.cells)
                        == forest.extent
                    )
                    forest_key = (
                        tuple(cell.local_id for cell in forest.cells),
                        forest.extent,
                    )
                    valid &= root._forest_keys.get(forest_key) == index
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(forest))
                else:
                    invalid.add((root._forest_node_owner, id(forest)))
            for forest_key, index in root._forest_keys.items():
                valid = (
                    type(forest_key) is tuple
                    and len(forest_key) == 2
                    and type(index) is int
                    and 0 <= index < len(root._forests)
                )
                if valid:
                    forest = root._forests[index]
                    valid &= forest_key == (
                        tuple(cell.local_id for cell in forest.cells),
                        forest.extent,
                    )
                if valid:
                    approved.add(id(forest_key))
                else:
                    invalid.add((root._forest_key_owner, id(forest_key)))
        elif type(root) is FieldGeometryArena:
            geometry_stores = (
                (root._node_owner, root._nodes),
                (root._key_owner, root._keys),
            )
            valid_root = root.ledger is ledger and all(
                containers.get(owner) is store for owner, store in geometry_stores
            )
            for index, geometry in enumerate(root._nodes):
                try:
                    geometry.__post_init__()
                    valid = valid_root and root.resolve(root._handle(index)) is geometry
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(geometry))
                else:
                    invalid.add((root._node_owner, id(geometry)))
            for geometry_key, index in root._keys.items():
                valid = valid_root and type(geometry_key) is FieldGeometry
                valid &= type(index) is int and 0 <= index < len(root._nodes)
                if valid:
                    valid &= root._nodes[index] is geometry_key
                if valid:
                    approved.add(id(geometry_key))
                else:
                    invalid.add((root._key_owner, id(geometry_key)))
        elif type(root) is ConcretePortScheduler:
            virtual_stores = (
                (root._virtual_owner, root._virtual),
                (root._virtual_key_owner, root._virtual_keys),
                (root._virtual_binding_owner, root._virtual_bindings),
            )
            layer_stores = (
                (root.layers._node_owner, root.layers._nodes),
                (root.layers._key_owner, root.layers._keys),
            )
            state_stores = (
                (root._port_owner, root._ports),
                (root._port_key_owner, root._port_keys),
                (root._residual_owner, root._residuals),
                (root._residual_key_owner, root._residual_keys),
                (root._memo_owner, root._memo),
            )
            valid_root = root.ledger is ledger and all(
                containers.get(owner) is store
                for owner, store in virtual_stores + layer_stores + state_stores
            )
            for port_index, port_record in root._ports.items():
                valid = (
                    valid_root
                    and type(port_index) is int
                    and type(port_record) is ComposedPort
                )
                try:
                    root.adapter.validate_action(port_record.action)
                    root._validate_side(port_record.side)
                    root._validate_atom(port_record.anchor)
                    root.resolve_residual(port_record.residual)
                    valid &= (
                        root.resolve_port(
                            PortStateID(root.owner, root._PORT_KIND, port_index),
                        )
                        is port_record
                    )
                    valid &= root._port_keys.get(port_record) == port_index
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(port_record))
                else:
                    invalid.add((root._port_owner, id(port_record)))
                    valid_root = False
            for port_record, port_index in root._port_keys.items():
                valid = (
                    valid_root
                    and type(port_record) is ComposedPort
                    and type(port_index) is int
                    and root._ports.get(port_index) is port_record
                )
                if valid:
                    approved.add(id(port_record))
                else:
                    invalid.add((root._port_key_owner, id(port_record)))
                    valid_root = False
            for residual_index, residual_record in root._residuals.items():
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
                                root.owner,
                                root._RESIDUAL_KIND,
                                residual_index,
                            )
                        )
                        is residual_record
                    )
                    valid &= root._residual_keys.get(residual_record) == residual_index
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(residual_record))
                else:
                    invalid.add((root._residual_owner, id(residual_record)))
                    valid_root = False
            for residual_record, residual_index in root._residual_keys.items():
                valid = (
                    valid_root
                    and type(residual_record) is Residual
                    and type(residual_index) is int
                    and root._residuals.get(residual_index) is residual_record
                )
                if valid:
                    approved.add(id(residual_record))
                else:
                    invalid.add((root._residual_key_owner, id(residual_record)))
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
                    current_root._validate_atom(item)
                    return
                current_root.adapter.validate_action(cast(FieldCellActionID, item))

            for task_key, task_value in root._memo.items():
                valid = valid_root and type(task_key) is tuple and bool(task_key)
                try:
                    valid &= type(task_key[0]) is str
                    for task_item in task_key[1:]:
                        validate_task_item(task_item)
                    root._validate_atom(task_value)
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(task_key))
                else:
                    invalid.add((root._memo_owner, id(task_key)))
                    valid_root = False
            for virtual_index, virtual_record in root._virtual.items():
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
                    valid &= (
                        root.resolve_virtual(root._virtual_id(virtual_index))
                        is virtual_record
                    )
                    valid &= root._virtual_keys.get(virtual_record) == virtual_index
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(virtual_record))
                else:
                    invalid.add((root._virtual_owner, id(virtual_record)))
                    valid_root = False
            for virtual_record, virtual_index in root._virtual_keys.items():
                valid = (
                    valid_root
                    and type(virtual_record) is _VirtualInterface
                    and type(virtual_index) is int
                    and root._virtual.get(virtual_index) is virtual_record
                )
                if valid:
                    approved.add(id(virtual_record))
                else:
                    invalid.add((root._virtual_key_owner, id(virtual_record)))
                    valid_root = False
            for binding, virtual_interface in root._virtual_bindings.items():
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
                    root._validate_atom(binding.anchor)
                    root._validate_atom(binding.argument)
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(binding))
                else:
                    invalid.add((root._virtual_binding_owner, id(binding)))
                    valid_root = False
            for layer_index, layer_node in root.layers._nodes.items():
                valid = (
                    valid_root
                    and type(layer_index) is int
                    and type(layer_node) is ProviderLayerNode
                )
                try:
                    valid &= (
                        root.layers.resolve(
                            root.layers._handle(layer_index),
                        )
                        is layer_node
                    )
                    root.layers.validate_optional(layer_node.previous)
                    root.adapter.validate_action(layer_node.layer.action)
                    root._validate_atom(cast(PortAtom, layer_node.layer.left))
                    root._validate_atom(cast(PortAtom, layer_node.layer.right))
                    valid &= root.layers._keys.get(layer_node) == layer_index
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(layer_node))
                else:
                    invalid.add((root.layers._node_owner, id(layer_node)))
                    valid_root = False
            for layer_node, layer_index in root.layers._keys.items():
                valid = (
                    valid_root
                    and type(layer_node) is ProviderLayerNode
                    and type(layer_index) is int
                    and root.layers._nodes.get(layer_index) is layer_node
                )
                if valid:
                    approved.add(id(layer_node))
                else:
                    invalid.add((root.layers._key_owner, id(layer_node)))
                    valid_root = False
            if valid_root:
                approved.update(
                    id(store)
                    for _, store in virtual_stores + layer_stores + state_stores
                )
        elif type(root) is RecursiveFieldImageArena:
            image_stores = (
                (root._domain_owner, root._domains),
                (root._node_owner, root._nodes),
                (root._key_owner, root._keys),
                (root._binding_owner, root._bindings),
            )
            valid_root = root.ledger is ledger and all(
                containers.get(owner) is store for owner, store in image_stores
            )
            domains_valid, domain_approved, domain_invalid = audit_field_image_domains(
                root, ledger, containers
            )
            valid_root &= domains_valid
            approved.update(domain_approved)
            invalid.update(domain_invalid)
            for index, image_record in root._nodes.items():
                valid = (
                    valid_root
                    and type(index) is int
                    and type(image_record) is FieldImageRecord
                )
                try:
                    image_record.__post_init__()
                    valid &= root.resolve(root._handle(index)) is image_record
                    root.resolve_interface(image_record.interface)
                    geometry = root.geometries.resolve(image_record.geometry)
                    valid &= geometry.spatial_level == image_record.level
                    root.validate_output(image_record.output)
                    if image_record.left is not None and image_record.right is not None:
                        valid &= image_record.left.local_id < index
                        valid &= image_record.right.local_id < index
                        if valid:
                            left_image_record = root.resolve(image_record.left)
                            right_image_record = root.resolve(image_record.right)
                            valid &= left_image_record.level < image_record.level
                            valid &= right_image_record.level < image_record.level
                    else:
                        valid &= image_record.left is image_record.right is None
                    semantic = _ImageKey(
                        image_record.level,
                        image_record.left,
                        image_record.right,
                        image_record.interface,
                        image_record.output,
                        image_record.geometry,
                        image_record.summary,
                    )
                    valid &= root._keys.get(semantic) == index
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(image_record))
                else:
                    invalid.add((root._node_owner, id(image_record)))
            for request_key, reference in root._bindings.items():
                valid = type(request_key) is ImageRequestKey
                try:
                    root._validate_request(request_key)
                    image_record = root.resolve(reference)
                    valid &= (
                        root.resolve_interface(image_record.interface).signature
                        == request_key.signature
                    )
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(request_key))
                else:
                    invalid.add((root._binding_owner, id(request_key)))
            for semantic_key, index in root._keys.items():
                valid = type(semantic_key) is _ImageKey and type(index) is int
                valid &= index in root._nodes
                if valid:
                    recursive_image = root._nodes[index]
                    expected = _ImageKey(
                        recursive_image.level,
                        recursive_image.left,
                        recursive_image.right,
                        recursive_image.interface,
                        recursive_image.output,
                        recursive_image.geometry,
                        recursive_image.summary,
                    )
                    valid &= semantic_key == expected
                if valid:
                    approved.add(id(semantic_key))
                else:
                    invalid.add((root._key_owner, id(semantic_key)))
            image_owners = {root._node_owner, root._key_owner, root._binding_owner}
            if valid_root and not any(owner in image_owners for owner, _ in invalid):
                approved.update(id(store) for _, store in image_stores)
        elif type(root) is FieldTransferArena:
            transfer_stores = (
                (root._node_owner, root._nodes),
                (root._key_owner, root._keys),
                (root._binding_owner, root._bindings),
                (root._observation_owner, root._observation_bindings),
            )
            valid_root = root.ledger is ledger and all(
                containers.get(owner) is store for owner, store in transfer_stores
            )
            for transfer_id, transfer_record in root._nodes.items():
                valid = valid_root and type(transfer_id) is int and transfer_id >= 0
                valid &= type(transfer_record) is FieldTransferRecord
                try:
                    transfer_record.__post_init__()
                    valid &= root.resolve(root._handle(transfer_id)) is transfer_record
                    root.interfaces.resolve(transfer_record.interface)
                    geometry = root.geometries.resolve(transfer_record.geometry)
                    valid &= geometry.spatial_level == transfer_record.level
                    transfer_record.output.validate(root.output_owner, root.output_kind)
                    root._output_validate(transfer_record.output)
                    transfer_expected = _TransferKey(
                        transfer_record.level,
                        transfer_record.interface,
                        transfer_record.output,
                        transfer_record.geometry,
                    )
                    valid &= root._keys.get(transfer_expected) == transfer_id
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(transfer_record))
                else:
                    invalid.add((root._node_owner, id(transfer_record)))
            for transfer_semantic, transfer_id in root._keys.items():
                valid = (
                    type(transfer_semantic) is _TransferKey and type(transfer_id) is int
                )
                valid &= transfer_id in root._nodes
                if valid:
                    transfer_record = root._nodes[transfer_id]
                    valid &= transfer_semantic == _TransferKey(
                        transfer_record.level,
                        transfer_record.interface,
                        transfer_record.output,
                        transfer_record.geometry,
                    )
                if valid:
                    approved.add(id(transfer_semantic))
                else:
                    invalid.add((root._key_owner, id(transfer_semantic)))
            for transfer_request, transfer_reference in root._bindings.items():
                valid = type(transfer_request) is FieldTransferRequestKey
                try:
                    root._validate_request(transfer_request)
                    transfer_record = root.resolve(transfer_reference)
                    valid &= (
                        root.interfaces.resolve(transfer_record.interface).signature
                        == transfer_request.signature
                    )
                    valid &= (
                        transfer_reference,
                        transfer_request.source,
                    ) in root._observation_bindings
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(transfer_request))
                else:
                    invalid.add((root._binding_owner, id(transfer_request)))
            for observation_key, marker in root._observation_bindings.items():
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
                            for request, bound in root._bindings.items()
                        )
                    except (TypeError, ValueError, IndexError, AttributeError):
                        valid = False
                if valid:
                    approved.add(id(observation_key))
                else:
                    invalid.add((root._observation_owner, id(observation_key)))
        elif type(root) is ProviderAbsorptionArena:
            provider_stores = (
                (root._node_owner, root._nodes),
                (root._key_owner, root._keys),
                (root._binding_owner, root._bindings),
                (root._point_owner, root._points),
            )
            valid_root = root.ledger is ledger and all(
                containers.get(owner) is store for owner, store in provider_stores
            )
            for local_id, provider_record in root._nodes.items():
                valid = (
                    valid_root
                    and type(local_id) is int
                    and local_id >= 0
                    and type(provider_record) is ProviderAction
                )
                try:
                    provider_record.__post_init__()
                    root._validate_output(provider_record.output)
                    root._validate_interface(provider_record.interface)
                    root._validate_action(provider_record.action)
                    provider_id = ProviderActionID(root.owner, root._KIND, local_id)
                    valid &= indexed_record_matches(
                        provider_id, root.resolve, root._keys, provider_record, local_id
                    )
                except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(provider_record))
                else:
                    invalid.add((root._node_owner, id(provider_record)))
            for provider_key, local_id in root._keys.items():
                valid = (
                    type(provider_key) is ProviderAction
                    and type(local_id) is int
                    and local_id in root._nodes
                )
                if valid:
                    valid &= root._nodes[local_id] is provider_key
                if valid:
                    approved.add(id(provider_key))
                else:
                    invalid.add((root._key_owner, id(provider_key)))
            for provider_binding, marker in root._bindings.items():
                valid = marker is None and valid_provider_occurrence(
                    root, provider_binding
                )
                if valid:
                    approved.add(id(provider_binding))
                else:
                    invalid.add((root._binding_owner, id(provider_binding)))
            if len(root._points) > 1:
                invalid.add((root._point_owner, id(root._points)))
            for provider_point_key, point_result in root._points.items():
                valid = (
                    type(provider_point_key) is _PointKey
                    and provider_point_key.binding in root._bindings
                    and type(provider_point_key.coordinate) is int
                    and provider_point_key.coordinate >= 0
                    and type(point_result) is int
                )
                try:
                    root._validate_boundary(provider_point_key.left)
                    root._validate_boundary(provider_point_key.right)
                except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(provider_point_key))
                else:
                    invalid.add((root._point_owner, id(provider_point_key)))
        elif type(root) is ProviderImageInputArena:
            input_approved, input_invalid = audit_provider_image_inputs(
                root,
                ledger,
                containers,
            )
            approved.update(input_approved)
            invalid.update(input_invalid)
        elif type(root) is ProviderFusedTransfer:
            fused_stores = (
                (root._binding_owner, root._bindings),
                (root._point_owner, root._points),
                (root._width_owner, root._widths),
            )
            valid_root = root.ledger is ledger and all(
                containers.get(owner) is store for owner, store in fused_stores
            )

            def valid_fused_binding(
                binding: object, *, current_root: ProviderFusedTransfer = root
            ) -> bool:
                if type(binding) is not FusedProviderBinding:
                    return False
                occurrence = binding.occurrence
                if not valid_provider_occurrence(current_root.providers, occurrence):
                    return False
                return occurrence in current_root.providers._bindings

            for fused_binding, marker in root._bindings.items():
                valid = (
                    valid_root and marker is None and valid_fused_binding(fused_binding)
                )
                if valid:
                    approved.add(id(fused_binding))
                else:
                    invalid.add((root._binding_owner, id(fused_binding)))
            if len(root._points) > 1:
                invalid.add((root._point_owner, id(root._points)))
            for fused_point_key, point_result in root._points.items():
                valid = (
                    type(fused_point_key) is _FusedPointKey
                    and fused_point_key.binding in root._bindings
                    and type(fused_point_key.coordinate) is int
                    and fused_point_key.coordinate >= 0
                    and type(point_result) is int
                )
                try:
                    root.providers._validate_boundary(fused_point_key.left)
                    root.providers._validate_boundary(fused_point_key.right)
                except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(fused_point_key))
                else:
                    invalid.add((root._point_owner, id(fused_point_key)))
            for width_key, width_result in root._widths.items():
                valid = (
                    type(width_key) is _FusedWidthKey
                    and width_key.binding in root._bindings
                    and type(width_result) is int
                    and width_result >= 0
                )
                try:
                    root.providers._validate_boundary(width_key.left)
                    root.providers._validate_boundary(width_key.right)
                except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(width_key))
                else:
                    invalid.add((root._width_owner, id(width_key)))
        elif type(root) is DiamondQuotientArena:
            quotient_stores = (
                (root._signature_owner, root._signatures),
                (root._signature_key_owner, root._signature_keys),
                (root._node_owner, root._nodes),
                (root._key_owner, root._keys),
                (root._normalization_owner, root._normalizations),
                (root._binding_owner, root._parents),
            )
            all_valid = (
                root.ledger is ledger
                and type(root._next_node) is int
                and root._next_node >= 0
                and len(root._nodes) <= root._next_node
                and len(root._keys) == len(root._nodes)
                and all(
                    type(local_id) is int and 0 <= local_id < root._next_node
                    for local_id in root._nodes
                )
                and all(
                    containers.get(owner) is store for owner, store in quotient_stores
                )
            )
            for index, signature_record in enumerate(root._signatures):
                valid = type(signature_record) is MacroInterface
                diamond_signature_handle: PortSignatureID | None = None
                retained_handle: object = None
                try:
                    root._validate_interface(signature_record)
                    diamond_signature_handle = PortSignatureID(
                        root.owner,
                        "diamond-semantic-signature",
                        index,
                    )
                    valid &= (
                        root.interface(diamond_signature_handle) is signature_record
                    )
                    valid &= (
                        root._signature_keys.get(signature_record)
                        == diamond_signature_handle
                    )
                    retained_handle = root._signature_keys.get(signature_record)
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
                    invalid.add((root._signature_owner, id(signature_record)))
                    all_valid = False
            for index, quotient_record in root._nodes.items():
                valid = type(quotient_record) is QuotientRecord
                quotient_handle: LocalInterfaceID | None = None
                try:
                    valid &= type(quotient_record.components) is MacroComponents
                    root._validate_components(
                        quotient_record.signature,
                        quotient_record.components,
                    )
                    quotient_handle = LocalInterfaceID(
                        root.owner,
                        "diamond-quotient",
                        index,
                    )
                    valid &= root.resolve(quotient_handle) is quotient_record
                    valid &= root._keys.get(quotient_record) == quotient_handle
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
                    invalid.add((root._node_owner, id(quotient_record)))
                    all_valid = False
            for request, result in root._normalizations.items():
                valid = type(request) is QuotientRecord
                try:
                    root._validate_components(request.signature, request.components)
                    result_record = root.resolve(result)
                    valid &= result_record.signature == request.signature
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.update((id(request), id(request.components), id(result)))
                else:
                    invalid.add((root._normalization_owner, id(request)))
                    all_valid = False
            for parent_request, result in root._parents.items():
                valid = type(parent_request) is DiamondKey
                try:
                    root._validate_key(parent_request)
                    result_record = root.resolve(result)
                    valid &= result_record.signature == parent_request.signature
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.update((id(parent_request), id(result)))
                else:
                    invalid.add((root._binding_owner, id(parent_request)))
                    all_valid = False
            if all_valid:
                approved.update(id(store) for _, store in quotient_stores)
    return FieldImagePayloadAudit(frozenset(approved), frozenset(invalid))


__all__ = ["FieldImagePayloadAudit", "audit_field_image_payloads"]

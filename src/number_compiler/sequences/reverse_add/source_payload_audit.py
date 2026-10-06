"""Independent retained-payload audit for the reverse/add source adapter."""

from __future__ import annotations

from collections.abc import Iterable, Mapping, Sequence, Sized
from hashlib import sha256
from typing import cast

from number_compiler.resources.ledger import (
    OwnedMemo,
    ResourceInventory,
    ResourceLedger,
)
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditEntry,
    PayloadAuditStoreBinding,
)
from number_compiler.resources.reverse_source_payload_audit import (
    ReverseSourcePayloadAudit,
)
from number_compiler.sequences.reverse_add.source_audit_bindings import (
    nested_source_store_bindings,
    source_audit_owners,
)


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
        and not item.disposed
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
    # Keep unrelated ledgers independent of the reverse runtime imports below.
    # This is only an import gate; every admitted root still passes the exact
    # arena, owner, and authority checks in the audit body.
    if not any(
        type(root).__module__.startswith("number_compiler.sequences.reverse_add.")
        for root in roots
    ):
        return ReverseSourcePayloadAudit(frozenset(), frozenset(), frozenset())

    from number_compiler.arithmetic.carry.carry_monoid import CarryFn
    from number_compiler.arithmetic.contracts.exact_tree_context import (
        OriginalSourceConstruction,
    )
    from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
    from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
    from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
    from number_compiler.hashlife.actions.field_actions import (
        FieldCellActionID,
        FieldGeometry,
        FieldGeometryArena,
    )
    from number_compiler.hashlife.execution.continuations.higher_interfaces import (
        HigherMorphismSort,
        HigherPort,
    )
    from number_compiler.hashlife.execution.continuations.higher_macro_composer import (
        HigherSpatialMacroComposer,
    )
    from number_compiler.hashlife.execution.continuations.higher_types import (
        FieldStateSort,
        FieldSymbolSort,
    )
    from number_compiler.hashlife.execution.source_bound_images import (
        SourceBoundSchedulerCore,
        SourceImageID,
        _ImageRecord,
    )
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
    from number_compiler.sequences.reverse_add.higher_interface import (
        ReverseHigherInterfaceCompilation,
    )
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairOutputOccurrence,
        ReversePairQ19OutputOwner,
    )
    from number_compiler.sequences.reverse_add.recursive_adapters import (
        _ReverseRecursiveFieldAdapter,
    )
    from number_compiler.sequences.reverse_add.recursive_cutover import (
        ReverseRecursiveOccurrence,
        ReverseRecursiveTemporalCutover,
    )
    from number_compiler.sequences.reverse_add.source_actions import (
        _ReverseSourceRecord,
    )
    from number_compiler.sequences.reverse_add.source_images import (
        MAX_COMPLETED_CHILD_FALLBACK_STEPS,
        ReverseActionArena,
        ReverseActionID,
        ReverseActionNode,
        ReverseImagePayload,
        ReverseSource,
        ReverseSourceImageWorkspace,
        _ReverseSourceImageAdapter,
    )
    from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts

    owners = source_audit_owners(roots)
    inventory: dict[int, ResourceInventory] = {}
    for owner in owners:
        try:
            inventory[owner] = ledger.inventory_owner(owner)
        except (IndexError, TypeError, ValueError):
            continue
    containers = {owner: containers.get(owner) for owner in owners}
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
                approved.update((id(key), id(value)))
            else:
                invalid.add((owner, id(key)))
                invalid.add((owner, id(value)))
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
            and len(authority) == 9
            and authority[0] is ledger
            and authority[1] is actions
            and authority[2] is root.source
            and authority[3] is root.root_action
            and authority[4] is root.scheduler
            and authority[5] is root.adapter
            and authority[6] == root.steps
            and authority[7] == root.base
            and (
                authority[8] is None
                or authority[8] is root.adapter._recursive_construction
            )
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
        recursive_store = getattr(root.adapter, "_recursive_occurrences", None)
        recursive_owner = getattr(recursive_store, "owner", -1)
        occurrence_memo = (
            cast(OwnedMemo[int, ReverseRecursiveOccurrence], recursive_store)
            if type(recursive_store) is OwnedMemo
            else None
        )
        recursive_store_valid = _store_valid(
            recursive_owner,
            recursive_store,
            "reverse_recursive_occurrence_binding",
            containers,
            inventory,
        )
        valid &= recursive_store_valid and occurrence_memo is not None
        recursive = getattr(root.adapter, "_recursive", None)
        construction = getattr(root.adapter, "_recursive_construction", None)
        if construction is not None:
            try:
                if type(construction) is not OriginalSourceConstruction:
                    raise TypeError("reverse source construction has another owner")
                exact_pair_source = construction.validate_source()
                original = actions.source(root.source)
                maximum_steps = root.adapter._recursive_maximum_steps
                bounded_horizon = (
                    type(root.steps) is int
                    and type(maximum_steps) is int
                    and 3
                    <= root.steps
                    <= maximum_steps
                    <= MAX_COMPLETED_CHILD_FALLBACK_STEPS
                )
                expected_extent = (
                    1
                    << ((max(1, len(original.digits) + maximum_steps) - 1).bit_length())
                    if bounded_horizon
                    else None
                )
                recursive_authority_valid = (
                    exact_pair_source.base == original.base
                    and exact_pair_source.orbit == "reverse-add-pair"
                    and exact_pair_source.blank == 2 * original.base - 1
                    and exact_pair_source.extent == expected_extent
                    and exact_pair_source.alphabet_size == 2 * original.base
                    and len(exact_pair_source.digits) == len(original.digits)
                    and all(
                        exact_pair_source.digits[index]
                        == original.digits[index]
                        + original.digits[len(original.digits) - index - 1]
                        for index in range(len(original.digits))
                    )
                    and bounded_horizon
                )
            except (TypeError, ValueError, IndexError, AttributeError):
                recursive_authority_valid = False
            valid &= recursive_authority_valid
        else:
            valid &= recursive is None and not recursive_store
        if recursive is not None:
            recursive_valid = (
                type(recursive) is ReverseRecursiveTemporalCutover
                and recursive.ledger is ledger
                and recursive.source.owner is recursive.sources.owner
                and recursive.maximum_steps == root.adapter._recursive_maximum_steps
                and recursive.maximum_steps >= root.steps
                and root.adapter._recursive_source is actions.source(root.source)
            )
            if recursive_valid and construction is not None:
                recursive_valid &= (
                    recursive.source_geometry._construction.source
                    == construction.validate_source()
                    and recursive.extent == construction.validate_source().extent
                )
            if recursive_valid:
                valid &= recursive_valid
                recognized.add(id(recursive))
                occurrence_items = (
                    occurrence_memo.items() if occurrence_memo is not None else ()
                )
                for steps, occurrence in occurrence_items:
                    recognized.add(id(occurrence))
                    recognized.add(id(steps))
                    occurrence_valid = (
                        type(steps) is int
                        and type(occurrence) is ReverseRecursiveOccurrence
                        and occurrence.temporal_steps == steps
                        and occurrence.source is recursive.source
                    )
                    try:
                        recursive.validate_occurrence(occurrence)
                        expected_action = recursive._pair_actions.get(steps)
                        occurrence_valid &= (
                            expected_action is not None
                            and occurrence.action == expected_action
                            and occurrence._authority is recursive._occurrence_authority
                        )
                    except (
                        TypeError,
                        ValueError,
                        IndexError,
                        KeyError,
                        AttributeError,
                    ):
                        occurrence_valid = False
                    if occurrence_valid:
                        approved.update((id(steps), id(occurrence)))
                    else:
                        valid = False
                        invalid.add((recursive_owner, id(steps)))
                        invalid.add((recursive_owner, id(occurrence)))
                core_adapter = recursive.adapter
                composer_store = getattr(core_adapter, "_composers", None)
                composer_owner = getattr(composer_store, "owner", -1)
                composer_store_valid = (
                    type(core_adapter) is _ReverseRecursiveFieldAdapter
                    and core_adapter.ledger is ledger
                    and core_adapter.actions is recursive.actions
                    and core_adapter.semantics is recursive.semantics
                    and core_adapter.interfaces is recursive.interfaces
                    and core_adapter.outputs is recursive.outputs
                    and core_adapter.sources is recursive.sources
                    and _store_valid(
                        composer_owner,
                        composer_store,
                        "reverse_recursive_composer_memo",
                        containers,
                        inventory,
                    )
                )
                valid &= composer_store_valid
                composer_items = (
                    composer_store.items() if type(composer_store) is OwnedMemo else ()
                )
                published_kernels: dict[FieldCellActionID, str] = {}
                published_morphism_sorts: dict[
                    FieldCellActionID, HigherMorphismSort
                ] = {}
                for composer_action, composer in composer_items:
                    recognized.update((id(composer_action), id(composer)))
                    composer_valid = (
                        type(composer_action) is FieldCellActionID
                        and type(composer) is HigherSpatialMacroComposer
                        and composer.action == composer_action
                        and composer.ledger is ledger
                        and composer.semantics is core_adapter.semantics
                        and composer.interfaces is core_adapter.interfaces
                        and composer.outputs is core_adapter.outputs
                        and composer.sources is core_adapter.sources
                        and not composer.source_backed_temporal
                        and composer.blank == recursive.blank
                    )
                    try:
                        recursive.actions.validate_action(composer_action)
                        action_record = recursive.actions.resolve(composer_action)
                        declaration = composer.declaration()
                        interface_record = recursive.interfaces.resolve(
                            composer.local_interface
                        )
                        interface = recursive.interfaces.interface(
                            interface_record.signature
                        )
                        expected_ports = (
                            HigherPort(composer.left, "left-boundary"),
                            HigherPort(composer.symbol, "source-symbol"),
                            HigherPort(composer.right, "right-boundary"),
                        )
                        composer_valid &= (
                            declaration.action == composer_action
                            and declaration.interface == composer.local_interface
                            and declaration.left == composer.left
                            and declaration.symbol == composer.symbol
                            and declaration.right == composer.right
                            and declaration.blank
                            == recursive.semantics.schema.alphabet(composer_action)[1]
                            and declaration.kernel_digest == interface.kernel.digest
                            and declaration.morphism_sort.owner
                            is recursive.outputs.owner
                            and declaration.morphism_sort.kind == recursive.outputs.kind
                            and interface.kernel
                            == recursive.actions.semantic_identity(
                                composer_action, audit=True
                            )
                            and interface.inputs == expected_ports
                            and interface.phase_count
                            == action_record.geometry.phase_count
                            and recursive.semantics.component_sort(composer.left)
                            == FieldStateSort(composer_action, 0)
                            and recursive.semantics.component_sort(composer.right)
                            == FieldStateSort(composer_action, 1)
                            and recursive.semantics.component_sort(composer.symbol)
                            == FieldSymbolSort(
                                *recursive.semantics.schema.alphabet(composer_action)
                            )
                        )
                        compilation = core_adapter.compiler._cache.get(composer_action)
                        if compilation is not None:
                            composer_valid &= (
                                type(compilation) is ReverseHigherInterfaceCompilation
                                and composer.local_interface == compilation.interface
                                and interface_record.signature == compilation.signature
                                and composer.left == compilation.left
                                and composer.symbol == compilation.symbol
                                and composer.right == compilation.right
                                and action_record.output == compilation.output_morphism
                            )
                    except (
                        TypeError,
                        ValueError,
                        IndexError,
                        KeyError,
                        AttributeError,
                    ):
                        composer_valid = False
                    if composer_store_valid and composer_valid:
                        approved.update((id(composer_action), id(composer)))
                        published_kernels[composer_action] = declaration.kernel_digest
                        published_morphism_sorts[composer_action] = (
                            declaration.morphism_sort
                        )
                    else:
                        valid = False
                        invalid.add((composer_owner, id(composer_action)))
                        invalid.add((composer_owner, id(composer)))

                signature_store = getattr(core_adapter, "_signatures", None)
                signature_owner = getattr(signature_store, "owner", -1)
                signature_store_valid = (
                    type(core_adapter._geometries) is FieldGeometryArena
                    and core_adapter._geometries.ledger is ledger
                    and type(signature_store) is OwnedMemo
                    and _store_valid(
                        signature_owner,
                        signature_store,
                        "reverse_recursive_signature_memo",
                        containers,
                        inventory,
                    )
                )
                valid &= signature_store_valid
                geometries = (
                    core_adapter._geometries._nodes
                    if type(core_adapter._geometries) is FieldGeometryArena
                    else ()
                )
                valid_geometry_domains = {
                    (geometry.spatial_level, geometry.phase_count)
                    for geometry in geometries
                    if type(geometry) is FieldGeometry
                }
                signatures_valid = True
                signature_items = (
                    signature_store.items()
                    if type(signature_store) is OwnedMemo
                    else ()
                )
                for signature_key, signature in signature_items:
                    recognized.update((id(signature_key), id(signature)))
                    signature_valid = (
                        type(signature_key) is tuple
                        and len(signature_key) == 2
                        and type(signature_key[0]) is FieldCellActionID
                        and type(signature_key[1]) is int
                        and signature_key[1] >= 0
                        and type(signature) is PortSignatureID
                    )
                    try:
                        if signature_valid:
                            signature_action = cast(FieldCellActionID, signature_key[0])
                            action_record = recursive.actions.resolve(signature_action)
                            signature_contract = recursive.interfaces.interface(
                                cast(PortSignatureID, signature)
                            )
                            kernel_digest = published_kernels.get(signature_action)
                            expected_family = (
                                "source-bound-higher-leaf"
                                if signature_key[1] == 0
                                else "source-bound-higher-parent"
                            )
                            expected_behavior = (
                                expected_family,
                                kernel_digest,
                            )
                            expected_identity = (
                                SemanticIdentity(
                                    sha256(
                                        repr(expected_behavior).encode()
                                    ).hexdigest(),
                                    expected_behavior,
                                )
                                if kernel_digest is not None
                                else None
                            )
                            expected_morphism = published_morphism_sorts.get(
                                signature_action
                            )
                            expected_output_sort = (
                                FieldSymbolSort(
                                    *recursive.semantics.schema.alphabet(
                                        signature_action
                                    )
                                )
                                if signature_key[1] == 0
                                else expected_morphism
                            )
                            signature_valid &= (
                                expected_identity is not None
                                and signature_contract.kernel == expected_identity
                                and (
                                    cast(int, signature_key[1]),
                                    action_record.geometry.phase_count,
                                )
                                in valid_geometry_domains
                                and signature_contract.phase_count
                                == action_record.geometry.phase_count
                                and tuple(
                                    port.role for port in signature_contract.inputs
                                )
                                == (
                                    "left-boundary",
                                    "right-boundary",
                                )
                                and tuple(
                                    recursive.semantics.component_sort(port.variable)
                                    for port in signature_contract.inputs
                                )
                                == (
                                    FieldStateSort(signature_action, 0),
                                    FieldStateSort(signature_action, 1),
                                )
                                and expected_output_sort is not None
                                and signature_contract.outputs[2]
                                == expected_output_sort
                                and signature_contract.outputs[11]
                                == expected_output_sort
                            )
                    except (
                        TypeError,
                        ValueError,
                        IndexError,
                        KeyError,
                        AttributeError,
                    ):
                        signature_valid = False
                    if signature_store_valid and signature_valid:
                        approved.update((id(signature_key), id(signature)))
                    else:
                        valid = False
                        signatures_valid = False
                        invalid.add((signature_owner, id(signature_key)))
                if (
                    type(signature_store) is OwnedMemo
                    and signature_store_valid
                    and signatures_valid
                ):
                    approved.add(id(signature_store._data))
                else:
                    invalid.add((signature_owner, id(signature_store)))
            else:
                valid = False
                invalid.add((recursive_owner, id(recursive)))
        if recursive_store_valid and recursive_store is not None:
            approved.add(id(recursive_store._data))
        else:
            invalid.add((recursive_owner, id(recursive_store)))
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
        q19_owner = getattr(root.adapter, "_q19_owner", None)
        if q19_owner is not None:
            valid &= (
                q19_owner.ledger is ledger
                and root.adapter._q19_source is source
                and type(source) is ExactSource
                and q19_owner._digits is source.digits
                and q19_owner.base == source.base == 10
            )
        if root_action is not None:
            valid &= root_action.steps == root.steps

        ports = root.adapter._ports
        if ports is not None:
            valid &= (
                type(ports) is SourceCarryPorts
                and ports._source is source
                and ports._ledger is ledger
            )

        for index, node in actions._nodes.items():
            recognized.update((id(index), id(node)))
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
                approved.update((id(index), id(node), id(action)))
            else:
                invalid.add((getattr(actions._nodes, "owner", -1), id(index)))
                invalid.add((getattr(actions._nodes, "owner", -1), id(node)))

        for steps, action in actions._normal.items():
            recognized.update((id(steps), id(action)))
            action_valid = type(steps) is int and type(action) is ReverseActionID
            if action_valid:
                action_valid = (
                    action_handle_valid(action)
                    and actions._nodes[action.local_id].steps == steps
                )
            valid &= action_valid
            if action_valid:
                approved.update((id(steps), id(action)))
            else:
                invalid.add((getattr(actions._normal, "owner", -1), id(steps)))
                invalid.add((getattr(actions._normal, "owner", -1), id(action)))

        for index, record in actions._sources.items():
            recognized.update((id(index), id(record)))
            record_valid = index == 0 and type(record) is _ReverseSourceRecord
            exact = getattr(record, "exact", None)
            record_valid &= type(exact) is ExactSource and exact is source
            valid &= record_valid
            if record_valid:
                approved.update((id(index), id(record), id(exact)))
            else:
                invalid.add((getattr(actions._sources, "owner", -1), id(index)))
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
        for cached_image, expected_action in (
            (root._image, root.root_action),
            (root._width_image, actions.identity),
        ):
            if cached_image is None:
                continue
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
                    and image_record.binding.action == expected_action
                    and image_record.adapter_key
                    == (root.adapter.family, root.adapter.semantic_version)
                    and core._adapters.get(image_record.adapter_key) is root.adapter
                )
                if cached_valid:
                    payload = image_record.payload
                    cached_valid = (
                        type(payload) is ReverseImagePayload
                        and payload.action == expected_action
                    )
                    pair_output = (
                        payload.pair_output
                        if type(payload) is ReverseImagePayload
                        else None
                    )
                    if pair_output is not None:
                        q19_owner = root.adapter._q19_owner
                        cached_valid &= (
                            type(q19_owner) is ReversePairQ19OutputOwner
                            and type(pair_output) is ReversePairOutputOccurrence
                            and type(source) is ExactSource
                            and root.adapter._q19_source is source
                            and q19_owner.ledger is ledger
                            and q19_owner._digits is source.digits
                            and pair_output.temporal_steps
                            == actions.node(expected_action).steps
                            and q19_owner._issued.get(
                                (pair_output.root, pair_output.temporal_steps)
                            )
                            is pair_output
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


def audit_reverse_source_owner(
    ledger: object, root: object
) -> PayloadAuditContribution:
    """Return source-image evidence only from this root's bound stores."""
    if type(ledger) is not ResourceLedger:
        raise TypeError("reverse source audit requires its resource ledger")
    from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts
    from number_compiler.sequences.reverse_add.source_workspace import (
        ReverseSourceImageWorkspace,
    )

    bindings: tuple[PayloadAuditStoreBinding, ...]
    roots: tuple[object, ...]
    if type(root) is SourceCarryPorts:
        bindings = (
            PayloadAuditStoreBinding(
                root._cache_owner,
                "_audit_cache",
                "reverse_source_carry_interval",
            ),
        )
        roots = (root,)
    elif type(root) is ReverseSourceImageWorkspace:
        bindings = (
            PayloadAuditStoreBinding(
                root.actions._nodes.owner,
                "_audit_action_nodes",
                "reverse_source_action",
            ),
            PayloadAuditStoreBinding(
                root.actions._normal.owner,
                "_audit_action_normal",
                "reverse_source_action_normal_form",
            ),
            PayloadAuditStoreBinding(
                root.actions._sources.owner,
                "_audit_sources",
                "reverse_original_source",
            ),
            PayloadAuditStoreBinding(
                root.actions._workspace_owner,
                "_audit_action_workspace",
                "reverse_source_action_workspace",
            ),
            PayloadAuditStoreBinding(
                root.adapter._recursive_occurrences.owner,
                "_audit_recursive_occurrences",
                "reverse_recursive_occurrence_binding",
            ),
            *nested_source_store_bindings(root),
        )
        ports = root.adapter._ports
        roots = (root,) if ports is None else (root, ports)
    else:
        return PayloadAuditContribution()

    owners = source_audit_owners(roots)
    containers: dict[int, object] = {}
    for owner in owners:
        try:
            containers[owner] = ledger.registered_container(owner)
        except (IndexError, RuntimeError, TypeError, ValueError):
            continue
    results = audit_reverse_source_payloads(ledger, roots, containers)
    approved: list[PayloadAuditEntry] = []
    invalid: list[PayloadAuditEntry] = []
    for binding in bindings:
        owner, attribute = binding.owner, binding.attribute
        store = getattr(root, attribute)
        if isinstance(store, Mapping):
            values: Iterable[object] = (
                value for pair in store.items() for value in pair
            )
        elif isinstance(store, Sequence) and not isinstance(
            store, (str, bytes, bytearray)
        ):
            values = store
        else:
            values = ()
        for value in values:
            if id(value) in results.approved:
                approved.append(PayloadAuditEntry(owner, value))
            if (owner, id(value)) in results.invalid:
                invalid.append(PayloadAuditEntry(owner, value))
    if results.invalid and not invalid:
        invalid.append(PayloadAuditEntry(bindings[0].owner, root))
    return PayloadAuditContribution(tuple(approved), tuple(invalid))


__all__ = [
    "ReverseSourcePayloadAudit",
    "audit_reverse_source_owner",
    "audit_reverse_source_payloads",
]

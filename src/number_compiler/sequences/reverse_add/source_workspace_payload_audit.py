"""Authority audit for retained reverse source-image workspaces."""

from __future__ import annotations

from collections.abc import Iterator, Mapping
from typing import Protocol, TypeGuard, TypeVar, cast

from number_compiler.resources.ledger import (
    OwnedMemo,
    ResourceInventory,
    ResourceLedger,
)
from number_compiler.resources.owned_memo import (
    DynamicMemoValue,
    OwnedMemoAuditSnapshot,
)
from number_compiler.resources.stores import LedgerDict, LedgerList
from number_compiler.sequences.reverse_add.source_workspace_core_audit import (
    source_image_core_storage_valid,
)

_AuditKey = TypeVar("_AuditKey")
_AuditValue = TypeVar("_AuditValue")


class _LedgerSizedStore(Protocol):
    owner: int
    ledger: ResourceLedger
    nodes_per_entry: int

    def __len__(self) -> int: ...


def _audit_payload_items(
    snapshot: OwnedMemoAuditSnapshot[_AuditKey, _AuditValue],
) -> Iterator[tuple[_AuditKey, object]]:
    """Read current memo payloads while preserving malformed-wrapper evidence."""
    view = snapshot.payload_view
    for key in snapshot.container:
        try:
            yield key, view[key]
        except TypeError:
            # Keep malformed dynamic entries visible to exact payload checks.
            yield key, snapshot.container[key]


def _audit_payload_value(
    snapshot: OwnedMemoAuditSnapshot[_AuditKey, _AuditValue], key: _AuditKey
) -> object:
    if key not in snapshot.container:
        return _MISSING
    try:
        return snapshot.payload_view[key]
    except TypeError:
        return snapshot.container[key]


_MISSING = object()


def store_valid_for_audit(
    ledger: ResourceLedger,
    owner: object,
    store: object,
    expected_role: str,
    containers: Mapping[int, object],
    inventory: Mapping[int, object],
) -> bool:
    if type(ledger) is not ResourceLedger or type(owner) is not int:
        return False
    item = inventory.get(owner)
    if type(item) is not ResourceInventory:
        return False
    owned_container: object | None = None
    entries = 0
    expected_nodes = 0
    if type(store) is OwnedMemo:
        snapshot = cast(OwnedMemo[object, object], store).audit_snapshot()
    elif type(store) is OwnedMemoAuditSnapshot:
        snapshot = cast(OwnedMemoAuditSnapshot[object, object], store)
    else:
        snapshot = None
    if snapshot is not None:
        data: Mapping[object, object] = snapshot.container
        if (
            snapshot.ledger is not ledger
            or snapshot.owner != owner
            or snapshot.disposed
        ):
            return False
        owned_container = data
        entries = len(data)
        if not snapshot.dynamic_cost:
            expected_nodes = entries * snapshot.nodes_per_entry
        else:
            expected_nodes = snapshot.dynamic_nodes
            measured_nodes = 0
            for raw_value in data.values():
                value: object = raw_value
                if type(value) is not DynamicMemoValue:
                    return False
                if type(value.nodes) is not int or value.nodes < 1:
                    return False
                measured_nodes += value.nodes
            if measured_nodes != expected_nodes:
                return False
    elif isinstance(store, (LedgerList, LedgerDict)):
        owned_store = cast(_LedgerSizedStore, store)
        owned_container = cast(object, store)
        entries = len(owned_store)
        expected_nodes = entries * owned_store.nodes_per_entry
        if owned_store.owner != owner or owned_store.ledger is not ledger:
            return False
    else:
        return False
    try:
        registered_container = ledger.registered_container(owner)
    except (IndexError, RuntimeError, TypeError, ValueError):
        return False
    return (
        containers.get(owner) is owned_container
        and registered_container is owned_container
        and not item.disposed
        and item.payloads_registered
        and item.role == expected_role
        and item.entries == entries
        and item.nodes == expected_nodes
    )


def audit_reverse_source_workspaces(
    ledger: ResourceLedger,
    roots: tuple[object, ...],
    containers: Mapping[int, object],
    inventory: Mapping[int, ResourceInventory],
) -> tuple[set[int], set[int], set[tuple[int, int]]]:
    """Validate workspace authority and every retained source-image record."""
    from number_compiler.arithmetic.contracts.exact_tree_context import (
        OriginalSourceConstruction,
    )
    from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
    from number_compiler.arithmetic.contracts.semantic_identity import (
        SemanticIdentity,
        SemanticIdentityDomain,
    )
    from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
    from number_compiler.hashlife.actions.field_actions import (
        FieldCellActionID,
        FieldGeometry,
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
        SourceImageRecord,
    )
    from number_compiler.hashlife.execution.source_image_inventory import SourceImageID
    from number_compiler.hashlife.execution.source_image_seals import (
        publication_matches_readonly,
    )
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
    from number_compiler.sequences.reverse_add.higher_interface import (
        ReverseHigherInterfaceCompilation,
    )
    from number_compiler.sequences.reverse_add.q19_controlled_gt_bank import (
        SourceGuardedGTBankAction,
    )
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairOutputOccurrence,
        ReversePairQ19OutputOwner,
    )
    from number_compiler.sequences.reverse_add.recursive_adapters import (
        ReverseRecursiveFieldAdapter,
    )
    from number_compiler.sequences.reverse_add.recursive_cutover import (
        ReverseRecursiveOccurrence,
        ReverseRecursiveTemporalCutover,
    )
    from number_compiler.sequences.reverse_add.source_actions import (
        ReverseSourceRecord,
    )
    from number_compiler.sequences.reverse_add.source_images import (
        MAX_COMPLETED_CHILD_FALLBACK_STEPS,
        ReverseActionArena,
        ReverseActionID,
        ReverseActionNode,
        ReverseImagePayload,
        ReverseSource,
        ReverseSourceImageAdapter,
        ReverseSourceImageWorkspace,
    )
    from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts

    approved: set[int] = set()
    recognized: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    for root in roots:
        if type(root) is not ReverseSourceImageWorkspace:
            continue
        state = root.audit_snapshot()
        actions = state.actions
        action_state = actions.audit_snapshot()
        adapter_state = state.adapter.audit_snapshot()
        owner = action_state.nodes.owner
        if type(actions) is not ReverseActionArena or actions.ledger is not ledger:
            invalid.add((owner, id(root)))
            continue
        valid = (
            state.ledger is ledger
            and type(state.disposed) is bool
            and not state.disposed
            and type(action_state.closed) is bool
            and not action_state.closed
        )
        authority = state.authority
        valid &= (
            type(authority) is tuple
            and len(authority) == 11
            and authority[0] is ledger
            and authority[1] is actions
            and authority[2] is state.source
            and authority[3] is state.root_action
            and authority[4] is state.scheduler
            and authority[5] is state.adapter
            and authority[6] == state.steps
            and authority[7] == state.base
            and authority[9] is state.request_binding
            and authority[10] is state.pointed_gt_store
            and type(state.request_binding) is tuple
            and len(state.request_binding) == 3
            and all(type(value) is int for value in state.request_binding)
            and state.request_binding[0] >= 0
            and state.request_binding[1:] == (state.steps, state.base)
            and (
                authority[8] is None
                or authority[8] is adapter_state.recursive_construction
            )
        )
        stores = (
            (
                action_state.nodes,
                action_state.nodes.owner,
                "reverse_source_action",
            ),
            (
                action_state.normal,
                action_state.normal.owner,
                "reverse_source_action_normal_form",
            ),
            (
                action_state.sources,
                action_state.sources.owner,
                "reverse_original_source",
            ),
            (
                action_state.workspace,
                action_state.workspace_owner,
                "reverse_source_action_workspace",
            ),
            (
                state.pointed_gt_banks,
                state.pointed_gt_banks.owner,
                "reverse_source_pointed_gt_bank",
            ),
        )
        stores_valid = True
        for store, store_owner, role in stores:
            if not store_valid_for_audit(
                ledger, store_owner, store, role, containers, inventory
            ):
                stores_valid = False
            else:
                if type(store) is OwnedMemoAuditSnapshot:
                    snapshot = cast(OwnedMemoAuditSnapshot[object, object], store)
                    approved.add(id(snapshot.container))
                else:
                    approved.add(id(store))
        valid &= stores_valid
        for bank_key, bank_action in _audit_payload_items(state.pointed_gt_banks):
            recognized.update((id(bank_key), id(bank_action)))
            action_owner = adapter_state.q19_owner
            q19_state = (
                action_owner.audit_snapshot() if action_owner is not None else None
            )
            action_valid = False
            if (
                type(bank_key) is tuple
                and len(bank_key) == 3
                and type(bank_key[0]) is ReverseSource
                and bank_key[0] is root.source
                and type(bank_key[1]) is int
                and type(bank_key[2]) is int
                and type(bank_action) is SourceGuardedGTBankAction
                and action_owner is not None
                and q19_state is not None
            ):
                action_valid = (
                    bank_action.owner is action_owner
                    and bank_action.source.owner is q19_state.authority
                    and bank_action.source is action_owner.initial
                    and bank_action.steps == bank_key[1] == root.steps
                    and bank_action.coordinate == bank_key[2]
                )
            if action_valid and type(bank_action) is SourceGuardedGTBankAction:
                try:
                    bank_action.validate_source_authority()
                except (AttributeError, TypeError, ValueError):
                    action_valid = False
            if action_valid:
                approved.update((id(bank_key), id(bank_action)))
            else:
                valid = False
                invalid.add((state.pointed_gt_banks.owner, id(bank_key)))
                invalid.add((state.pointed_gt_banks.owner, id(bank_action)))
        action_size = len(action_state.nodes.container)

        def action_handle_valid(
            value: object,
            *,
            _owner: object = actions.owner,
            _kind: str = action_state.kind,
            _size: int = action_size,
        ) -> TypeGuard[ReverseActionID]:
            return (
                type(value) is ReverseActionID
                and value.owner is _owner
                and value.kind == _kind
                and type(value.local_id) is int
                and 0 <= value.local_id < _size
            )

        source = None
        root_action: object | None = None
        if (
            type(root.source) is ReverseSource
            and root.source.owner is actions.owner
            and root.source.kind == action_state.source_kind
            and type(root.source.local_id) is int
        ):
            try:
                source_record = _audit_payload_value(
                    action_state.sources, root.source.local_id
                )
                source_authority = action_state.source_authority
                if type(source_record) is ReverseSourceRecord:
                    if (
                        type(root.source.local_id) is int
                        and root.source.local_id == 0
                        and type(source_authority) is tuple
                        and len(source_authority) == 4
                        and source_authority[0] is source_record
                        and source_authority[1] is source_record.exact
                        and source_authority[2] is source_record.exact.digits
                        and source_authority[3] == source_record.exact.base
                    ):
                        source = source_record.exact
            except (TypeError, ValueError, AttributeError, IndexError, KeyError):
                source = None
        if valid and type(source) is ExactSource and source.base >= 2:
            # Explicit resource audits check request metadata against the
            # admitted original source; runtime hits only check its authority.
            remaining_seed = state.request_binding[0]
            for digit in source.digits:
                remaining_seed, remainder = divmod(remaining_seed, source.base)
                valid &= type(digit) is int and remainder == digit
            valid &= remaining_seed == 0 and source.base == root.base
        if action_handle_valid(root.root_action):
            root_action = _audit_payload_value(
                action_state.nodes, root.root_action.local_id
            )
        if (
            type(root.source) is not ReverseSource
            or type(root.root_action) is not ReverseActionID
        ):
            valid = False
        if type(root.steps) is not int or root.steps < 0:
            valid = False
        if type(root.base) is not int or root.base < 2:
            valid = False
        if (
            type(root.scheduler) is not TileScheduler
            or not root.scheduler.is_source_only
        ):
            valid = False
        if (
            type(root.adapter) is not ReverseSourceImageAdapter
            or root.adapter.actions is not actions
            or root.adapter.ledger is not ledger
        ):
            valid = False
        recursive_store = adapter_state.recursive_occurrences
        recursive_owner = recursive_store.owner
        recursive_store_valid = store_valid_for_audit(
            ledger,
            recursive_owner,
            recursive_store,
            "reverse_recursive_occurrence_binding",
            containers,
            inventory,
        )
        valid &= recursive_store_valid
        recursive = adapter_state.recursive
        construction = adapter_state.recursive_construction
        if construction is not None:
            try:
                if type(construction) is not OriginalSourceConstruction:
                    raise TypeError("reverse source construction has another owner")
                exact_pair_source = construction.validate_source()
                original = actions.source(root.source)
                maximum_steps = adapter_state.recursive_maximum_steps
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
            # The snapshot object itself is always truthy; inspect its exact
            # backing mapping to establish that no fallback occurrence was
            # published without its recursive owner/construction.
            valid &= recursive is None and len(recursive_store.container) == 0
        if recursive is not None:
            recursive_state = recursive.audit_snapshot()
            recursive_valid = (
                type(recursive) is ReverseRecursiveTemporalCutover
                and recursive.ledger is ledger
                and recursive.source.owner is recursive.sources.owner
                and recursive.maximum_steps == adapter_state.recursive_maximum_steps
                and recursive.maximum_steps >= root.steps
                and adapter_state.recursive_source is actions.source(root.source)
            )
            if recursive_valid and construction is not None:
                recursive_valid &= (
                    recursive_state.source_geometry.construction.source
                    == construction.validate_source()
                    and recursive.extent == construction.validate_source().extent
                )
            if recursive_valid:
                valid &= recursive_valid
                recognized.add(id(recursive))
                for steps, occurrence in _audit_payload_items(
                    adapter_state.recursive_occurrences
                ):
                    recognized.add(id(occurrence))
                    recognized.add(id(steps))
                    if (
                        type(steps) is not int
                        or type(occurrence) is not ReverseRecursiveOccurrence
                    ):
                        valid = False
                        invalid.add((recursive_owner, id(steps)))
                        invalid.add((recursive_owner, id(occurrence)))
                        continue
                    occurrence_valid = (
                        occurrence.temporal_steps == steps
                        and occurrence.source is recursive.source
                    )
                    try:
                        recursive.validate_occurrence(occurrence)
                        expected_action = _audit_payload_value(
                            recursive_state.pair_actions, steps
                        )
                        occurrence_valid &= (
                            type(expected_action) is FieldCellActionID
                            and occurrence.action == expected_action
                            and occurrence.authority
                            is recursive_state.occurrence_authority
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
                recursive_adapter_state = core_adapter.audit_snapshot()
                composer_store = recursive_adapter_state.composers
                composer_owner = composer_store.owner
                composer_store_valid = (
                    type(core_adapter) is ReverseRecursiveFieldAdapter
                    and core_adapter.ledger is ledger
                    and core_adapter.actions is recursive.actions
                    and core_adapter.semantics is recursive.semantics
                    and core_adapter.interfaces is recursive.interfaces
                    and core_adapter.outputs is recursive.outputs
                    and core_adapter.sources is recursive.sources
                    and store_valid_for_audit(
                        ledger,
                        composer_owner,
                        composer_store,
                        "reverse_recursive_composer_memo",
                        containers,
                        inventory,
                    )
                )
                valid &= composer_store_valid
                composer_items = _audit_payload_items(composer_store)
                published_kernels: dict[FieldCellActionID, str] = {}
                published_morphism_sorts: dict[
                    FieldCellActionID, HigherMorphismSort
                ] = {}
                for composer_action, composer in composer_items:
                    recognized.update((id(composer_action), id(composer)))
                    if (
                        type(composer_action) is not FieldCellActionID
                        or type(composer) is not HigherSpatialMacroComposer
                    ):
                        valid = False
                        invalid.add((composer_owner, id(composer_action)))
                        invalid.add((composer_owner, id(composer)))
                        continue
                    declaration = None
                    composer_valid = (
                        composer.action == composer_action
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
                        compilation = recursive_adapter_state.compiler_cache.get(
                            composer_action
                        )
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
                    if (
                        composer_store_valid
                        and composer_valid
                        and declaration is not None
                    ):
                        approved.update((id(composer_action), id(composer)))
                        published_kernels[composer_action] = declaration.kernel_digest
                        published_morphism_sorts[composer_action] = (
                            declaration.morphism_sort
                        )
                    else:
                        valid = False
                        invalid.add((composer_owner, id(composer_action)))
                        invalid.add((composer_owner, id(composer)))

                signature_store = recursive_adapter_state.signatures
                signature_owner = signature_store.owner
                signature_store_valid = (
                    recursive_adapter_state.geometries is not None
                    and recursive_adapter_state.geometries.ledger is ledger
                    and store_valid_for_audit(
                        ledger,
                        signature_owner,
                        signature_store,
                        "reverse_recursive_signature_memo",
                        containers,
                        inventory,
                    )
                )
                valid &= signature_store_valid
                geometries = (
                    recursive_adapter_state.geometries.nodes
                    if recursive_adapter_state.geometries is not None
                    else ()
                )
                valid_geometry_domains = {
                    (geometry.spatial_level, geometry.phase_count)
                    for geometry in geometries
                    if type(geometry) is FieldGeometry
                }
                signatures_valid = True
                signature_items = _audit_payload_items(signature_store)
                for signature_key, signature in signature_items:
                    recognized.update((id(signature_key), id(signature)))
                    if not (
                        type(signature_key) is tuple
                        and len(signature_key) == 2
                        and type(signature_key[0]) is FieldCellActionID
                        and type(signature_key[1]) is int
                        and signature_key[1] >= 0
                        and type(signature) is PortSignatureID
                    ):
                        signatures_valid = False
                        valid = False
                        invalid.add((signature_owner, id(signature_key)))
                        continue
                    signature_action = signature_key[0]
                    signature_level = signature_key[1]
                    try:
                        action_record = recursive.actions.resolve(signature_action)
                        signature_contract = recursive.interfaces.interface(signature)
                        kernel_digest = published_kernels.get(signature_action)
                        expected_family = (
                            "source-bound-higher-leaf"
                            if signature_level == 0
                            else "source-bound-higher-parent"
                        )
                        expected_behavior = (expected_family, kernel_digest)
                        expected_identity = (
                            SemanticIdentity(
                                SemanticIdentityDomain.ANONYMOUS,
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
                                *recursive.semantics.schema.alphabet(signature_action)
                            )
                            if signature_level == 0
                            else expected_morphism
                        )
                        signature_valid = (
                            expected_identity is not None
                            and signature_contract.kernel == expected_identity
                            and (signature_level, action_record.geometry.phase_count)
                            in valid_geometry_domains
                            and signature_contract.phase_count
                            == action_record.geometry.phase_count
                            and tuple(port.role for port in signature_contract.inputs)
                            == ("left-boundary", "right-boundary")
                            and tuple(
                                recursive.semantics.component_sort(port.variable)
                                for port in signature_contract.inputs
                            )
                            == (
                                FieldStateSort(signature_action, 0),
                                FieldStateSort(signature_action, 1),
                            )
                            and expected_output_sort is not None
                            and signature_contract.outputs[2] == expected_output_sort
                            and signature_contract.outputs[11] == expected_output_sort
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
                if signature_store_valid and signatures_valid:
                    approved.add(id(signature_store.container))
                else:
                    invalid.add((signature_owner, id(signature_store)))
            else:
                valid = False
                invalid.add((recursive_owner, id(recursive)))
        if recursive_store_valid:
            approved.add(id(recursive_store.container))
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
                and root.root_action
                is _audit_payload_value(action_state.normal, root.steps)
            )
        q19_owner = adapter_state.q19_owner
        if q19_owner is not None:
            q19_state = q19_owner.audit_snapshot()
            valid &= (
                q19_owner.ledger is ledger
                and adapter_state.q19_source is source
                and type(source) is ExactSource
                and q19_state.digits is source.digits
                and q19_owner.base == source.base == 10
            )
        if root_action is not None:
            if type(root_action) is ReverseActionNode:
                valid &= root_action.steps == root.steps
            else:
                valid = False

        ports = root.adapter.published_ports
        if ports is not None:
            valid &= (
                type(ports) is SourceCarryPorts
                and ports.audit_snapshot().source is source
                and ports.audit_snapshot().ledger is ledger
            )

        for index, node in _audit_payload_items(action_state.nodes):
            recognized.update((id(index), id(node)))
            if (
                type(index) is not int
                or index < 0
                or type(node) is not ReverseActionNode
            ):
                invalid.add((action_state.nodes.owner, id(index)))
                invalid.add((action_state.nodes.owner, id(node)))
                valid = False
                continue
            action_id = ReverseActionID(actions.owner, action_state.kind, index)
            node_valid = action_handle_valid(action_id) and (
                _audit_payload_value(action_state.nodes, index) is node
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
                    before_id = before
                    after_id = after
                    before_node = _audit_payload_value(
                        action_state.nodes, before_id.local_id
                    )
                    after_node = _audit_payload_value(
                        action_state.nodes, after_id.local_id
                    )
                    if (
                        type(before_node) is not ReverseActionNode
                        or type(after_node) is not ReverseActionNode
                    ):
                        node_valid = False
                        valid = False
                        invalid.add((action_state.nodes.owner, id(before_node)))
                        invalid.add((action_state.nodes.owner, id(after_node)))
                        continue
                    node_valid = (
                        type(node.steps) is int
                        and node.steps >= 2
                        and before_id.local_id < index
                        and after_id.local_id < index
                        and before_node.steps + after_node.steps == node.steps
                        and node.depth
                        == 1
                        + max(
                            before_node.depth,
                            after_node.depth,
                        )
                    )
            valid &= node_valid
            if node_valid:
                approved.update((id(index), id(node), id(action_id)))
            else:
                invalid.add((action_state.nodes.owner, id(index)))
                invalid.add((action_state.nodes.owner, id(node)))

        for steps, normal_action in _audit_payload_items(action_state.normal):
            recognized.update((id(steps), id(normal_action)))
            action_valid = False
            if type(steps) is int and action_handle_valid(normal_action):
                node = _audit_payload_value(action_state.nodes, normal_action.local_id)
                action_valid = type(node) is ReverseActionNode and node.steps == steps
            valid &= action_valid
            if action_valid:
                approved.update((id(steps), id(normal_action)))
            else:
                invalid.add((action_state.normal.owner, id(steps)))
                invalid.add((action_state.normal.owner, id(normal_action)))

        for index, record in _audit_payload_items(action_state.sources):
            recognized.update((id(index), id(record)))
            record_valid = False
            exact = None
            if index == 0 and type(record) is ReverseSourceRecord:
                exact = record.exact
                record_valid = type(exact) is ExactSource and exact is source
            valid &= record_valid
            if record_valid:
                approved.update((id(index), id(record), id(exact)))
            else:
                invalid.add((action_state.sources.owner, id(index)))
                invalid.add((action_state.sources.owner, id(record)))

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
        for cached_image, expected_reverse_action in ((state.image, root.root_action),):
            if cached_image is None:
                continue
            cached_valid = False
            core = state.scheduler.published_source_image_core
            core_state = core.audit_snapshot() if core is not None else None
            if (
                type(core) is SourceBoundSchedulerCore
                and core_state is not None
                and core_state.ledger is ledger
                and not core_state.closed
                and source_image_core_storage_valid(
                    ledger, containers, inventory, core_state
                )
                and type(cached_image) is SourceImageID
                and cached_image.owner is core_state.owner
                and cached_image.kind == core_state.kind
                and type(cached_image.local_id) is int
                and 0 <= cached_image.local_id < len(core_state.nodes)
            ):
                image_record = core_state.nodes[cached_image.local_id]
                cached_valid = (
                    type(image_record) is SourceImageRecord
                    and cached_image.local_id < len(core_state.image_seals)
                    and core_state.image_seals[cached_image.local_id]
                    is image_record.publication_snapshot
                    and image_record.binding.source == root.source
                    and image_record.binding.action == expected_reverse_action
                    and image_record.adapter_key
                    == (root.adapter.family, root.adapter.semantic_version)
                    and core_state.adapters.get(image_record.adapter_key)
                    is root.adapter
                )
                if cached_valid:
                    try:
                        cached_valid = publication_matches_readonly(
                            (
                                image_record.binding,
                                image_record.payload,
                                image_record.failure_prefix,
                                image_record.publication_provenance,
                                id(image_record.adapter),
                                image_record.binding_audit_required,
                            ),
                            image_record.publication_snapshot,
                        )
                    except (AttributeError, IndexError, TypeError, ValueError):
                        cached_valid = False
                if cached_valid:
                    payload = image_record.payload
                    cached_valid = (
                        type(payload) is ReverseImagePayload
                        and payload.action == expected_reverse_action
                    )
                    pair_output = (
                        payload.pair_output
                        if type(payload) is ReverseImagePayload
                        else None
                    )
                    if pair_output is not None:
                        q19_owner = adapter_state.q19_owner
                        q19_state = (
                            q19_owner.audit_snapshot()
                            if q19_owner is not None
                            else None
                        )
                        if (
                            type(q19_owner) is ReversePairQ19OutputOwner
                            and type(pair_output) is ReversePairOutputOccurrence
                            and type(source) is ExactSource
                            and adapter_state.q19_source is source
                            and q19_owner.ledger is ledger
                            and q19_state is not None
                            and q19_state.digits is source.digits
                            and pair_output.temporal_steps
                            == actions.node(expected_reverse_action).steps
                        ):
                            try:
                                q19_owner.validate_issued_occurrence(pair_output)
                            except (TypeError, ValueError):
                                cached_valid = False
                        else:
                            cached_valid = False
            if not cached_valid:
                valid = False
                invalid.add((owner, id(cached_image)))
        if valid:
            approved.add(id(root))
        else:
            invalid.add((owner, id(root)))
    return approved, recognized, invalid


__all__ = ["audit_reverse_source_workspaces"]

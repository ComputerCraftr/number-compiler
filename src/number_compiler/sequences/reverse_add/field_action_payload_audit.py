"""Exact owner audit for reverse/add algebraic field-action arenas."""

from __future__ import annotations

from collections.abc import Callable, Hashable, Iterable, Mapping, Sized
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.input_validation import is_object_tuple
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle
from number_compiler.resources.ledger import ResourceInventory, ResourceLedger
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditEntry,
)

if TYPE_CHECKING:
    from number_compiler.sequences.reverse_add.field_action import (
        ReverseFieldActionArena,
    )


def register_reverse_field_action_contract(root: ReverseFieldActionArena) -> None:
    """Bind the reverse action arena's exact owned stores to its pure auditor."""
    root.ledger.register_payload_audit_contract(
        root,
        "reverse_add",
        root.payload_audit_store_bindings(),
        audit_reverse_field_action_owner,
    )


def _bounded_semantic_key(value: object) -> bool:
    from number_compiler.arithmetic.contracts.canonical_payload import (
        validate_bounded_semantic_key,
    )

    if not isinstance(value, Hashable):
        return False
    try:
        validate_bounded_semantic_key(value, max_units=256)
    except (TypeError, ValueError):
        return False
    return True


def _semantic_slot(
    value: object,
    reference: ArenaHandle | None,
    index: int,
    validate_handle: Callable[[object], bool],
) -> bool:
    """Check a bounded semantic value and its exact interner position."""
    return (
        _bounded_semantic_key(value)
        and reference is not None
        and validate_handle(reference)
        and reference.local_id == index
    )


def _owner_inventory(
    ledger: ResourceLedger, owners: Iterable[int]
) -> dict[int, ResourceInventory]:
    result: dict[int, ResourceInventory] = {}
    for owner in owners:
        try:
            result[owner] = ledger.inventory_owner(owner)
        except (IndexError, TypeError, ValueError):
            continue
    return result


def _owner_containers(
    ledger: ResourceLedger, owners: Iterable[int]
) -> dict[int, object]:
    result: dict[int, object] = {}
    for owner in owners:
        try:
            result[owner] = ledger.registered_container(owner)
        except (IndexError, RuntimeError, TypeError, ValueError):
            continue
    return result


def _registered_store(
    owner: object,
    store: object,
    role: str,
    containers: dict[int, object],
    inventory: dict[int, ResourceInventory],
    *,
    node_store: bool = False,
) -> bool:
    if (
        type(owner) is not int
        or type(store).__module__ != "number_compiler.resources.stores"
        or not isinstance(store, Sized)
    ):
        return False
    item = inventory.get(owner)
    size = len(store)
    expected_nodes = size if node_store else 0
    return (
        type(item) is ResourceInventory
        and containers.get(owner) is store
        and item.role == role
        and item.entries == size
        and item.observed_entries == size
        and item.nodes == expected_nodes
        and (
            item.observed_nodes == expected_nodes
            if node_store
            else item.observed_nodes in (None, 0)
        )
        and item.payloads_registered
        and not item.disposed
    )


def audit_reverse_field_action_root(
    root: object,
    ledger: ResourceLedger,
    containers: dict[int, object],
    owner_snapshot: object | None = None,
) -> tuple[set[int], set[tuple[int, int]]]:
    """Validate one reverse action/output arena without blessing its class name."""
    from number_compiler.arithmetic.automata.symmetry_powering import ActionTransform
    from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
    from number_compiler.hashlife.actions.field_actions import (
        CoordinateOutputMorphismID,
        FieldCellActionID,
    )
    from number_compiler.sequences.reverse_add.coordinate_program import (
        ReverseCoordinateProgram,
        ReverseCoordinateProgramArena,
        ReverseCoordinateProgramAuditSnapshot,
    )
    from number_compiler.sequences.reverse_add.field_action import (
        ReverseDefectClassID,
        ReverseFieldActionArena,
    )
    from number_compiler.sequences.reverse_add.field_action_audit import (
        ReverseFieldActionAuditSnapshot,
    )

    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    if type(root) is ReverseCoordinateProgramArena:
        coordinate_snapshot = (
            root.payload_audit_snapshot() if owner_snapshot is None else owner_snapshot
        )
        if type(coordinate_snapshot) is not ReverseCoordinateProgramAuditSnapshot:
            raise TypeError("coordinate owner returned an invalid audit snapshot")
        coordinate_keys = dict(coordinate_snapshot.keys)
        coordinate_stores = (
            (
                coordinate_snapshot.node_owner,
                coordinate_snapshot.node_backing,
                "reverse_output_morphism",
                True,
            ),
            (
                coordinate_snapshot.key_owner,
                coordinate_snapshot.key_backing,
                "reverse_output_interner",
                False,
            ),
            (
                coordinate_snapshot.compose_owner,
                coordinate_snapshot.compose_backing,
                "reverse_output_composition",
                False,
            ),
        )
        inventory = _owner_inventory(
            ledger, (owner for owner, _, _, _ in coordinate_stores)
        )
        all_valid = (
            coordinate_snapshot.ledger is ledger
            and type(coordinate_snapshot.owner) is ArenaToken
            and type(coordinate_snapshot.base) is int
            and coordinate_snapshot.base >= 2
            and all(
                _registered_store(
                    owner,
                    store,
                    role,
                    containers,
                    inventory,
                    node_store=node_store,
                )
                for owner, store, role, node_store in coordinate_stores
            )
        )

        def coordinate_handle(value: object) -> bool:
            from number_compiler.hashlife.actions.field_actions import (
                CoordinateOutputMorphismID,
            )

            return (
                type(value) is CoordinateOutputMorphismID
                and type(value.owner) is ArenaToken
                and value.owner is coordinate_snapshot.owner
                and value.kind == coordinate_snapshot.kind
                and type(value.local_id) is int
                and 0 <= value.local_id < len(coordinate_snapshot.nodes)
            )

        for index, program in enumerate(coordinate_snapshot.nodes):
            valid = type(program) is ReverseCoordinateProgram
            try:
                if not valid:
                    raise TypeError("invalid reverse coordinate program")
                program.__post_init__()
                valid &= program.base == root.base
                if program.atom is not None:
                    valid &= _bounded_semantic_key(program.atom)
                from number_compiler.hashlife.actions.field_actions import (
                    CoordinateOutputMorphismID,
                )

                reference = CoordinateOutputMorphismID(
                    coordinate_snapshot.owner, coordinate_snapshot.kind, index
                )
                valid &= coordinate_handle(reference)
                valid &= root.resolve(reference) is program
                valid &= coordinate_keys.get(program) == index
                if index == 0:
                    valid &= program == ReverseCoordinateProgram(root.base, 0, False)
                elif index == 1:
                    valid &= program == ReverseCoordinateProgram(root.base, 1, False)
                elif index == 2:
                    valid &= program == ReverseCoordinateProgram(root.base, 0, True)
            except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                valid = False
            if valid:
                approved.add(id(program))
            else:
                invalid.add((coordinate_snapshot.node_owner, id(program)))
                all_valid = False

        for program, index in coordinate_snapshot.keys:
            valid = type(program) is ReverseCoordinateProgram and type(index) is int
            try:
                if not valid:
                    raise TypeError("invalid reverse coordinate interner entry")
                valid &= 0 <= index < len(coordinate_snapshot.nodes)
                valid &= coordinate_snapshot.nodes[index] is program
                valid &= program.base == coordinate_snapshot.base
            except (TypeError, ValueError, IndexError, AttributeError):
                valid = False
            if valid:
                approved.add(id(program))
            else:
                invalid.add((coordinate_snapshot.key_owner, id(program)))
                all_valid = False
        all_valid &= len(coordinate_snapshot.keys) == len(coordinate_snapshot.nodes)

        for coordinate_key, coordinate_result in coordinate_snapshot.compositions:
            valid = (
                type(coordinate_key) is tuple
                and len(coordinate_key) == 2
                and all(coordinate_handle(item) for item in coordinate_key)
                and coordinate_handle(coordinate_result)
            )
            try:
                if not valid:
                    raise TypeError("invalid reverse coordinate composition")
                before, after = coordinate_key
                valid &= root.audit_composition_is_exact(
                    before, after, coordinate_result
                )
            except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                valid = False
            if valid:
                approved.update((id(coordinate_key), id(coordinate_result)))
            else:
                invalid.add((coordinate_snapshot.compose_owner, id(coordinate_key)))
                all_valid = False
        if all_valid:
            approved.update(id(store) for _, store, _, _ in coordinate_stores)
            approved.update(
                id(value)
                for value in (
                    coordinate_snapshot.identity,
                    coordinate_snapshot.primitive,
                    coordinate_snapshot.terminal,
                )
            )
    elif type(root) is ReverseFieldActionArena:
        action_snapshot = (
            root.payload_audit_snapshot() if owner_snapshot is None else owner_snapshot
        )
        if type(action_snapshot) is not ReverseFieldActionAuditSnapshot:
            raise TypeError("field-action owner returned an invalid audit snapshot")
        coordinate_programs = action_snapshot.coordinate_programs
        action_stores = tuple(
            (
                owner,
                backing,
                role,
                role
                in {
                    "reverse_residual_node",
                    "reverse_output_morphism",
                    "reverse_field_action",
                    "reverse_action_semantic_identity",
                },
            )
            for owner, _attribute, role, backing in action_snapshot.stores
        )
        inventory = _owner_inventory(
            ledger, (owner for owner, _, _, _ in action_stores)
        )
        all_valid = (
            action_snapshot.ledger is ledger
            and type(action_snapshot.owner) is ArenaToken
            and type(action_snapshot.base) is int
            and action_snapshot.base >= 2
            and type(action_snapshot.order) is int
            and 2 <= action_snapshot.order <= 16
            and action_snapshot.order & (action_snapshot.order - 1) == 0
            and type(action_snapshot.max_residual_classes) is int
            and 1 <= action_snapshot.max_residual_classes <= 64
            and all(
                _registered_store(
                    owner,
                    store,
                    role,
                    containers,
                    inventory,
                    node_store=node_store,
                )
                for owner, store, role, node_store in action_stores
            )
        )
        if coordinate_programs is not None:
            all_valid &= (
                type(coordinate_programs) is ReverseCoordinateProgramArena
                and coordinate_programs.ledger is ledger
                and coordinate_programs.base == action_snapshot.base
                and any(
                    live_root is coordinate_programs
                    for live_root in ledger.iter_execution_roots()
                )
            )

        def action_handle(value: object) -> bool:
            if (
                type(value) is not FieldCellActionID
                or type(value.owner) is not ArenaToken
                or value.owner is not action_snapshot.owner
                or value.kind != action_snapshot.action_kind
                or type(value.local_id) is not int
                or not 0 <= value.local_id < len(action_snapshot.actions)
            ):
                return False
            try:
                root.validate_action(value)
            except (TypeError, ValueError, IndexError):
                return False
            return True

        def residual_handle(value: object) -> bool:
            if (
                type(value) is not ReverseDefectClassID
                or type(value.owner) is not ArenaToken
                or value.owner is not action_snapshot.owner
                or value.kind != action_snapshot.residual_kind
                or type(value.local_id) is not int
                or not 0 <= value.local_id < len(action_snapshot.residuals)
            ):
                return False
            try:
                root.validate_residual(value)
            except (TypeError, ValueError, IndexError):
                return False
            return True

        def output_handle(value: object) -> bool:
            if type(value) is not CoordinateOutputMorphismID:
                return False
            try:
                root.validate_output(value)
            except (TypeError, ValueError, IndexError):
                return False
            if coordinate_programs is None:
                return (
                    value.owner is action_snapshot.owner
                    and value.kind == action_snapshot.output_kind
                    and type(value.local_id) is int
                    and 0 <= value.local_id < len(action_snapshot.outputs)
                )
            if type(coordinate_programs) is not ReverseCoordinateProgramArena:
                return False
            coordinate_snapshot = coordinate_programs.payload_audit_snapshot()
            return (
                value.owner is coordinate_snapshot.owner
                and value.kind == coordinate_snapshot.kind
                and type(value.local_id) is int
                and 0 <= value.local_id < len(coordinate_snapshot.nodes)
            )

        residuals_valid = (
            len(action_snapshot.residuals) <= action_snapshot.max_residual_classes
        )
        for index, residual_value in enumerate(action_snapshot.residuals):
            residual_reference = action_snapshot.residual_keys.get(residual_value)
            if _semantic_slot(
                residual_value, residual_reference, index, residual_handle
            ):
                approved.update((id(residual_value), id(residual_reference)))
            else:
                invalid.add((action_snapshot.residual_owner, id(residual_value)))
                residuals_valid = False
        residuals_valid &= len(action_snapshot.residual_keys) == len(
            action_snapshot.residuals
        )
        all_valid &= residuals_valid

        if coordinate_programs is None:
            outputs_valid = True
            for index, output_value in enumerate(action_snapshot.outputs):
                output_reference = action_snapshot.output_keys.get(output_value)
                if _semantic_slot(output_value, output_reference, index, output_handle):
                    approved.update((id(output_value), id(output_reference)))
                else:
                    invalid.add((action_snapshot.output_owner, id(output_value)))
                    outputs_valid = False
            outputs_valid &= len(action_snapshot.output_keys) == len(
                action_snapshot.outputs
            )
            all_valid &= outputs_valid
        else:
            all_valid &= not action_snapshot.outputs and not action_snapshot.output_keys
            if action_snapshot.outputs or action_snapshot.output_keys:
                invalid.add(
                    (action_snapshot.output_owner, id(action_snapshot.output_backing))
                )
                invalid.add(
                    (
                        action_snapshot.output_key_owner,
                        id(action_snapshot.output_key_backing),
                    )
                )
            if all_valid:
                approved.update(
                    (
                        id(action_snapshot.output_backing),
                        id(action_snapshot.output_key_backing),
                    )
                )

        actions_valid = True
        for index, action in enumerate(action_snapshot.actions):
            valid = root.audit_action_record_is_exact(index, action)
            if valid:
                approved.add(id(action))
                approved.update(
                    id(component)
                    for component in (
                        action.radial,
                        action.innovation,
                        action.carry_forward,
                        action.carry_backward,
                        action.residual,
                        action.output,
                        action.geometry,
                    )
                )
            else:
                invalid.add((action_snapshot.action_owner, id(action)))
                actions_valid = False
        actions_valid &= len(action_snapshot.action_keys) == len(
            action_snapshot.actions
        )
        for action_key, action_reference in action_snapshot.action_keys.items():
            valid = action_handle(action_reference) and type(action_key) is tuple
            try:
                action = root.resolve(action_reference)
                valid &= action_key == root.audit_expected_action_key(action)
            except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                valid = False
            if valid:
                approved.update((id(action_key), id(action_reference)))
            else:
                invalid.add((action_snapshot.action_key_owner, id(action_key)))
                actions_valid = False
        all_valid &= actions_valid

        identities_valid = (
            len(action_snapshot.semantic_identities)
            == len(action_snapshot.semantic_identity_issued)
            <= len(action_snapshot.actions)
        )
        for identity_source, record in action_snapshot.semantic_identities.items():
            issued_record = action_snapshot.semantic_identity_issued.get(
                identity_source
            )
            valid = action_handle(
                identity_source
            ) and root.audit_semantic_identity_is_exact(
                identity_source, record, issued_record
            )
            if valid and type(record) is tuple and len(record) == 6:
                radial_identity = record[3]
                digest = record[4]
                behavior = record[5]
                approved.update(
                    (
                        id(identity_source),
                        id(record),
                        id(radial_identity),
                        id(digest),
                        id(behavior),
                    )
                )
            else:
                invalid.add((action_snapshot.semantic_identity_owner, id(record)))
                identities_valid = False
        all_valid &= identities_valid

        compositions_valid = True
        for (
            action_composition_key,
            action_composition_result,
        ) in action_snapshot.compositions.items():
            valid = (
                type(action_composition_key) is tuple
                and len(action_composition_key) == 2
                and action_handle(action_composition_key[0])
                and action_handle(action_composition_key[1])
                and action_handle(action_composition_result)
            )
            if valid:
                action_before, action_after = action_composition_key
                valid &= root.audit_composition_is_exact(
                    action_before, action_after, action_composition_result
                )
            if valid:
                approved.update(
                    (id(action_composition_key), id(action_composition_result))
                )
            else:
                invalid.add((action_snapshot.compose_owner, id(action_composition_key)))
                compositions_valid = False
        all_valid &= compositions_valid

        witnesses_valid = True
        for witness_result, witness in action_snapshot.witnesses.items():
            valid = (
                action_handle(witness_result)
                and type(witness) is tuple
                and len(witness) == 2
                and action_handle(witness[0])
                and action_handle(witness[1])
            )
            if valid:
                valid &= action_snapshot.compositions.get(witness) == witness_result
                valid &= root.audit_composition_is_exact(
                    witness[0], witness[1], witness_result
                )
            if valid:
                approved.update((id(witness_result), id(witness)))
            else:
                invalid.add((action_snapshot.witness_owner, id(witness)))
                witnesses_valid = False
        all_valid &= witnesses_valid

        transforms_valid = True
        for transform_key, transform_result in action_snapshot.transforms.items():
            valid = (
                type(transform_key) is tuple
                and len(transform_key) == 2
                and action_handle(transform_key[0])
                and type(transform_key[1]) is ActionTransform
                and int(transform_key[1]) & ~3 == 0
                and action_handle(transform_result)
            )
            if valid:
                valid &= root.audit_transform_is_exact(
                    transform_key[0], transform_key[1], transform_result
                )
            if valid:
                approved.update((id(transform_key), id(transform_result)))
            else:
                invalid.add((action_snapshot.transform_owner, id(transform_key)))
                transforms_valid = False
        all_valid &= transforms_valid
        if all_valid:
            approved.update(id(store) for _, store, _, _ in action_stores)
        else:
            invalid.add((action_snapshot.action_owner, id(root)))
    return approved, invalid


def _coordinate_item_values(rows: tuple[object, ...]) -> Iterable[object]:
    """Expose exact mapping members without trusting erased snapshot types."""
    for row in rows:
        if not is_object_tuple(row) or type(row) is not tuple or len(row) != 2:
            raise TypeError("coordinate audit snapshot requires key/value pairs")
        yield from row


def audit_reverse_field_action_owner(
    ledger: object, root: object
) -> PayloadAuditContribution:
    """Audit a fresh owner snapshot and report its exact direct members."""
    if not isinstance(ledger, ResourceLedger):
        raise TypeError("reverse field audit requires a resource ledger")
    from number_compiler.sequences.reverse_add.coordinate_program import (
        ReverseCoordinateProgramArena,
    )
    from number_compiler.sequences.reverse_add.field_action import (
        ReverseFieldActionArena,
    )

    bindings: tuple[tuple[int, str, object, object], ...]
    owner_snapshot: object
    if isinstance(root, ReverseCoordinateProgramArena):
        if type(root) is not ReverseCoordinateProgramArena:
            raise TypeError("coordinate audit rejects subclassed arena owners")
        coordinate_snapshot = root.payload_audit_snapshot()
        owner_snapshot = coordinate_snapshot
        bindings = (
            (
                coordinate_snapshot.node_owner,
                "_nodes",
                coordinate_snapshot.node_backing,
                coordinate_snapshot.nodes,
            ),
            (
                coordinate_snapshot.key_owner,
                "_keys",
                coordinate_snapshot.key_backing,
                coordinate_snapshot.keys,
            ),
            (
                coordinate_snapshot.compose_owner,
                "_compose",
                coordinate_snapshot.compose_backing,
                coordinate_snapshot.compositions,
            ),
        )
    elif isinstance(root, ReverseFieldActionArena):
        if type(root) is not ReverseFieldActionArena:
            raise TypeError("field-action audit rejects subclassed arena owners")
        action_snapshot = root.payload_audit_snapshot()
        owner_snapshot = action_snapshot
        bindings = (
            (
                action_snapshot.residual_owner,
                "_residuals",
                action_snapshot.residual_backing,
                action_snapshot.residuals,
            ),
            (
                action_snapshot.residual_key_owner,
                "_residual_keys",
                action_snapshot.residual_key_backing,
                action_snapshot.residual_keys,
            ),
            (
                action_snapshot.output_owner,
                "_outputs",
                action_snapshot.output_backing,
                action_snapshot.outputs,
            ),
            (
                action_snapshot.output_key_owner,
                "_output_keys",
                action_snapshot.output_key_backing,
                action_snapshot.output_keys,
            ),
            (
                action_snapshot.action_owner,
                "_actions",
                action_snapshot.action_backing,
                action_snapshot.actions,
            ),
            (
                action_snapshot.action_key_owner,
                "_action_keys",
                action_snapshot.action_key_backing,
                action_snapshot.action_keys,
            ),
            (
                action_snapshot.compose_owner,
                "_compose",
                action_snapshot.compose_backing,
                action_snapshot.compositions,
            ),
            (
                action_snapshot.transform_owner,
                "_transforms",
                action_snapshot.transform_backing,
                action_snapshot.transforms,
            ),
            (
                action_snapshot.witness_owner,
                "_witnesses",
                action_snapshot.witness_backing,
                action_snapshot.witnesses,
            ),
            (
                action_snapshot.semantic_identity_owner,
                "_semantic_identities",
                action_snapshot.semantic_identity_backing,
                action_snapshot.semantic_identities,
            ),
            (
                action_snapshot.semantic_identity_issued_owner,
                "_semantic_identity_issued",
                action_snapshot.semantic_identity_issued_backing,
                action_snapshot.semantic_identity_issued,
            ),
        )
    else:
        return PayloadAuditContribution()

    containers = _owner_containers(ledger, (owner for owner, _, _, _ in bindings))
    approved_ids, invalid_rows = audit_reverse_field_action_root(
        root, ledger, containers, owner_snapshot
    )

    approved: list[PayloadAuditEntry] = []
    invalid: list[PayloadAuditEntry] = []
    anchor_owner = bindings[0][0]
    for owner, attribute, _backing, contents in bindings:
        if isinstance(contents, Mapping):
            values: Iterable[object] = (
                item for pair in contents.items() for item in pair
            )
        elif type(root) is ReverseCoordinateProgramArena and attribute in (
            "_keys",
            "_compose",
        ):
            # Coordinate snapshots store immutable item rows, whereas the
            # original owners use mappings. Treat the pair members as direct
            # store entries so the identity approvals made by the owner audit
            # are applied to the actual key and value objects, not only to the
            # temporary row tuple.
            if type(contents) is not tuple:
                raise TypeError("coordinate audit snapshot requires exact item rows")
            values = _coordinate_item_values(contents)
        else:
            values = iter(contents)
        for value in values:
            if id(value) in approved_ids:
                approved.append(PayloadAuditEntry(owner, value))
            if (owner, id(value)) in invalid_rows:
                invalid.append(PayloadAuditEntry(owner, value))
    if invalid_rows and not invalid:
        invalid.append(PayloadAuditEntry(anchor_owner, root))
    return PayloadAuditContribution(tuple(approved), tuple(invalid))


def audit_reverse_powered_codec_owner(
    ledger: object, root: object
) -> PayloadAuditContribution:
    """Validate one fresh packed-codec snapshot without reading private fields."""
    if not isinstance(ledger, ResourceLedger):
        raise TypeError("reverse codec audit requires a resource ledger")
    from number_compiler.hashlife.execution.field_images import (
        SourceCellID,
        SourceForestID,
    )
    from number_compiler.sequences.reverse_add.powered_local_codec import (
        ReverseLocalAction,
        ReverseLocalActionID,
        ReversePoweredLocalCodec,
    )

    if not isinstance(root, ReversePoweredLocalCodec):
        return PayloadAuditContribution()
    if type(root) is not ReversePoweredLocalCodec:
        raise TypeError("reverse codec audit rejects subclassed codec owners")

    owner_snapshot = root.payload_audit_snapshot()
    approved: list[PayloadAuditEntry] = []
    invalid: list[PayloadAuditEntry] = []

    def accept(owner: int, value: object, valid: bool) -> None:
        entry = PayloadAuditEntry(owner, value)
        (approved if valid else invalid).append(entry)

    valid_root = (
        owner_snapshot.ledger is ledger
        and owner_snapshot.sources.ledger is ledger
        and type(owner_snapshot.base) is int
        and owner_snapshot.base >= 2
        and owner_snapshot.blank == 2 * owner_snapshot.base - 1
        and type(owner_snapshot.states) is tuple
        and len(owner_snapshot.states) == 2
        and len(owner_snapshot.state_ids) == 2
        and owner_snapshot.state_index_layout_valid
        and len(owner_snapshot.state_owners) == 2
        and len(owner_snapshot.state_backings) == 2
    )

    for states, state_ids, owner in zip(
        owner_snapshot.states,
        owner_snapshot.state_ids,
        owner_snapshot.state_owners,
        strict=True,
    ):
        state_valid = valid_root and len(states) == len(state_ids)
        state_valid &= all(
            type(index) is int and 0 <= index < len(states) and states[index] == state
            for state, index in state_ids.items()
        )
        state_valid &= all(
            type(index) is int and state_ids.get(state) == index
            for index, state in enumerate(states)
        )
        if not state_valid:
            invalid.append(PayloadAuditEntry(owner, root))
        for state, local_index in state_ids.items():
            item_valid = (
                state_valid
                and type(local_index) is int
                and 0 <= local_index < len(states)
                and states[local_index] == state
            )
            accept(owner, state, item_valid)
            accept(owner, local_index, item_valid)

    nodes_valid = valid_root
    for index, action in enumerate(owner_snapshot.nodes):
        valid = root.audit_action_record_is_exact(index, action)
        accept(owner_snapshot.node_owner, action, valid)
        nodes_valid &= valid

    keys_valid = valid_root and len(owner_snapshot.keys) == len(owner_snapshot.nodes)
    for action, index in owner_snapshot.keys.items():
        valid = (
            type(action) is ReverseLocalAction
            and type(index) is int
            and 0 <= index < len(owner_snapshot.nodes)
            and owner_snapshot.nodes[index] is action
        )
        accept(owner_snapshot.key_owner, action, valid)
        keys_valid &= valid

    compose_valid = valid_root
    for key, result in owner_snapshot.compositions.items():
        valid = (
            type(key) is tuple
            and len(key) == 2
            and type(key[0]) is ReverseLocalActionID
            and type(key[1]) is ReverseLocalActionID
            and type(result) is ReverseLocalActionID
        )
        if valid:
            left, right = key
            valid &= root.audit_composition_is_exact(left, right, result)
        accept(owner_snapshot.compose_owner, key, valid)
        compose_valid &= valid

    bindings_valid = valid_root
    for symbol, action_id in owner_snapshot.leaf_actions.items():
        valid = root.audit_leaf_binding_is_exact(symbol, action_id)
        accept(owner_snapshot.leaf_owner, action_id, valid)
        bindings_valid &= valid

    for source, action_id in owner_snapshot.source_actions.items():
        valid = type(source) in (
            SourceCellID,
            SourceForestID,
        ) and root.audit_source_binding_is_valid(source, action_id)
        accept(owner_snapshot.source_owner, source, valid)
        bindings_valid &= valid

    if not (nodes_valid and keys_valid and compose_valid and bindings_valid):
        invalid.append(PayloadAuditEntry(owner_snapshot.node_owner, root))
    return PayloadAuditContribution(tuple(approved), tuple(invalid))

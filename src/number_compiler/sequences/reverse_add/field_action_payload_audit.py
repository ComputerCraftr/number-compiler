"""Exact owner audit for reverse/add algebraic field-action arenas."""

from __future__ import annotations

from collections.abc import Callable, Hashable, Iterable, Mapping, Sequence, Sized
from typing import TYPE_CHECKING, cast

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
    from number_compiler.resources.payload_contracts import PayloadAuditStoreBinding

    root.ledger.register_payload_audit_contract(
        root,
        "reverse_add",
        (
            PayloadAuditStoreBinding(
                root._residual_owner, "_residuals", "reverse_residual_node"
            ),
            PayloadAuditStoreBinding(
                root._residual_key_owner, "_residual_keys", "reverse_residual_interner"
            ),
            PayloadAuditStoreBinding(
                root._output_owner, "_outputs", "reverse_output_morphism"
            ),
            PayloadAuditStoreBinding(
                root._output_key_owner, "_output_keys", "reverse_output_interner"
            ),
            PayloadAuditStoreBinding(
                root._action_owner, "_actions", "reverse_field_action"
            ),
            PayloadAuditStoreBinding(
                root._action_key_owner, "_action_keys", "reverse_action_interner"
            ),
            PayloadAuditStoreBinding(
                root._compose_owner, "_compose", "reverse_action_composition"
            ),
            PayloadAuditStoreBinding(
                root._transform_owner, "_transforms", "reverse_action_transform"
            ),
            PayloadAuditStoreBinding(
                root._witness_owner,
                "_witnesses",
                "reverse_action_construction_witness",
            ),
            PayloadAuditStoreBinding(
                root._semantic_identity_owner,
                "_semantic_identities",
                "reverse_action_semantic_identity",
            ),
            PayloadAuditStoreBinding(
                root._semantic_identity_issued_owner,
                "_semantic_identity_issued",
                "reverse_action_semantic_identity_authority",
            ),
        ),
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
) -> tuple[set[int], set[tuple[int, int]]]:
    """Validate one reverse action/output arena without blessing its class name."""
    from number_compiler.arithmetic.automata.symmetry_powering import ActionTransform
    from number_compiler.arithmetic.carry.carry_monoid import compose_carry_fn
    from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
    from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
    from number_compiler.hashlife.actions.field_actions import FieldCellActionID
    from number_compiler.sequences.reverse_add.coordinate_program import (
        ReverseCoordinateProgram,
        ReverseCoordinateProgramArena,
    )
    from number_compiler.sequences.reverse_add.field_action import (
        ReverseActionAutomorphisms,
        ReverseDefectClassID,
        ReverseFieldAction,
        ReverseFieldActionArena,
        ReverseGeometry,
    )
    from number_compiler.sequences.reverse_add.semantic_identity_cache import (
        build_radial_identity,
    )

    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    if type(root) is ReverseCoordinateProgramArena:
        coordinate_stores = (
            (root._node_owner, root._nodes, "reverse_output_morphism", True),
            (root._key_owner, root._keys, "reverse_output_interner", False),
            (
                root._compose_owner,
                root._compose,
                "reverse_output_composition",
                False,
            ),
        )
        inventory = _owner_inventory(
            ledger, (owner for owner, _, _, _ in coordinate_stores)
        )
        all_valid = (
            root.ledger is ledger
            and type(root.owner) is ArenaToken
            and type(root.base) is int
            and root.base >= 2
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
                and value.owner is root.owner
                and value.kind == root._KIND
                and type(value.local_id) is int
                and 0 <= value.local_id < len(root._nodes)
            )

        for index, program in enumerate(root._nodes):
            valid = type(program) is ReverseCoordinateProgram
            try:
                if not valid:
                    raise TypeError("invalid reverse coordinate program")
                program.__post_init__()
                valid &= program.base == root.base
                if program.atom is not None:
                    valid &= _bounded_semantic_key(program.atom)
                reference = root._handle(index)
                valid &= coordinate_handle(reference)
                valid &= root.resolve(reference) is program
                valid &= root._keys.get(program) == index
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
                invalid.add((root._node_owner, id(program)))
                all_valid = False

        for program, index in root._keys.items():
            valid = type(program) is ReverseCoordinateProgram and type(index) is int
            try:
                if not valid:
                    raise TypeError("invalid reverse coordinate interner entry")
                valid &= 0 <= index < len(root._nodes)
                valid &= root._nodes[index] is program
                valid &= program.base == root.base
            except (TypeError, ValueError, IndexError, AttributeError):
                valid = False
            if valid:
                approved.add(id(program))
            else:
                invalid.add((root._key_owner, id(program)))
                all_valid = False
        all_valid &= len(root._keys) == len(root._nodes)

        for coordinate_key, coordinate_result in root._compose.items():
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
                first, second = root.resolve(before), root.resolve(after)
                actual = root.resolve(coordinate_result)
                valid &= first.executable and second.executable
                valid &= not (
                    first.normalized and (second.pair_steps or second.normalized)
                )
                expected = ReverseCoordinateProgram(
                    root.base,
                    first.pair_steps + second.pair_steps,
                    first.normalized or second.normalized,
                )
                valid &= actual == expected
                valid &= root._keys.get(expected) == coordinate_result.local_id
            except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                valid = False
            if valid:
                approved.update((id(coordinate_key), id(coordinate_result)))
            else:
                invalid.add((root._compose_owner, id(coordinate_key)))
                all_valid = False
        if all_valid:
            approved.update(id(store) for _, store, _, _ in coordinate_stores)
            approved.update(
                id(value) for value in (root.identity, root.primitive, root.terminal)
            )
    elif type(root) is ReverseFieldActionArena:
        coordinate_programs = root._coordinate_programs
        action_stores = (
            (root._residual_owner, root._residuals, "reverse_residual_node", True),
            (
                root._residual_key_owner,
                root._residual_keys,
                "reverse_residual_interner",
                False,
            ),
            (root._output_owner, root._outputs, "reverse_output_morphism", True),
            (
                root._output_key_owner,
                root._output_keys,
                "reverse_output_interner",
                False,
            ),
            (root._action_owner, root._actions, "reverse_field_action", True),
            (
                root._action_key_owner,
                root._action_keys,
                "reverse_action_interner",
                False,
            ),
            (
                root._compose_owner,
                root._compose,
                "reverse_action_composition",
                False,
            ),
            (
                root._transform_owner,
                root._transforms,
                "reverse_action_transform",
                False,
            ),
            (
                root._witness_owner,
                root._witnesses,
                "reverse_action_construction_witness",
                False,
            ),
            (
                root._semantic_identity_owner,
                root._semantic_identities,
                "reverse_action_semantic_identity",
                True,
            ),
            (
                root._semantic_identity_issued_owner,
                root._semantic_identity_issued,
                "reverse_action_semantic_identity_authority",
                False,
            ),
        )
        inventory = _owner_inventory(
            ledger, (owner for owner, _, _, _ in action_stores)
        )
        coordinate_reference = ledger._execution_roots.get(id(coordinate_programs))
        all_valid = (
            root.ledger is ledger
            and type(root.owner) is ArenaToken
            and type(root._base) is int
            and root._base >= 2
            and type(root._order) is int
            and 2 <= root._order <= 16
            and root._order & (root._order - 1) == 0
            and type(root._max_residual_classes) is int
            and 1 <= root._max_residual_classes <= 64
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
                and coordinate_programs.base == root._base
                and coordinate_reference is not None
                and coordinate_reference() is coordinate_programs
            )

        def action_handle(value: object) -> bool:
            return (
                type(value) is FieldCellActionID
                and type(value.owner) is ArenaToken
                and value.owner is root.owner
                and value.kind == root._ACTION_KIND
                and type(value.local_id) is int
                and 0 <= value.local_id < len(root._actions)
            )

        def residual_handle(value: object) -> bool:
            return (
                type(value) is ReverseDefectClassID
                and type(value.owner) is ArenaToken
                and value.owner is root.owner
                and value.kind == root._RESIDUAL_KIND
                and type(value.local_id) is int
                and 0 <= value.local_id < len(root._residuals)
            )

        def output_handle(value: object) -> bool:
            from number_compiler.hashlife.actions.field_actions import (
                CoordinateOutputMorphismID,
            )

            if type(value) is not CoordinateOutputMorphismID:
                return False
            expected_owner = (
                root.owner if coordinate_programs is None else coordinate_programs.owner
            )
            size = (
                len(root._outputs)
                if coordinate_programs is None
                else len(coordinate_programs._nodes)
            )
            return (
                type(value.owner) is ArenaToken
                and value.owner is expected_owner
                and value.kind == root._OUTPUT_KIND
                and type(value.local_id) is int
                and 0 <= value.local_id < size
            )

        residuals_valid = len(root._residuals) <= root._max_residual_classes
        for index, residual_value in enumerate(root._residuals):
            residual_reference = root._residual_keys.get(residual_value)
            if _semantic_slot(
                residual_value, residual_reference, index, residual_handle
            ):
                approved.update((id(residual_value), id(residual_reference)))
            else:
                invalid.add((root._residual_owner, id(residual_value)))
                residuals_valid = False
        residuals_valid &= len(root._residual_keys) == len(root._residuals)
        all_valid &= residuals_valid
        if coordinate_programs is None:
            outputs_valid = True
            for index, output_value in enumerate(root._outputs):
                output_reference = root._output_keys.get(output_value)
                if _semantic_slot(output_value, output_reference, index, output_handle):
                    approved.update((id(output_value), id(output_reference)))
                else:
                    invalid.add((root._output_owner, id(output_value)))
                    outputs_valid = False
            outputs_valid &= len(root._output_keys) == len(root._outputs)
            all_valid &= outputs_valid
        else:
            # Coordinate programs are the sole output store in this mode.
            all_valid &= not root._outputs and not root._output_keys
            if root._outputs or root._output_keys:
                invalid.add((root._output_owner, id(root._outputs)))
                invalid.add((root._output_key_owner, id(root._output_keys)))
            if all_valid:
                approved.update((id(root._outputs), id(root._output_keys)))

        def action_record(reference: FieldCellActionID) -> ReverseFieldAction:
            return root.resolve(reference)

        def expected_action_key(action: ReverseFieldAction) -> tuple[object, ...]:
            return root._action_key(
                action.base,
                root._block(action),
                action.carry_forward,
                action.carry_backward,
                action.residual,
                action.output,
                action.geometry,
            )

        actions_valid = True
        for index, action in enumerate(root._actions):
            valid = type(action) is ReverseFieldAction
            action_id = FieldCellActionID(root.owner, root._ACTION_KIND, index)
            try:
                if not valid:
                    raise TypeError("invalid reverse field-action record")
                valid &= action.base == root._base
                valid &= type(action.carry_forward).__name__ == "CarryFn"
                valid &= type(action.carry_backward).__name__ == "CarryFn"
                valid &= type(action.geometry) is ReverseGeometry
                action.geometry.__post_init__()
                block = root._block(action)
                valid &= root._canonical_block(block) == block
                valid &= residual_handle(action.residual)
                valid &= output_handle(action.output)
                valid &= root.resolve(action_id) is action
                valid &= root._action_keys.get(expected_action_key(action)) == action_id
                if coordinate_programs is None:
                    valid &= _bounded_semantic_key(root._residual_key(action.residual))
                    valid &= _bounded_semantic_key(root._output_key(action.output))
                else:
                    output_program = coordinate_programs.resolve(action.output)
                    valid &= output_program.base == root._base
                    if output_program.atom is not None:
                        valid &= _bounded_semantic_key(output_program.atom)
            except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                valid = False
            if valid:
                approved.add(id(action))
                approved.update(
                    id(getattr(action, name))
                    for name in (
                        "radial",
                        "innovation",
                        "carry_forward",
                        "carry_backward",
                        "residual",
                        "output",
                        "geometry",
                    )
                )
            else:
                invalid.add((root._action_owner, id(action)))
                actions_valid = False
        actions_valid &= len(root._action_keys) == len(root._actions)
        for action_key, action_reference in root._action_keys.items():
            valid = action_handle(action_reference) and type(action_key) is tuple
            try:
                action = action_record(action_reference)
                valid &= action_key == expected_action_key(action)
            except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                valid = False
            if valid:
                approved.update((id(action_key), id(action_reference)))
            else:
                invalid.add((root._action_key_owner, id(action_key)))
                actions_valid = False
        all_valid &= actions_valid

        identities_valid = (
            len(root._semantic_identities)
            == len(root._semantic_identity_issued)
            <= len(root._actions)
        )
        for identity_source, record in root._semantic_identities.items():
            valid = (
                action_handle(identity_source)
                and type(record) is tuple
                and root._semantic_identity_issued.get(identity_source) is record
            )
            try:
                if not valid:
                    raise TypeError("invalid reverse semantic identity cache entry")
                (
                    source,
                    action_seal,
                    radial_seal,
                    radial_identity,
                    digest,
                    behavior,
                ) = record
                action = action_record(identity_source)
                expected_identity = build_radial_identity(action.radial)
                valid &= (
                    type(source) is FieldCellActionID
                    and action_handle(source)
                    and source == identity_source
                    and type(action_seal) is int
                    and action_seal == id(action)
                    and type(radial_seal) is tuple
                    and len(radial_seal) == 2
                    and type(radial_seal[0]) is int
                    and type(radial_seal[1]) is int
                    and radial_seal == (action.radial.no_growth, action.radial.growth)
                    and type(radial_identity) is SemanticIdentity
                    and type(digest) is str
                    and radial_identity.digest == digest
                    and type(behavior) is tuple
                    and radial_identity.behavior is behavior
                    and radial_identity == expected_identity
                )
            except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                valid = False
            if valid:
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
                invalid.add((root._semantic_identity_owner, id(record)))
                identities_valid = False
        all_valid &= identities_valid

        def composition_valid(key: object, result: object) -> bool:
            if (
                type(key) is not tuple
                or len(key) != 2
                or not all(action_handle(item) for item in key)
                or not action_handle(result)
            ):
                return False
            typed_key = cast(tuple[FieldCellActionID, FieldCellActionID], key)
            before, after = typed_key
            result_id = cast(FieldCellActionID, result)
            try:
                first = action_record(before)
                second = action_record(after)
                actual = action_record(result_id)
                block = root._canonical_block(
                    root._block(first).then(root._block(second))
                )
                valid = (
                    actual.base == first.base == second.base
                    and actual.radial == block.radial
                    and actual.innovation == block.innovation
                    and actual.carry_forward
                    is compose_carry_fn(second.carry_forward, first.carry_forward)
                    and actual.carry_backward
                    is compose_carry_fn(second.carry_backward, first.carry_backward)
                    and actual.geometry == first.geometry.then(second.geometry)
                )
                if coordinate_programs is None:
                    residual_key = root._residual_compose(
                        root._residual_key(first.residual),
                        root._residual_key(second.residual),
                    )
                    output_key = root._output_compose(
                        root._output_key(first.output),
                        root._output_key(second.output),
                    )
                    valid &= _bounded_semantic_key(residual_key)
                    valid &= _bounded_semantic_key(output_key)
                    valid &= root._residual_keys.get(residual_key) == actual.residual
                    valid &= root._output_keys.get(output_key) == actual.output
                else:
                    before_program = coordinate_programs.resolve(first.output)
                    after_program = coordinate_programs.resolve(second.output)
                    actual_program = coordinate_programs.resolve(actual.output)
                    expected_program = ReverseCoordinateProgram(
                        root._base,
                        before_program.pair_steps + after_program.pair_steps,
                        before_program.normalized or after_program.normalized,
                    )
                    valid &= (
                        actual_program == expected_program
                        and coordinate_programs._keys.get(expected_program)
                        == result_id.local_id
                        and root._residual_key(actual.residual)
                        == root._residual_key(first.residual)
                        == root._residual_key(second.residual)
                    )
                return bool(valid)
            except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                return False

        compositions_valid = True
        for action_composition_key, action_composition_result in root._compose.items():
            valid = composition_valid(action_composition_key, action_composition_result)
            if valid:
                approved.update(
                    (id(action_composition_key), id(action_composition_result))
                )
            else:
                invalid.add((root._compose_owner, id(action_composition_key)))
                compositions_valid = False
        all_valid &= compositions_valid

        witnesses_valid = True
        for witness_result, witness in root._witnesses.items():
            valid = (
                action_handle(witness_result)
                and type(witness) is tuple
                and len(witness) == 2
                and all(action_handle(item) for item in witness)
            )
            if valid:
                valid &= root._compose.get(witness) == witness_result
                valid &= composition_valid(witness, witness_result)
            if valid:
                approved.update((id(witness_result), id(witness)))
            else:
                invalid.add((root._witness_owner, id(witness)))
                witnesses_valid = False
        all_valid &= witnesses_valid

        transforms_valid = True
        for transform_key, transform_result in root._transforms.items():
            valid = (
                type(transform_key) is tuple
                and len(transform_key) == 2
                and action_handle(transform_key[0])
                and type(transform_key[1]) is ActionTransform
                and int(transform_key[1]) & ~3 == 0
                and action_handle(transform_result)
            )
            try:
                if not valid:
                    raise TypeError("invalid reverse action transform entry")
                if coordinate_programs is not None:
                    valid = False
                else:
                    source_action = action_record(transform_key[0])
                    valid &= type(root._automorphisms) is ReverseActionAutomorphisms
                    (
                        block,
                        residual_key,
                        output_key,
                        carry_forward,
                        carry_backward,
                        geometry,
                    ) = root._transformed_components(source_action, transform_key[1])
                    valid &= _bounded_semantic_key(residual_key)
                    valid &= _bounded_semantic_key(output_key)
                    residual_result = root._residual_keys.get(residual_key)
                    output_result = root._output_keys.get(output_key)
                    valid &= residual_result is not None and output_result is not None
                    if residual_result is not None and output_result is not None:
                        expected_key = root._action_key(
                            source_action.base,
                            block,
                            carry_forward,
                            carry_backward,
                            residual_result,
                            output_result,
                            geometry,
                        )
                        valid &= root._action_keys.get(expected_key) == transform_result
            except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                valid = False
            if valid:
                approved.update((id(transform_key), id(transform_result)))
            else:
                invalid.add((root._transform_owner, id(transform_key)))
                transforms_valid = False
        all_valid &= transforms_valid
        if all_valid:
            approved.update(id(store) for _, store, _, _ in action_stores)
        else:
            invalid.add((root._action_owner, id(root)))
    return approved, invalid


def audit_reverse_field_action_owner(
    ledger: object, root: object
) -> PayloadAuditContribution:
    """Constrain one reverse action audit to its exact direct owned stores."""
    if not isinstance(ledger, ResourceLedger):
        raise TypeError("reverse field audit requires a resource ledger")
    from number_compiler.sequences.reverse_add.coordinate_program import (
        ReverseCoordinateProgramArena,
    )
    from number_compiler.sequences.reverse_add.field_action import (
        ReverseFieldActionArena,
    )

    bindings: tuple[tuple[int, str], ...]
    if type(root) is ReverseCoordinateProgramArena:
        bindings = (
            (root._node_owner, "_nodes"),
            (root._key_owner, "_keys"),
            (root._compose_owner, "_compose"),
        )
    elif type(root) is ReverseFieldActionArena:
        bindings = (
            (root._residual_owner, "_residuals"),
            (root._residual_key_owner, "_residual_keys"),
            (root._output_owner, "_outputs"),
            (root._output_key_owner, "_output_keys"),
            (root._action_owner, "_actions"),
            (root._action_key_owner, "_action_keys"),
            (root._compose_owner, "_compose"),
            (root._transform_owner, "_transforms"),
            (root._witness_owner, "_witnesses"),
            (root._semantic_identity_owner, "_semantic_identities"),
            (root._semantic_identity_issued_owner, "_semantic_identity_issued"),
        )
    else:
        return PayloadAuditContribution()

    containers = _owner_containers(ledger, (owner for owner, _ in bindings))
    approved_ids, invalid_rows = audit_reverse_field_action_root(
        root, ledger, containers
    )

    approved: list[PayloadAuditEntry] = []
    invalid: list[PayloadAuditEntry] = []
    anchor_owner = bindings[0][0]
    for owner, attribute in bindings:
        store = getattr(root, attribute)
        if isinstance(store, Mapping):
            values: Iterable[object] = (item for pair in store.items() for item in pair)
        elif isinstance(store, Sequence) and not isinstance(
            store, (str, bytes, bytearray)
        ):
            values = iter(store)
        else:
            values = iter(())
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
    """Validate the bounded local-action codec from its family-owned stores."""
    if not isinstance(ledger, ResourceLedger):
        raise TypeError("reverse codec audit requires a resource ledger")
    from number_compiler.arithmetic.contracts.block_effect import BoundarySide
    from number_compiler.hashlife.execution.field_images import (
        SourceCellID,
        SourceForestID,
    )
    from number_compiler.sequences.reverse_add.powered_local_codec import (
        ReverseLocalAction,
        ReverseLocalActionID,
        ReversePoweredLocalCodec,
    )

    if type(root) is not ReversePoweredLocalCodec:
        return PayloadAuditContribution()
    approved: list[PayloadAuditEntry] = []
    invalid: list[PayloadAuditEntry] = []
    valid_root = (
        root.ledger is ledger
        and root.sources.ledger is ledger
        and type(root._states) is tuple
        and len(root._states) == 2
        and len(root._state_ids) == 2
        and root._state_ids[0] is root._left_state_ids
        and root._state_ids[1] is root._right_state_ids
    )

    def accept(owner: int, value: object, valid: bool) -> None:
        entry = PayloadAuditEntry(owner, value)
        (approved if valid else invalid).append(entry)

    for states, state_ids, owner in zip(
        root._states, root._state_ids, root._state_owners, strict=True
    ):
        state_valid = valid_root and len(states) == len(state_ids)
        state_valid &= all(
            state_ids.get(state) == index for index, state in enumerate(states)
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

    node_owner = root._node_owner
    nodes_valid = valid_root
    for index, action in enumerate(root._nodes):
        valid = type(action) is ReverseLocalAction
        try:
            valid &= root.resolve(root._handle(index)) is action
            widths = (
                len(root._states[0]),
                len(root._states[0]),
                len(root._states[1]),
                len(root._states[1]),
            )
            for mapping, width in zip(
                (
                    action.left_forward,
                    action.left_reverse,
                    action.right_forward,
                    action.right_reverse,
                ),
                widths,
                strict=True,
            ):
                valid &= type(mapping) is tuple and len(mapping) == width
                valid &= all(
                    type(item) is int and 0 <= item < width for item in mapping
                )
            valid &= root._keys.get(action) == index
        except (TypeError, ValueError, IndexError, KeyError, AttributeError):
            valid = False
        accept(node_owner, action, valid)
        nodes_valid &= valid

    for action, index in root._keys.items():
        valid = (
            type(action) is ReverseLocalAction
            and type(index) is int
            and 0 <= index < len(root._nodes)
            and root._nodes[index] is action
        )
        accept(root._key_owner, action, valid)
        if not valid:
            nodes_valid = False

    compose_valid = valid_root
    for key, result in root._compose.items():
        valid = (
            type(key) is tuple
            and len(key) == 2
            and all(type(item) is ReverseLocalActionID for item in key)
        )
        try:
            left, right = key
            before, after, actual = (
                root.resolve(left),
                root.resolve(right),
                root.resolve(result),
            )
            expected = ReverseLocalAction(
                root._then(before.left_forward, after.left_forward),
                root._then(after.left_reverse, before.left_reverse),
                root._then(before.right_forward, after.right_forward),
                root._then(after.right_reverse, before.right_reverse),
            )
            valid &= actual == expected
        except (TypeError, ValueError, IndexError, AttributeError):
            valid = False
        accept(root._compose_owner, key, valid)
        compose_valid &= valid

    bindings_valid = valid_root
    for symbol, action_id in root._leaf_actions.items():
        try:
            valid = type(symbol) is int and 0 <= symbol <= root.blank
            valid &= root.resolve(action_id) == ReverseLocalAction(
                root._mapping(BoundarySide.LEFT, symbol),
                root._mapping(BoundarySide.LEFT, symbol),
                root._mapping(BoundarySide.RIGHT, symbol),
                root._mapping(BoundarySide.RIGHT, symbol),
            )
        except (TypeError, ValueError, IndexError, AttributeError):
            valid = False
        accept(root._leaf_owner, action_id, valid)
        bindings_valid &= valid
    for source, action_id in root._source_actions.items():
        try:
            valid = type(source) in (SourceCellID, SourceForestID)
            if type(source) is SourceCellID:
                root.sources.resolve(source)
            elif type(source) is SourceForestID:
                root.sources.resolve_forest(source)
            root.resolve(action_id)
        except (TypeError, ValueError, IndexError, AttributeError):
            valid = False
        accept(root._source_owner, source, valid)
        bindings_valid &= valid

    if not (nodes_valid and compose_valid and bindings_valid):
        invalid.append(PayloadAuditEntry(node_owner, root))
    return PayloadAuditContribution(tuple(approved), tuple(invalid))

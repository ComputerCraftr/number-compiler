"""Owner-aware validation for retained algebraic field-action records."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class FieldActionPayloadAudit:
    approved: frozenset[int]
    invalid: frozenset[tuple[int, int]]


def audit_field_action_payloads(ledger: ResourceLedger) -> FieldActionPayloadAudit:
    """Validate actual arena stores before treating their actions as semantic.

    An action class name alone grants no exemption. The owning arena, ledger,
    registered backing stores, scoped component handles, and bounded arithmetic
    invariants must all agree.
    """
    from number_compiler.resources.cylinder_innovation_payload_audit import (
        audit_cylinder_innovation_payloads,
    )
    from number_compiler.resources.symbolic_innovation_payload_audit import (
        audit_symbolic_innovation_payloads,
    )

    innovations = audit_symbolic_innovation_payloads(ledger)
    cylinders = audit_cylinder_innovation_payloads(ledger)
    scoped_approved = innovations.approved | cylinders.approved
    scoped_invalid = innovations.invalid | cylinders.invalid
    legacy_prefixes = (
        "number_compiler.hashlife.actions.field_actions",
        "number_compiler.hashlife.execution.field_",
        "number_compiler.sequences.collatz.field_action",
        "number_compiler.sequences.collatz.powered_local_codec",
        "number_compiler.sequences.reverse_add.powered_local_codec",
        "number_compiler.sequences.reverse_add.coordinate_program",
        "number_compiler.sequences.reverse_add.field_action",
    )
    if not any(
        type(root).__module__.startswith(legacy_prefixes)
        for root in ledger.iter_execution_roots()
    ):
        return FieldActionPayloadAudit(scoped_approved, scoped_invalid)

    from number_compiler.arithmetic.contracts.block_effect import BoundarySide
    from number_compiler.arithmetic.contracts.scoped_handles import (
        ActionProgramID,
    )
    from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
    from number_compiler.hashlife.actions.field_actions import (
        FieldCellActionID,
    )
    from number_compiler.hashlife.execution.continuations.generic_higher import (
        GenericHigherActionSchema,
        _GenericHigherAction,
    )
    from number_compiler.hashlife.execution.field_images import (
        SourceCellID,
        SourceForestID,
    )
    from number_compiler.sequences.collatz.field_action import (
        CollatzFieldActionArena,
        CollatzFieldActionID,
    )
    from number_compiler.sequences.collatz.powered_local_codec import (
        CollatzLocalAction,
        CollatzLocalActionID,
        CollatzPoweredLocalCodec,
    )
    from number_compiler.sequences.collatz.runtime_programs import (
        CollatzRuntimeProgram,
        CollatzRuntimeProgramArena,
    )
    from number_compiler.sequences.reverse_add.coordinate_program import (
        ReverseCoordinateProgramArena,
    )
    from number_compiler.sequences.reverse_add.field_action import (
        ReverseFieldActionArena,
    )
    from number_compiler.sequences.reverse_add.powered_local_codec import (
        ReverseLocalAction,
        ReverseLocalActionID,
        ReversePoweredLocalCodec,
    )

    containers = dict(ledger.iter_containers())
    container_owners = {id(value): owner for owner, value in containers.items()}
    approved: set[int] = set(scoped_approved)
    invalid: set[tuple[int, int]] = set(scoped_invalid)
    for root in ledger.iter_execution_roots():
        if type(root) in (ReverseCoordinateProgramArena, ReverseFieldActionArena):
            from number_compiler.resources.reverse_field_action_payload_audit import (
                audit_reverse_field_action_root,
            )

            reverse_approved, reverse_invalid = audit_reverse_field_action_root(
                root, ledger, containers
            )
            approved.update(reverse_approved)
            invalid.update(reverse_invalid)
        elif type(root) is GenericHigherActionSchema:
            stores = root._nodes, root._keys
            all_valid = (
                root.ledger is ledger
                and root.runtime.ledger is ledger
                and (
                    containers.get(root._node_owner) is root._nodes
                    and containers.get(root._key_owner) is root._keys
                )
            )

            def exact_action(left: object, right: object) -> bool:
                return (
                    type(left) is type(right) is ActionProgramID
                    and left.owner is right.owner
                    and left.kind == right.kind
                    and type(left.local_id) is type(right.local_id) is int
                    and left.local_id == right.local_id
                )

            def exact_field(left: object, right: object) -> bool:
                return (
                    type(left) is type(right) is FieldCellActionID
                    and left.owner is right.owner
                    and left.kind == right.kind
                    and type(left.local_id) is type(right.local_id) is int
                    and left.local_id == right.local_id
                )

            for index, record in enumerate(root._nodes):
                valid = type(record) is _GenericHigherAction
                try:
                    if not valid:
                        raise TypeError("invalid generic higher record")
                    node = root.runtime.actions.resolve(record.original)
                    handle = root._handle(index)
                    valid &= root._resolve(handle) is record
                    expected = None
                    if node.kind == "compose":
                        originals = (
                            root.runtime.actions.reference(node.left),
                            root.runtime.actions.reference(node.right),
                        )
                        expected = tuple(
                            root._handle(root._keys[item]) for item in originals
                        )
                    if expected is None:
                        valid &= record.children is None
                    else:
                        valid &= (
                            type(record.children) is tuple
                            and len(record.children) == 2
                            and all(
                                exact_field(actual, wanted)
                                for actual, wanted in zip(
                                    record.children, expected, strict=True
                                )
                            )
                        )
                    matches = [
                        value
                        for key, value in root._keys.items()
                        if exact_action(key, record.original)
                    ]
                    valid &= (
                        len(matches) == 1
                        and type(matches[0]) is int
                        and matches[0] == index
                    )
                except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(record))
                else:
                    invalid.add((root._node_owner, id(record)))
                    all_valid = False
            for original, index in root._keys.items():
                try:
                    valid = (
                        type(original) is ActionProgramID
                        and type(index) is int
                        and 0 <= index < len(root._nodes)
                    )
                    if not valid:
                        raise TypeError("invalid generic higher interner entry")
                    root.runtime.actions.resolve(original)
                    valid &= exact_action(root._nodes[index].original, original)
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.update((id(original), id(index)))
                else:
                    invalid.add((root._key_owner, id(original)))
                    all_valid = False
            all_valid &= len(root._keys) == len(root._nodes)
            if all_valid:
                approved.update(id(value) for value in stores)
        elif type(root) is ReversePoweredLocalCodec:
            local_stores = (
                root._nodes,
                root._keys,
                root._compose,
                root._leaf_actions,
                root._source_actions,
                *root._state_ids,
            )
            valid_root = (
                root.ledger is ledger
                and all(id(value) in container_owners for value in local_stores)
                and len(root._states) == len(root._state_ids) == 2
            )
            for states, state_ids in zip(root._states, root._state_ids, strict=True):
                valid_root &= len(states) == len(state_ids)
                valid_root &= all(
                    state_ids.get(state) == index for index, state in enumerate(states)
                )
                if valid_root:
                    # These are the frozen finite boundary universe of the
                    # primitive kernel.  Treating the index map as an
                    # untyped numeric aggregate made the representation audit
                    # depend on the powered action's incidental state bound
                    # (and rejected the primitive N=1 route).  The map is a
                    # dense codec, not packed future digit state.
                    approved.update(id(state) for state in states)
            nodes_valid = valid_root
            for index, local_action in enumerate(root._nodes):
                valid = type(local_action) is ReverseLocalAction
                try:
                    valid &= (
                        root.resolve(
                            ReverseLocalActionID(
                                root.owner,
                                root._KIND,
                                index,
                            )
                        )
                        is local_action
                    )
                    widths = (
                        len(root._states[0]),
                        len(root._states[0]),
                        len(root._states[1]),
                        len(root._states[1]),
                    )
                    for mapping, width in zip(
                        (
                            local_action.left_forward,
                            local_action.left_reverse,
                            local_action.right_forward,
                            local_action.right_reverse,
                        ),
                        widths,
                        strict=True,
                    ):
                        valid &= type(mapping) is tuple and len(mapping) == width
                        valid &= all(
                            type(item) is int and 0 <= item < width for item in mapping
                        )
                    valid &= root._keys.get(local_action) == index
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(local_action))
                else:
                    invalid.add((root._node_owner, id(local_action)))
                    nodes_valid = False
            compose_valid = valid_root
            for key, local_result in root._compose.items():
                valid = (
                    type(key) is tuple
                    and len(key) == 2
                    and all(type(item) is ReverseLocalActionID for item in key)
                )
                try:
                    left, right = key
                    a, b, actual = (
                        root.resolve(left),
                        root.resolve(right),
                        root.resolve(local_result),
                    )
                    valid &= actual == ReverseLocalAction(
                        root._then(a.left_forward, b.left_forward),
                        root._then(b.left_reverse, a.left_reverse),
                        root._then(a.right_forward, b.right_forward),
                        root._then(b.right_reverse, a.right_reverse),
                    )
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(key))
                else:
                    invalid.add((root._compose_owner, id(key)))
                    compose_valid = False
            bindings_valid = valid_root
            for symbol, local_reference in root._leaf_actions.items():
                try:
                    valid = type(symbol) is int and 0 <= symbol <= root.blank
                    valid &= root.resolve(local_reference) == ReverseLocalAction(
                        root._mapping(BoundarySide.LEFT, symbol),
                        root._mapping(BoundarySide.LEFT, symbol),
                        root._mapping(BoundarySide.RIGHT, symbol),
                        root._mapping(BoundarySide.RIGHT, symbol),
                    )
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if not valid:
                    invalid.add((root._leaf_owner, id(local_reference)))
                    bindings_valid = False
            for source_reference, local_reference in root._source_actions.items():
                try:
                    valid = type(source_reference) in (SourceCellID, SourceForestID)
                    if type(source_reference) is SourceCellID:
                        root.sources.resolve(source_reference)
                    elif type(source_reference) is SourceForestID:
                        root.sources.resolve_forest(source_reference)
                    root.resolve(local_reference)
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(source_reference))
                else:
                    invalid.add((root._source_owner, id(source_reference)))
                    bindings_valid = False
            if nodes_valid and compose_valid and bindings_valid:
                approved.update(id(value) for value in local_stores)
        elif type(root) is CollatzFieldActionArena:
            collatz_stores = (
                (root._node_owner, root._nodes),
                (root._key_owner, root._keys),
                (root._output_node_owner, root._output_programs),
                (root._output_key_owner, root._output_ids),
                (root._witness_owner, root._witnesses),
                (root._composition_owner, root._compositions),
            )
            if root.ledger is not ledger or any(
                containers.get(owner) is not store for owner, store in collatz_stores
            ):
                invalid.add((root._node_owner, id(root)))
                continue
            for index, collatz_action in enumerate(root._nodes):
                try:
                    collatz_reference = CollatzFieldActionID(
                        root.owner,
                        root.action_kind,
                        index,
                    )
                    root._validate_action(collatz_action)
                    valid = root.resolve(collatz_reference) is collatz_action
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(collatz_action))
                    approved.update(
                        id(getattr(collatz_action, name))
                        for name in (
                            "character",
                            "root_action",
                            "affine_action",
                            "innovation",
                            "defect",
                            "cocycles",
                            "output_morphism",
                            "geometry",
                        )
                    )
                else:
                    invalid.add((root._node_owner, id(collatz_action)))
            for semantic_key, collatz_reference in root._keys.items():
                valid = type(semantic_key) is SemanticIdentity
                try:
                    valid &= root.semantic_identity(collatz_reference) == semantic_key
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.update((id(semantic_key), id(collatz_reference)))
                else:
                    invalid.add((root._key_owner, id(semantic_key)))
            for index, collatz_program in enumerate(root._output_programs):
                try:
                    root._validate_program("output", collatz_program)
                    valid = root._output_ids.get(collatz_program) == index
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(collatz_program))
                else:
                    invalid.add((root._output_node_owner, id(collatz_program)))
            for parent, witness in root._witnesses.items():
                try:
                    valid = type(parent) is CollatzFieldActionID
                    root.resolve(parent)
                    valid &= type(witness) is tuple and len(witness) == 2
                    valid &= all(root.resolve(child) is not None for child in witness)
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(witness))
                    approved.update(id(child) for child in witness)
                else:
                    invalid.add((root._witness_owner, id(witness)))
            compositions_valid = True
            for composition, composition_result in root._compositions.items():
                valid = type(composition) is tuple and len(composition) == 2
                try:
                    valid &= all(
                        root.resolve(child) is not None for child in composition
                    )
                    root.resolve(composition_result)
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.update((id(composition), id(composition_result)))
                else:
                    invalid.add((root._composition_owner, id(composition)))
                    compositions_valid = False
            if compositions_valid and not any(
                owner == root._node_owner for owner, _ in invalid
            ):
                approved.update(id(store) for _, store in collatz_stores)
        elif type(root) is CollatzPoweredLocalCodec:
            collatz_local_stores = (
                root._nodes,
                root._keys,
                root._compose,
                root._leaf_actions,
                root._source_actions,
                root._binary_source_actions,
            )
            valid_root = root.ledger is ledger and all(
                id(value) in container_owners for value in collatz_local_stores
            )
            all_valid = valid_root
            for index, collatz_local_action in enumerate(root._nodes):
                valid = type(collatz_local_action) is CollatzLocalAction
                try:
                    collatz_local_action.__post_init__()
                    valid &= (
                        root.resolve(
                            CollatzLocalActionID(
                                root.owner,
                                root._KIND,
                                index,
                            )
                        )
                        is collatz_local_action
                    )
                    valid &= root._keys.get(collatz_local_action) == index
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(collatz_local_action))
                else:
                    invalid.add((root._node_owner, id(collatz_local_action)))
                    all_valid = False
            for collatz_key, collatz_composition_result in root._compose.items():
                valid = (
                    type(collatz_key) is tuple
                    and len(collatz_key) == 2
                    and all(type(item) is CollatzLocalActionID for item in collatz_key)
                )
                try:
                    collatz_left, collatz_right = collatz_key
                    collatz_a = root.resolve(collatz_left)
                    collatz_b = root.resolve(collatz_right)
                    valid &= root.resolve(
                        collatz_composition_result
                    ) == CollatzLocalAction(
                        root._then(collatz_a.forward, collatz_b.forward),
                        root._then(collatz_b.reverse, collatz_a.reverse),
                    )
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.update((id(collatz_key), id(collatz_composition_result)))
                else:
                    invalid.add((root._compose_owner, id(collatz_key)))
                    all_valid = False
            for symbol, collatz_leaf_result in root._leaf_actions.items():
                try:
                    valid = type(symbol) is int and 0 <= symbol < 4
                    mapping = tuple(
                        root.kernel.transition(state, symbol) for state in range(3)
                    )
                    valid &= root.resolve(collatz_leaf_result) == CollatzLocalAction(
                        (mapping[0], mapping[1], mapping[2]),
                        (mapping[0], mapping[1], mapping[2]),
                    )
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if not valid:
                    invalid.add((root._leaf_owner, id(collatz_leaf_result)))
                    all_valid = False
            for source_store, source_owner in (
                (root._source_actions, root._source_owner),
                (root._binary_source_actions, root._binary_source_owner),
            ):
                for source_reference, collatz_source_result in source_store.items():
                    valid = type(source_reference) in (SourceCellID, SourceForestID)
                    try:
                        if type(source_reference) is SourceCellID:
                            root.sources.resolve(source_reference)
                        elif type(source_reference) is SourceForestID:
                            root.sources.resolve_forest(source_reference)
                        else:
                            valid = False
                        root.resolve(collatz_source_result)
                    except (TypeError, ValueError, IndexError, AttributeError):
                        valid = False
                    if valid:
                        approved.update(
                            (id(source_reference), id(collatz_source_result))
                        )
                    else:
                        invalid.add((source_owner, id(source_reference)))
                        all_valid = False
            if all_valid:
                approved.update(id(value) for value in collatz_local_stores)
        elif type(root) is CollatzRuntimeProgramArena:
            program_stores = root._nodes, root._keys, root._compositions
            all_valid = root.ledger is ledger and all(
                id(value) in container_owners for value in program_stores
            )
            for index, runtime_program in enumerate(root._nodes):
                valid = type(runtime_program) is CollatzRuntimeProgram
                stored_handle = None
                try:
                    runtime_program.__post_init__()
                    program_handle = ActionProgramID(root.owner, root._KIND, index)
                    stored_handle = root._keys.get(
                        (runtime_program.role, runtime_program.exponent)
                    )
                    valid &= root.resolve(program_handle) is runtime_program
                    valid &= stored_handle == program_handle
                    for child in (runtime_program.before, runtime_program.after):
                        if child is not None:
                            root.resolve(child)
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(runtime_program))
                    if stored_handle is not None:
                        approved.add(id(stored_handle))
                else:
                    invalid.add((root._node_owner, id(runtime_program)))
                    all_valid = False
            for runtime_key, program_result in root._compositions.items():
                valid = (
                    type(runtime_key) is tuple
                    and len(runtime_key) == 3
                    and type(runtime_key[0]) is str
                )
                try:
                    runtime_first = root.resolve(runtime_key[1])
                    runtime_second = root.resolve(runtime_key[2])
                    runtime_actual = root.resolve(program_result)
                    valid &= (
                        runtime_first.role
                        == runtime_second.role
                        == runtime_key[0]
                        == runtime_actual.role
                    )
                    valid &= (
                        runtime_actual.exponent
                        == runtime_first.exponent + runtime_second.exponent
                    )
                    valid &= runtime_actual.before == runtime_key[1]
                    valid &= runtime_actual.after == runtime_key[2]
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.update((id(runtime_key), id(program_result)))
                else:
                    invalid.add((root._compose_owner, id(runtime_key)))
                    all_valid = False
            if all_valid:
                approved.update(id(value) for value in program_stores)
    return FieldActionPayloadAudit(frozenset(approved), frozenset(invalid))


__all__ = ["FieldActionPayloadAudit", "audit_field_action_payloads"]

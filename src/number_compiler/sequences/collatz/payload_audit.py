"""Read-only validators for Collatz-owned retained action and range stores."""

from __future__ import annotations

from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditEntry,
    PayloadAuditStoreBinding,
    register_payload_audit_contract,
)


def register_collatz_field_action_contract(root: object) -> None:
    from number_compiler.sequences.collatz.field_action import CollatzFieldActionArena

    if type(root) is not CollatzFieldActionArena:
        raise TypeError("Collatz field-action audit requires its exact arena")
    stores = (
        PayloadAuditStoreBinding(root._node_owner, "_nodes", "collatz_field_action"),
        PayloadAuditStoreBinding(
            root._key_owner, "_keys", "collatz_field_action_interner"
        ),
        PayloadAuditStoreBinding(
            root._output_node_owner,
            "_output_programs",
            "coordinate_output_morphism",
        ),
        PayloadAuditStoreBinding(
            root._output_key_owner,
            "_output_ids",
            "coordinate_output_interner",
        ),
        PayloadAuditStoreBinding(
            root._witness_owner,
            "_witnesses",
            "action_construction_metadata",
        ),
        PayloadAuditStoreBinding(
            root._composition_owner,
            "_compositions",
            "action_construction_metadata",
        ),
    )
    register_payload_audit_contract(
        root.ledger, root, "collatz", stores, audit_collatz_field_action
    )


def audit_collatz_field_action(
    ledger: object, root: object
) -> PayloadAuditContribution:
    """Validate action/key/output/witness rows without ledger mutation."""
    from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
    from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.collatz.field_action import (
        CollatzFieldAction,
        CollatzFieldActionArena,
        CollatzFieldActionID,
    )

    if type(ledger) is not ResourceLedger or type(root) is not CollatzFieldActionArena:
        raise TypeError("Collatz field-action audit received a foreign owner")
    arena = root
    approved: list[PayloadAuditEntry] = []
    invalid: list[PayloadAuditEntry] = []

    def accept(owner: int, value: object) -> None:
        approved.append(PayloadAuditEntry(owner, value))

    def reject(owner: int, value: object) -> None:
        invalid.append(PayloadAuditEntry(owner, value))

    if arena.ledger is not ledger:
        reject(arena._node_owner, arena)
        return PayloadAuditContribution((), tuple(invalid))

    for index, action in enumerate(arena._nodes):
        try:
            valid = type(action) is CollatzFieldAction
            arena._validate_action(action)
            reference = CollatzFieldActionID(arena.owner, arena.action_kind, index)
            valid &= arena.resolve(reference) is action
        except (TypeError, ValueError, IndexError, AttributeError):
            valid = False
        (accept if valid else reject)(arena._node_owner, action)

    for key, reference in arena._keys.items():
        try:
            valid = type(key) is SemanticIdentity
            valid &= type(reference) is CollatzFieldActionID
            valid &= arena.semantic_identity(reference) == key
        except (TypeError, ValueError, IndexError, AttributeError):
            valid = False
        (accept if valid else reject)(arena._key_owner, key)
        (accept if valid else reject)(arena._key_owner, reference)

    for index, program in enumerate(arena._output_programs):
        try:
            valid = type(program) is ActionProgramID
            arena._validate_program("output", program)
            valid &= arena._output_ids.get(program) == index
        except (TypeError, ValueError, IndexError, AttributeError):
            valid = False
        (accept if valid else reject)(arena._output_node_owner, program)

    for program, index in arena._output_ids.items():
        valid = type(program) is ActionProgramID and type(index) is int
        valid &= 0 <= index < len(arena._output_programs)
        if valid:
            valid &= arena._output_programs[index] == program
        (accept if valid else reject)(arena._output_key_owner, program)
        (accept if valid else reject)(arena._output_key_owner, index)

    for parent, children in arena._witnesses.items():
        try:
            valid = type(parent) is CollatzFieldActionID
            arena.resolve(parent)
            valid &= type(children) is tuple and len(children) == 2
            if valid:
                for child in children:
                    arena.resolve(child)
        except (TypeError, ValueError, IndexError, AttributeError):
            valid = False
        (accept if valid else reject)(arena._witness_owner, parent)
        (accept if valid else reject)(arena._witness_owner, children)

    for operands, result in arena._compositions.items():
        try:
            valid = type(operands) is tuple and len(operands) == 2
            if valid:
                first, second = operands
                arena.resolve(first)
                arena.resolve(second)
            arena.resolve(result)
        except (TypeError, ValueError, IndexError, AttributeError):
            valid = False
        (accept if valid else reject)(arena._composition_owner, operands)
        (accept if valid else reject)(arena._composition_owner, result)

    return PayloadAuditContribution(tuple(approved), tuple(invalid))


def register_collatz_range_contract(root: object) -> None:
    from number_compiler.sequences.collatz.range_runtime import CollatzRadix4RangeArena

    if type(root) is not CollatzRadix4RangeArena:
        raise TypeError("Collatz range audit requires its exact arena")
    stores = (
        PayloadAuditStoreBinding(root._node_owner, "_nodes", "finite_port"),
        PayloadAuditStoreBinding(root._key_owner, "_keys", "transfer_interner"),
        PayloadAuditStoreBinding(
            root._binding_owner,
            "_audit_bindings",
            "spatial_binding",
        ),
    )
    register_payload_audit_contract(
        root.ledger, root, "collatz", stores, audit_collatz_range
    )


def audit_collatz_range(ledger: object, root: object) -> PayloadAuditContribution:
    """Validate exact radix-4 range nodes, interning, and source bindings."""
    from number_compiler.hashlife.execution.field_images import SourceCellID
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.collatz.range_runtime import (
        CollatzRadix4Range,
        CollatzRadix4RangeArena,
        CollatzRadix4RangeID,
    )

    if type(ledger) is not ResourceLedger or type(root) is not CollatzRadix4RangeArena:
        raise TypeError("Collatz range audit received a foreign owner")
    arena = root
    approved: list[PayloadAuditEntry] = []
    invalid: list[PayloadAuditEntry] = []

    def record(owner: int, value: object, valid: bool) -> None:
        entry = PayloadAuditEntry(owner, value)
        (approved if valid else invalid).append(entry)

    if arena.ledger is not ledger:
        invalid.append(PayloadAuditEntry(arena._node_owner, arena))
        return PayloadAuditContribution((), tuple(invalid))

    for index, value in enumerate(arena._nodes):
        try:
            valid = type(value) is CollatzRadix4Range
            value.__post_init__()
            valid &= arena._keys.get(value) == index
            reference = CollatzRadix4RangeID(arena.owner, arena._KIND, index)
            valid &= arena.resolve(reference) is value
        except (TypeError, ValueError, IndexError, AttributeError):
            valid = False
        record(arena._node_owner, value, valid)

    for value, index in arena._keys.items():
        valid = type(value) is CollatzRadix4Range and type(index) is int
        valid &= 0 <= index < len(arena._nodes)
        if valid:
            valid &= arena._nodes[index] == value
        record(arena._key_owner, value, valid)
        record(arena._key_owner, index, valid)

    for source, result in arena._bindings.items():
        try:
            valid = type(source) is SourceCellID
            arena.sources.resolve(source)
            valid &= type(result) is CollatzRadix4RangeID
            arena.resolve(result)
        except (TypeError, ValueError, IndexError, AttributeError):
            valid = False
        record(arena._binding_owner, source, valid)
        record(arena._binding_owner, result, valid)

    return PayloadAuditContribution(tuple(approved), tuple(invalid))


def register_collatz_local_codec_contract(root: object) -> None:
    from number_compiler.sequences.collatz.powered_local_codec import (
        CollatzPoweredLocalCodec,
    )

    if type(root) is not CollatzPoweredLocalCodec:
        raise TypeError("Collatz local-codec audit requires its exact arena")
    stores = (
        PayloadAuditStoreBinding(root._node_owner, "_nodes", "collatz_local_action"),
        PayloadAuditStoreBinding(
            root._key_owner, "_keys", "collatz_local_action_interner"
        ),
        PayloadAuditStoreBinding(
            root._compose_owner, "_compose", "collatz_local_action_composition"
        ),
        PayloadAuditStoreBinding(
            root._leaf_owner, "_leaf_actions", "collatz_local_leaf_binding"
        ),
        PayloadAuditStoreBinding(
            root._source_owner, "_source_actions", "collatz_local_source_binding"
        ),
        PayloadAuditStoreBinding(
            root._binary_source_owner,
            "_binary_source_actions",
            "collatz_local_source_binding",
        ),
    )
    register_payload_audit_contract(
        root.ledger, root, "collatz", stores, audit_collatz_local_codec
    )


def audit_collatz_local_codec(ledger: object, root: object) -> PayloadAuditContribution:
    """Audit the local action codec and its source-bound projections."""
    from number_compiler.arithmetic.automata.symmetry_powering import FiniteKernel
    from number_compiler.hashlife.execution.field_images import (
        SourceCellID,
        SourceForestID,
    )
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.collatz.powered_local_codec import (
        CollatzLocalAction,
        CollatzLocalActionID,
        CollatzPoweredLocalCodec,
    )

    if type(ledger) is not ResourceLedger or type(root) is not CollatzPoweredLocalCodec:
        raise TypeError("Collatz local-codec audit received a foreign owner")
    arena = root
    approved: list[PayloadAuditEntry] = []
    invalid: list[PayloadAuditEntry] = []

    def record(owner: int, value: object, valid: bool) -> None:
        entry = PayloadAuditEntry(owner, value)
        (approved if valid else invalid).append(entry)

    kernel = arena.kernel
    root_valid = (
        arena.ledger is ledger
        and arena.sources.ledger is ledger
        and type(kernel) is FiniteKernel
        and kernel.state_count == 3
        and kernel.alphabet_size == 4
    )
    if not root_valid:
        invalid.append(PayloadAuditEntry(arena._node_owner, arena))

    for index, action in enumerate(arena._nodes):
        try:
            valid = type(action) is CollatzLocalAction
            action.__post_init__()
            reference = CollatzLocalActionID(arena.owner, arena._KIND, index)
            valid &= arena.resolve(reference) is action
            valid &= arena._keys.get(action) == index
        except (TypeError, ValueError, IndexError, AttributeError):
            valid = False
        record(arena._node_owner, action, valid)

    for action, index in arena._keys.items():
        valid = type(action) is CollatzLocalAction and type(index) is int
        valid &= 0 <= index < len(arena._nodes)
        if valid:
            valid &= arena._nodes[index] is action
        record(arena._key_owner, action, valid)
        record(arena._key_owner, index, valid)

    for operands, result in arena._compose.items():
        valid = (
            type(operands) is tuple
            and len(operands) == 2
            and all(type(item) is CollatzLocalActionID for item in operands)
        )
        try:
            left_id, right_id = operands
            left, right = arena.resolve(left_id), arena.resolve(right_id)
            expected = CollatzLocalAction(
                arena._then(left.forward, right.forward),
                arena._then(right.reverse, left.reverse),
            )
            valid &= arena.resolve(result) == expected
        except (TypeError, ValueError, IndexError, AttributeError):
            valid = False
        record(arena._compose_owner, operands, valid)
        record(arena._compose_owner, result, valid)

    for symbol, result in arena._leaf_actions.items():
        try:
            valid = type(symbol) is int and 0 <= symbol < 4
            mapping: tuple[int, int, int] = (
                kernel.transition(0, symbol),
                kernel.transition(1, symbol),
                kernel.transition(2, symbol),
            )
            expected = CollatzLocalAction(
                (mapping[0], mapping[1], mapping[2]),
                (mapping[0], mapping[1], mapping[2]),
            )
            valid &= arena.resolve(result) == expected
        except (TypeError, ValueError, IndexError, AttributeError):
            valid = False
        record(arena._leaf_owner, symbol, valid)
        record(arena._leaf_owner, result, valid)

    for store, owner in (
        (arena._source_actions, arena._source_owner),
        (arena._binary_source_actions, arena._binary_source_owner),
    ):
        for source, result in store.items():
            try:
                if type(source) is SourceCellID:
                    arena.sources.resolve(source)
                elif type(source) is SourceForestID:
                    arena.sources.resolve_forest(source)
                else:
                    raise TypeError("invalid Collatz local source reference")
                arena.resolve(result)
                valid = root_valid
            except (TypeError, ValueError, IndexError, AttributeError):
                valid = False
            record(owner, source, valid)
            record(owner, result, valid)

    return PayloadAuditContribution(tuple(approved), tuple(invalid))


def register_collatz_runtime_program_contract(root: object) -> None:
    from number_compiler.sequences.collatz.runtime_programs import (
        CollatzRuntimeProgramArena,
    )

    if type(root) is not CollatzRuntimeProgramArena:
        raise TypeError("Collatz runtime audit requires its exact arena")
    stores = (
        PayloadAuditStoreBinding(root._node_owner, "_nodes", "action_program"),
        PayloadAuditStoreBinding(root._key_owner, "_keys", "action_program_interner"),
        PayloadAuditStoreBinding(
            root._compose_owner, "_compositions", "action_construction_metadata"
        ),
        PayloadAuditStoreBinding(
            root._identity_owner, "_semantic_identities", "semantic_identity_cache"
        ),
        PayloadAuditStoreBinding(
            root._identity_authority_owner,
            "_semantic_identity_authority",
            "semantic_identity_cache_authority",
        ),
    )
    register_payload_audit_contract(
        root.ledger, root, "collatz", stores, audit_collatz_runtime_programs
    )


def audit_collatz_runtime_programs(
    ledger: object, root: object
) -> PayloadAuditContribution:
    """Validate canonical program nodes, compositions and identity witnesses."""
    from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
    from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.collatz.runtime_programs import (
        CollatzRuntimeProgram,
        CollatzRuntimeProgramArena,
    )

    if (
        type(ledger) is not ResourceLedger
        or type(root) is not CollatzRuntimeProgramArena
    ):
        raise TypeError("Collatz runtime-program audit received a foreign owner")
    arena = root
    approved: list[PayloadAuditEntry] = []
    invalid: list[PayloadAuditEntry] = []

    def record(owner: int, value: object, valid: bool) -> None:
        entry = PayloadAuditEntry(owner, value)
        (approved if valid else invalid).append(entry)

    identity_row = ledger.inventory_owner(arena._identity_owner)
    authority_row = ledger.inventory_owner(arena._identity_authority_owner)
    root_valid = (
        arena.ledger is ledger
        and identity_row is not None
        and identity_row.role == "semantic_identity_cache"
        and identity_row.entries == len(arena._semantic_identities)
        and identity_row.nodes == arena._identity_storage_nodes
        and authority_row is not None
        and authority_row.role == "semantic_identity_cache_authority"
        and authority_row.entries == len(arena._semantic_identity_authority)
        and authority_row.nodes == 0
        and len(arena._semantic_identities) == len(arena._semantic_identity_authority)
    )
    if not root_valid:
        invalid.append(PayloadAuditEntry(arena._node_owner, arena))

    for identity_key, identity_record in arena._semantic_identities.items():
        valid = (
            type(identity_key) is tuple
            and len(identity_key) == 2
            and type(identity_key[0]) is str
            and identity_key[0]
            in {"root", "affine", "output", "physical-tick", "valuation", "frame"}
            and type(identity_key[1]) is int
            and identity_key[1] >= 0
            and arena._semantic_identity_authority.get(identity_key) is identity_record
            and type(identity_record) is tuple
            and len(identity_record) == 4
        )
        try:
            identity, digest, behavior, exponent = identity_record
            if type(behavior) is not tuple or len(behavior) != 3:
                raise ValueError("malformed Collatz identity behavior")
            descriptor = behavior[2]
            if type(descriptor) is not tuple or len(descriptor) != 3:
                raise ValueError("malformed Collatz exponent descriptor")
            limbs = descriptor[2]
            valid &= (
                type(identity) is SemanticIdentity
                and type(digest) is str
                and identity.digest == digest
                and identity.behavior is behavior
                and type(exponent) is int
                and exponent == identity_key[1]
                and behavior[0] == "collatz-runtime-program-v2-binary-exponent"
                and behavior[1] == identity_key[0]
                and descriptor[0] == "exact-exponent-u64-v1"
                and descriptor[1] == exponent.bit_length()
                and type(limbs) is tuple
                and all(type(limb) is int and 0 <= limb < 1 << 64 for limb in limbs)
                and sum(limb << (64 * index) for index, limb in enumerate(limbs))
                == exponent
            )
            identity.validate()
        except (TypeError, ValueError, IndexError, KeyError, AttributeError):
            valid = False
        record(arena._identity_owner, identity_key, valid)
        record(arena._identity_owner, identity_record, valid)
        record(arena._identity_authority_owner, identity_key, valid)
        record(arena._identity_authority_owner, identity_record, valid)

    for index, program in enumerate(arena._nodes):
        valid = type(program) is CollatzRuntimeProgram
        stored_handle = None
        try:
            program.__post_init__()
            handle = ActionProgramID(arena.owner, arena._KIND, index)
            stored_handle = arena._keys.get((program.role, program.exponent))
            valid &= arena.resolve(handle) is program
            valid &= stored_handle == handle
            for child in (program.before, program.after):
                if child is not None:
                    arena.resolve(child)
        except (TypeError, ValueError, IndexError, AttributeError):
            valid = False
        record(arena._node_owner, program, valid)
        if stored_handle is not None:
            record(arena._key_owner, stored_handle, valid)

    for interner_key, handle in arena._keys.items():
        valid = (
            type(interner_key) is tuple
            and len(interner_key) == 2
            and type(interner_key[0]) is str
            and type(interner_key[1]) is int
            and type(handle) is ActionProgramID
        )
        try:
            program = arena.resolve(handle)
            valid &= (program.role, program.exponent) == interner_key
        except (TypeError, ValueError, IndexError, AttributeError):
            valid = False
        record(arena._key_owner, interner_key, valid)
        record(arena._key_owner, handle, valid)

    for composition_key, result in arena._compositions.items():
        valid = (
            type(composition_key) is tuple
            and len(composition_key) == 3
            and type(composition_key[0]) is str
        )
        try:
            first, second = (
                arena.resolve(composition_key[1]),
                arena.resolve(composition_key[2]),
            )
            actual = arena.resolve(result)
            valid &= first.role == second.role == composition_key[0] == actual.role
            valid &= actual.exponent == first.exponent + second.exponent
            valid &= (
                actual.before == composition_key[1]
                and actual.after == composition_key[2]
            )
        except (TypeError, ValueError, IndexError, AttributeError):
            valid = False
        record(arena._compose_owner, composition_key, valid)
        record(arena._compose_owner, result, valid)

    return PayloadAuditContribution(tuple(approved), tuple(invalid))


__all__ = [
    "audit_collatz_field_action",
    "audit_collatz_local_codec",
    "audit_collatz_range",
    "audit_collatz_runtime_programs",
    "register_collatz_field_action_contract",
    "register_collatz_local_codec_contract",
    "register_collatz_range_contract",
    "register_collatz_runtime_program_contract",
]

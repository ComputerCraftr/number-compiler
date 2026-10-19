"""Read-only audit for source-bound primitive cylinder innovation clauses."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.semantic_identity import (
    SemanticIdentityDomain,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditEntry,
)
from number_compiler.sequences.reverse_add.semantic_tags import (
    REVERSE_ADD_PRIMITIVE_CYLINDER_CLAUSE_TAG,
    REVERSE_ADD_SOURCE_CARRY_TAG,
)

if TYPE_CHECKING:
    from number_compiler.arithmetic.fields.symbolic_innovation import (
        SymbolicInnovationArena,
    )
    from number_compiler.sequences.reverse_add.cylinder_innovation import (
        PrimitiveSuccessorClause,
    )


def register_primitive_successor_clause_contract(
    root: PrimitiveSuccessorClause,
) -> None:
    """Register the clause's exact source-binding and seal stores."""
    from number_compiler.resources.payload_contracts import PayloadAuditStoreBinding

    state = root.audit_snapshot()
    state.arena.ledger.register_payload_audit_contract(
        root,
        "reverse_add",
        (
            PayloadAuditStoreBinding(
                state.binding_owner, "_binding_store", "spatial_binding"
            ),
            PayloadAuditStoreBinding(
                state.seal_owner, "_seals", "reverse_action_interner"
            ),
        ),
        audit_primitive_successor_clause_owner,
    )


def audit_primitive_successor_clause_owner(
    ledger_value: object, root_value: object
) -> PayloadAuditContribution:
    """Validate one clause and return only members of its bound stores."""
    from number_compiler.arithmetic.fields.symbolic_innovation import (
        SymbolicInnovationArena,
    )
    from number_compiler.resources.stores import LedgerDict, LedgerList
    from number_compiler.sequences.reverse_add.cylinder_innovation import (
        PrimitiveSuccessorClause,
    )

    if type(ledger_value) is not ResourceLedger:
        raise TypeError("clause auditor received a foreign ledger")
    if type(root_value) is not PrimitiveSuccessorClause:
        raise TypeError("clause auditor received a foreign root")
    ledger = ledger_value
    root = root_value
    state = root.audit_snapshot()
    binding = state.carry_atom.audit_snapshot()
    arena_state = state.arena.audit_snapshot()
    binding_owner, seal_owner, workspace_owner = (
        state.binding_owner,
        state.seal_owner,
        state.workspace_owner,
    )
    if any(
        type(owner) is not int for owner in (binding_owner, seal_owner, workspace_owner)
    ):
        raise ValueError("clause owner identifiers are malformed")
    binding_account = ledger.inventory_owner(binding_owner)
    seal_account = ledger.inventory_owner(seal_owner)
    workspace_account = ledger.inventory_owner(workspace_owner)
    binding_container = ledger.registered_container(binding_owner)
    seal_container = ledger.registered_container(seal_owner)
    workspace_container = ledger.registered_container(workspace_owner)
    binding_store = state.binding_store
    seal_store = state.seals
    valid = (
        type(state.arena) is SymbolicInnovationArena
        and arena_state.ledger is ledger
        and binding.ledger is ledger
        and binding.arena is state.arena
        and binding.ports.resource_ledger is ledger
        and type(binding_store) is LedgerList
        and binding_store.ledger is ledger
        and binding_store.owner == binding_owner
        and binding_store.nodes_per_entry == 1
        and binding_store.append_only
        and ledger.is_factory_container(binding_store)
        and binding_container is binding_store
        and binding_account.role == "spatial_binding"
        and not binding_account.disposed
        and type(seal_store) is LedgerDict
        and seal_store.ledger is ledger
        and seal_store.owner == seal_owner
        and seal_store.nodes_per_entry == 0
        and ledger.is_factory_container(seal_store)
        and seal_container is seal_store
        and seal_account.role == "reverse_action_interner"
        and not seal_account.disposed
        and workspace_container is None
        and workspace_account.role == "reverse_primitive_cylinder_workspace"
        and workspace_account.entries == workspace_account.nodes == 0
        and not workspace_account.disposed
        and not state.closed
        and not binding.closed
        and not arena_state.closed
        and binding_account.entries == binding_account.nodes == 1
        and seal_account.entries == 1
        and seal_account.nodes == 0
        and len(state.binding_rows) == 1
        and len(state.seal_rows) == 1
    )
    if not valid:
        raise ValueError("clause store or lifecycle authority is invalid")
    if not _valid_live_clause(root, ledger):
        raise ValueError("clause arithmetic authority is invalid")
    if len(state.binding_rows) != 1 or len(state.seal_rows) != 1:
        raise ValueError("clause stores do not contain exactly one binding")
    record = state.binding_rows[0]
    seal_record, seal_value = state.seal_rows[0]
    if (
        record is not state.record
        or seal_record is not record
        or type(seal_value) is not int
        or seal_value != 0
        or not _valid_semantic(record.authority)
    ):
        raise ValueError("clause record seal or semantic authority is invalid")
    return PayloadAuditContribution(
        approved=(
            PayloadAuditEntry(binding_owner, record),
            PayloadAuditEntry(seal_owner, record),
            PayloadAuditEntry(seal_owner, 0),
        )
    )


def _valid_live_clause(root: PrimitiveSuccessorClause, ledger: ResourceLedger) -> bool:
    from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
    from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
    from number_compiler.arithmetic.fields.radial_innovation import (
        InnovationAdd,
        InnovationAtom,
        InnovationID,
        RadialMultiplier,
        SymbolicRadialInnovation,
    )
    from number_compiler.arithmetic.fields.symbolic_innovation import (
        SymbolicInnovationArena,
    )
    from number_compiler.sequences.reverse_add.cylinder_innovation import (
        PrimitiveCarryAtomAuditSnapshot,
        PrimitiveClauseRecord,
        PrimitiveSuccessorClause,
    )
    from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts

    if type(root) is not PrimitiveSuccessorClause:
        return False
    state = root.audit_snapshot()
    binding = state.carry_atom.audit_snapshot()
    ports = binding.ports.audit_snapshot()
    arena = state.arena
    arena_state = arena.audit_snapshot()
    if (
        type(binding) is not PrimitiveCarryAtomAuditSnapshot
        or type(binding.arena) is not SymbolicInnovationArena
        or binding.arena is not arena
        or binding.ledger is not ledger
        or type(binding.ports) is not SourceCarryPorts
        or ports.ledger is not ledger
        or type(binding.source) is not ExactSource
        or binding.source is not ports.source
        or ports.closed
        or binding.source.digits is not ports.authority[1]
        or ports.authority[0] is not binding.source
        or ports.authority[2] != binding.source.base
        or ports.authority[3] != binding.source.orbit
        or ports.authority[4] != binding.source.blank
        or ports.authority[5] != binding.source.extent
        or ports.authority[6] != binding.source.alphabet_size
        or ports.authority[7] is not ledger
        or ports.authority[8] is not ports.cache_identity
        or ports.authority[9] != binding.source_owner
        or ports.cache.owner != binding.source_owner
        or ports.cache.ledger is not ledger
        or ports.width != len(binding.source.digits)
        or ports.workspace_owner != ports.workspace_authority
        or type(binding.source_owner) is not int
        or type(binding.extent) is not int
        or type(binding.growth) is not int
        or type(binding.base) is not int
        or binding.extent != ports.width
        or binding.growth != state.growth
        or binding.base != binding.source.base
        or type(state.extent) is not int
        or state.extent < 1
        or state.extent != binding.extent
        or type(state.base) is not int
        or state.base != binding.base
        or type(state.growth) is not int
        or state.growth not in (0, 1)
        or type(state.output_extent) is not int
        or state.output_extent != state.extent + state.growth
        or type(state.action) is not SymbolicRadialInnovation
        or type(state.correction) is not InnovationID
        or type(state.beta) is not InnovationID
        or type(state.record) is not PrimitiveClauseRecord
    ):
        return False
    source = binding.source
    record = state.record
    alphabet = source.base if source.alphabet_size is None else source.alphabet_size
    if (
        type(source.digits) is not tuple
        or not source.digits
        or type(source.base) is not int
        or source.base < 2
        or type(source.orbit) is not str
        or type(source.blank) is not int
        or source.blank < 0
        or type(alphabet) is not int
        or alphabet < 1
        or source.extent is not None
        and (type(source.extent) is not int or source.extent < len(source.digits))
    ):
        return False
    if (
        len(state.binding_rows) != 1
        or state.binding_rows[0] is not record
        or any(
            type(value) is not int
            for value in (
                record.source_owner,
                record.arena_node_owner,
                record.arena_key_owner,
                record.extent,
                record.growth,
                record.output_extent,
                record.base,
                record.binding_owner,
                record.seal_owner,
                record.workspace_owner,
            )
        )
        or record.source_owner != binding.source_owner
        or record.arena_node_owner != arena_state.node_owner
        or record.arena_key_owner != arena_state.key_owner
        or not _same_handle(record.q, binding.atom)
        or state.extent != record.extent
        or state.growth != record.growth
        or state.output_extent != record.output_extent
        or state.base != record.base
        or not _same_handle(state.correction, record.correction)
        or not _same_handle(state.beta, record.beta)
        or state.action != record.action
        or state.binding_owner != record.binding_owner
        or state.seal_owner != record.seal_owner
        or state.workspace_owner != record.workspace_owner
        or type(record.authority) is not SemanticIdentity
    ):
        return False
    carry = 0
    for index, digit in enumerate(source.digits):
        if type(digit) is not int or not 0 <= digit < alphabet:
            return False
        pair = digit + source.digits[-1 - index]
        carry = int(pair + carry >= source.base)
    if state.growth != carry:
        return False
    expected_multiplier = RadialMultiplier(1 - carry, carry)
    if (
        type(state.action.multiplier.no_growth) is not int
        or type(state.action.multiplier.growth) is not int
        or state.action.multiplier != expected_multiplier
        or not _same_handle(state.action.innovation, state.beta)
        or not _valid_handle(binding.atom, arena)
    ):
        return False
    atom = _node(arena, binding.atom)
    expected_atom_semantic = SemanticIdentity(
        SemanticIdentityDomain.REVERSE_ADD_SOURCE_CARRY,
        (
            REVERSE_ADD_SOURCE_CARRY_TAG,
            binding.source_owner,
            state.base,
            state.extent,
            state.growth,
        ),
    )
    if (
        type(atom) is not InnovationAtom
        or type(binding.semantic) is not SemanticIdentity
        or binding.semantic != expected_atom_semantic
        or atom.semantic != binding.semantic
        or not _valid_semantic(binding.semantic)
    ):
        return False
    correction = _node(arena, state.correction)
    if type(correction) is not InnovationAdd:
        return False
    correction_children = (correction.left, correction.right)
    shifted = next(
        (
            child
            for child in correction_children
            if _is_chart(arena, child, 1, -1, binding.atom)
        ),
        None,
    )
    scaled = next(
        (
            child
            for child in correction_children
            if _is_scale(arena, child, -state.base, binding.atom)
        ),
        None,
    )
    if shifted is None or scaled is None or _same_handle(shifted, scaled):
        return False
    beta = _node(arena, state.beta)
    if type(beta) is not InnovationAdd:
        return False
    beta_children = (beta.left, beta.right)
    reflected = next(
        (
            child
            for child in beta_children
            if _is_chart(
                arena,
                child,
                -1,
                state.extent + state.growth - 1,
                state.correction,
            )
        ),
        None,
    )
    if reflected is None or not any(
        _same_handle(child, state.correction) for child in beta_children
    ):
        return False
    expected_behavior = (
        REVERSE_ADD_PRIMITIVE_CYLINDER_CLAUSE_TAG,
        binding.source_owner,
        arena_state.node_owner,
        arena_state.key_owner,
        binding.atom.local_id,
        binding.atom.seal,
        state.extent,
        state.growth,
        state.output_extent,
        state.base,
        state.correction.local_id,
        state.correction.seal,
        state.beta.local_id,
        state.beta.seal,
        state.action.innovation.local_id,
        state.action.innovation.seal,
        state.action.multiplier.no_growth,
        state.action.multiplier.growth,
        state.binding_owner,
        state.seal_owner,
        state.workspace_owner,
    )
    return record.authority.behavior == expected_behavior


def _valid_handle(reference: object, arena: SymbolicInnovationArena) -> bool:
    from number_compiler.arithmetic.fields.radial_innovation import InnovationID
    from number_compiler.arithmetic.fields.symbolic_innovation import (
        SymbolicInnovationArena,
    )

    snapshot = arena.audit_snapshot()
    return (
        type(arena) is SymbolicInnovationArena
        and type(reference) is InnovationID
        and reference.owner is snapshot.owner
        and reference.kind == "symbolic-innovation"
        and type(reference.local_id) is int
        and 0 <= reference.local_id < len(snapshot.nodes)
        and reference.seal == f"{id(snapshot.owner):x}:{reference.local_id}"
    )


def _node(arena: SymbolicInnovationArena, reference: object) -> object:
    from number_compiler.arithmetic.fields.radial_innovation import InnovationID

    if not _valid_handle(reference, arena):
        raise ValueError("invalid cylinder innovation handle")
    assert type(reference) is InnovationID
    return arena.audit_snapshot().nodes[reference.local_id]


def _same_handle(left: object, right: object) -> bool:
    from number_compiler.arithmetic.fields.radial_innovation import InnovationID

    return (
        type(left) is InnovationID
        and type(right) is InnovationID
        and left.owner is right.owner
        and left.kind == right.kind
        and left.local_id == right.local_id
        and left.seal == right.seal
    )


def _is_chart(
    arena: SymbolicInnovationArena,
    reference: object,
    slope: int,
    offset: int,
    child: object,
) -> bool:
    from number_compiler.arithmetic.fields.radial_innovation import InnovationCharted

    try:
        node = _node(arena, reference)
    except (AttributeError, IndexError, TypeError, ValueError):
        return False
    return (
        type(node) is InnovationCharted
        and type(node.chart.slope) is int
        and type(node.chart.offset) is int
        and type(node.chart.extent_scale) is int
        and type(node.chart.growth_scale) is int
        and node.chart.slope == slope
        and node.chart.offset == offset
        and node.chart.extent_scale == node.chart.growth_scale == 0
        and _same_handle(node.child, child)
    )


def _is_scale(
    arena: SymbolicInnovationArena,
    reference: object,
    coefficient: int,
    child: object,
) -> bool:
    from number_compiler.arithmetic.fields.radial_innovation import InnovationScale

    try:
        node = _node(arena, reference)
    except (AttributeError, IndexError, TypeError, ValueError):
        return False
    return (
        type(node) is InnovationScale
        and type(node.coefficient) is int
        and node.coefficient == coefficient
        and _same_handle(node.child, child)
    )


def _valid_semantic(value: object) -> bool:
    from number_compiler.arithmetic.contracts.semantic_identity import (
        SemanticIdentity,
        SemanticIdentityValidator,
    )

    if type(value) is not SemanticIdentity:
        return False
    validator = SemanticIdentityValidator()
    try:
        validator.validate(value)
        validator.finish()
    except (AttributeError, TypeError, ValueError):
        return False
    return True


__all__ = [
    "audit_primitive_successor_clause_owner",
    "register_primitive_successor_clause_contract",
]

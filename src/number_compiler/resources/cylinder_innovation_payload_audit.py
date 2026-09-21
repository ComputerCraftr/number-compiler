"""Read-only audit for source-bound primitive cylinder innovation clauses."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.physical_support_payload_audit import (
    PhysicalSupportPayloadAudit,
)

if TYPE_CHECKING:
    from number_compiler.arithmetic.fields.symbolic_innovation import (
        SymbolicInnovationArena,
    )
    from number_compiler.sequences.reverse_add.cylinder_innovation import (
        PrimitiveSuccessorClause,
    )


def audit_cylinder_innovation_payloads(
    ledger: ResourceLedger,
) -> PhysicalSupportPayloadAudit:
    """Validate retained clause authority and source facts without runtime calls.

    The independent factual growth check is a bounded linear scan of the
    original source tuple.  It runs only during payload audit, never during
    primitive construction or coefficient consumption.
    """
    if not any(
        type(root).__module__
        == "number_compiler.sequences.reverse_add.cylinder_innovation"
        for root in ledger.iter_execution_roots()
    ):
        return PhysicalSupportPayloadAudit(frozenset(), frozenset())

    from number_compiler.arithmetic.fields.symbolic_innovation import (
        SymbolicInnovationArena,
    )
    from number_compiler.resources.stores import LedgerDict, LedgerList
    from number_compiler.sequences.reverse_add.cylinder_innovation import (
        PrimitiveCarryAtomBinding,
        PrimitiveSuccessorClause,
    )

    containers = dict(ledger.iter_containers())
    inventory = {row.owner: row for row in ledger.inventory()}
    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    for root in ledger.iter_execution_roots():
        if type(root) is not PrimitiveSuccessorClause:
            continue
        try:
            _ = (
                root.arena,
                root.carry_atom,
                root.extent,
                root.growth,
                root.output_extent,
                root.base,
                root.action,
                root._correction,
                root._beta,
                root._record,
                root._binding_store,
                root._seals,
                root._closed,
            )
            binding_owner = root._binding_owner
            seal_owner = root._seal_owner
            workspace_owner = root._workspace_owner
        except AttributeError:
            invalid.add((-1, id(root)))
            continue
        if any(
            type(owner) is not int
            for owner in (binding_owner, seal_owner, workspace_owner)
        ):
            invalid.add((-1, id(root)))
            continue
        binding_row = inventory.get(binding_owner)
        seal_row = inventory.get(seal_owner)
        workspace_row = inventory.get(workspace_owner)
        valid = (
            type(root.arena) is SymbolicInnovationArena
            and root.arena.ledger is ledger
            and type(root.carry_atom) is PrimitiveCarryAtomBinding
            and type(getattr(root.carry_atom, "_closed", None)) is bool
            and type(root._closed) is bool
            and type(root._binding_store) is LedgerList
            and root._binding_store.ledger is ledger
            and root._binding_store.owner == binding_owner
            and root._binding_store.nodes_per_entry == 1
            and root._binding_store.append_only
            and ledger.is_factory_container(root._binding_store)
            and containers.get(binding_owner) is root._binding_store
            and type(root._seals) is LedgerDict
            and root._seals.ledger is ledger
            and root._seals.owner == seal_owner
            and root._seals.nodes_per_entry == 0
            and ledger.is_factory_container(root._seals)
            and containers.get(seal_owner) is root._seals
            and binding_row is not None
            and seal_row is not None
            and workspace_row is not None
            and binding_row.role == "spatial_binding"
            and seal_row.role == "reverse_action_interner"
            and workspace_row.role == "reverse_primitive_cylinder_workspace"
            and binding_row.accounting_delta == 0
            and seal_row.accounting_delta == 0
            and workspace_row.entries == workspace_row.nodes == 0
            and containers.get(workspace_owner) is None
        )
        root_approved = {id(root._binding_store), id(root._seals)}
        if not valid:
            invalid.update(
                (
                    (binding_owner, id(root)),
                    (seal_owner, id(root)),
                    (workspace_owner, id(root)),
                )
            )
            continue
        if root._closed:
            valid &= (
                root.carry_atom._closed
                and binding_row is not None
                and seal_row is not None
                and workspace_row is not None
                and binding_row.disposed
                and seal_row.disposed
                and workspace_row.disposed
                and binding_row.entries == binding_row.nodes == 0
                and seal_row.entries == seal_row.nodes == 0
                and len(root._binding_store) == 0
                and len(root._seals) == 0
            )
        else:
            valid &= (
                not root.carry_atom._closed
                and not root.arena._closed
                and binding_row is not None
                and seal_row is not None
                and workspace_row is not None
                and not binding_row.disposed
                and not seal_row.disposed
                and not workspace_row.disposed
                and binding_row.entries == binding_row.nodes == 1
                and seal_row.entries == 1
                and seal_row.nodes == 0
                and len(root._binding_store) == 1
                and len(root._seals) == 1
            )
            try:
                valid &= _valid_live_clause(root, ledger)
                stored = root._binding_store[0]
                valid &= (
                    stored is root._record
                    and root._seals.get(stored) == 0
                    and _valid_semantic(root._record.authority)
                )
                if valid:
                    root_approved.update(
                        {
                            id(root._record),
                            id(root._record.authority),
                            id(root._record.authority.behavior),
                            id(stored),
                            id(root.carry_atom._semantic),
                            id(root.carry_atom._semantic.behavior),
                        }
                    )
            except (AttributeError, IndexError, KeyError, TypeError, ValueError):
                valid = False
        if valid:
            approved.update(root_approved)
        else:
            invalid.update(
                (
                    (binding_owner, id(root)),
                    (seal_owner, id(root)),
                    (workspace_owner, id(root)),
                )
            )
    return PhysicalSupportPayloadAudit(frozenset(approved), frozenset(invalid))


def _valid_live_clause(root: PrimitiveSuccessorClause, ledger: ResourceLedger) -> bool:
    from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
    from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
    from number_compiler.arithmetic.fields.symbolic_innovation import (
        InnovationID,
        RadialMultiplier,
        SymbolicInnovationArena,
        SymbolicRadialInnovation,
        _Add,
        _Atom,
    )
    from number_compiler.sequences.reverse_add.cylinder_innovation import (
        PrimitiveCarryAtomBinding,
        PrimitiveSuccessorClause,
        _PrimitiveClauseRecord,
    )
    from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts

    if type(root) is not PrimitiveSuccessorClause:
        return False
    binding = root.carry_atom
    if (
        type(binding) is not PrimitiveCarryAtomBinding
        or type(binding._arena) is not SymbolicInnovationArena
        or binding._arena is not root.arena
        or binding._ledger is not ledger
        or type(binding._ports) is not SourceCarryPorts
        or binding._ports._ledger is not ledger
        or type(binding._source) is not ExactSource
        or binding._source is not binding._ports._source
        or binding._ports._closed
        or binding._source.digits is not binding._ports._authority[1]
        or binding._ports._authority[0] is not binding._source
        or binding._ports._authority[2] != binding._source.base
        or binding._ports._authority[3] != binding._source.orbit
        or binding._ports._authority[4] != binding._source.blank
        or binding._ports._authority[5] != binding._source.extent
        or binding._ports._authority[6] != binding._source.alphabet_size
        or binding._ports._authority[7] is not ledger
        or binding._ports._authority[8] is not binding._ports._cache
        or binding._ports._authority[9] != binding._source_owner
        or binding._ports._cache.owner != binding._source_owner
        or binding._ports._cache.ledger is not ledger
        or binding._ports._width != len(binding._source.digits)
        or binding._ports._workspace_owner != binding._ports._workspace_authority
        or type(binding._source_owner) is not int
        or type(binding._extent) is not int
        or type(binding._growth) is not int
        or type(binding._base) is not int
        or binding._extent != binding._ports._width
        or binding._growth != root.growth
        or binding._base != binding._source.base
        or type(root.extent) is not int
        or root.extent < 1
        or root.extent != binding._extent
        or type(root.base) is not int
        or root.base != binding._base
        or type(root.growth) is not int
        or root.growth not in (0, 1)
        or type(root.output_extent) is not int
        or root.output_extent != root.extent + root.growth
        or type(root.action) is not SymbolicRadialInnovation
        or type(root._correction) is not InnovationID
        or type(root._beta) is not InnovationID
        or type(root._record) is not _PrimitiveClauseRecord
    ):
        return False
    source = binding._source
    record = root._record
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
        root._binding_store[0] is not record
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
        or record.source_owner != binding._source_owner
        or record.arena_node_owner != root.arena._node_owner
        or record.arena_key_owner != root.arena._key_owner
        or not _same_handle(record.q, binding._atom)
        or root.extent != record.extent
        or root.growth != record.growth
        or root.output_extent != record.output_extent
        or root.base != record.base
        or not _same_handle(root._correction, record.correction)
        or not _same_handle(root._beta, record.beta)
        or root.action != record.action
        or root._binding_owner != record.binding_owner
        or root._seal_owner != record.seal_owner
        or root._workspace_owner != record.workspace_owner
        or type(record.authority) is not SemanticIdentity
    ):
        return False
    carry = 0
    for index, digit in enumerate(source.digits):
        if type(digit) is not int or not 0 <= digit < alphabet:
            return False
        pair = digit + source.digits[-1 - index]
        carry = int(pair + carry >= source.base)
    if root.growth != carry:
        return False
    expected_multiplier = RadialMultiplier(1 - carry, carry)
    if (
        type(root.action.multiplier.no_growth) is not int
        or type(root.action.multiplier.growth) is not int
        or root.action.multiplier != expected_multiplier
        or not _same_handle(root.action.innovation, root._beta)
        or not _valid_handle(binding._atom, root.arena)
    ):
        return False
    atom = _node(root.arena, binding._atom)
    expected_atom_semantic = SemanticIdentity(
        "reverse-add-source-carry-v1",
        (
            "reverse-add-source-carry-v1",
            binding._source_owner,
            root.base,
            root.extent,
            root.growth,
        ),
    )
    if (
        type(atom) is not _Atom
        or type(binding._semantic) is not SemanticIdentity
        or binding._semantic != expected_atom_semantic
        or atom.semantic != binding._semantic
        or not _valid_semantic(binding._semantic)
    ):
        return False
    correction = _node(root.arena, root._correction)
    if type(correction) is not _Add:
        return False
    correction_children = (correction.left, correction.right)
    shifted = next(
        (
            child
            for child in correction_children
            if _is_chart(root.arena, child, 1, -1, binding._atom)
        ),
        None,
    )
    scaled = next(
        (
            child
            for child in correction_children
            if _is_scale(root.arena, child, -root.base, binding._atom)
        ),
        None,
    )
    if shifted is None or scaled is None or _same_handle(shifted, scaled):
        return False
    beta = _node(root.arena, root._beta)
    if type(beta) is not _Add:
        return False
    beta_children = (beta.left, beta.right)
    reflected = next(
        (
            child
            for child in beta_children
            if _is_chart(
                root.arena,
                child,
                -1,
                root.extent + root.growth - 1,
                root._correction,
            )
        ),
        None,
    )
    if reflected is None or not any(
        _same_handle(child, root._correction) for child in beta_children
    ):
        return False
    expected_behavior = (
        "reverse-add-primitive-cylinder-clause-v1",
        binding._source_owner,
        root.arena._node_owner,
        root.arena._key_owner,
        binding._atom.local_id,
        binding._atom.seal,
        root.extent,
        root.growth,
        root.output_extent,
        root.base,
        root._correction.local_id,
        root._correction.seal,
        root._beta.local_id,
        root._beta.seal,
        root.action.innovation.local_id,
        root.action.innovation.seal,
        root.action.multiplier.no_growth,
        root.action.multiplier.growth,
        root._binding_owner,
        root._seal_owner,
        root._workspace_owner,
    )
    return record.authority.behavior == expected_behavior


def _valid_handle(reference: object, arena: SymbolicInnovationArena) -> bool:
    from number_compiler.arithmetic.fields.symbolic_innovation import (
        InnovationID,
        SymbolicInnovationArena,
    )

    return (
        type(arena) is SymbolicInnovationArena
        and type(reference) is InnovationID
        and reference.owner is arena.owner
        and reference.kind == arena._KIND
        and type(reference.local_id) is int
        and 0 <= reference.local_id < len(arena._nodes)
        and reference.seal == f"{id(arena.owner):x}:{reference.local_id}"
    )


def _node(arena: SymbolicInnovationArena, reference: object) -> object:
    from number_compiler.arithmetic.fields.symbolic_innovation import InnovationID

    if not _valid_handle(reference, arena):
        raise ValueError("invalid cylinder innovation handle")
    assert type(reference) is InnovationID
    return arena._nodes[reference.local_id]


def _same_handle(left: object, right: object) -> bool:
    from number_compiler.arithmetic.fields.symbolic_innovation import InnovationID

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
    from number_compiler.arithmetic.fields.symbolic_innovation import _Charted

    try:
        node = _node(arena, reference)
    except (AttributeError, IndexError, TypeError, ValueError):
        return False
    return (
        type(node) is _Charted
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
    from number_compiler.arithmetic.fields.symbolic_innovation import _Scale

    try:
        node = _node(arena, reference)
    except (AttributeError, IndexError, TypeError, ValueError):
        return False
    return (
        type(node) is _Scale
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


__all__ = ["audit_cylinder_innovation_payloads"]

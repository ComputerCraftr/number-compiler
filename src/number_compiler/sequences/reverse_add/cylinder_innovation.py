"""One exact source-bound reverse/add primitive cylinder arithmetic clause.

For the original pair polynomial ``P`` and its carry boundaries ``C``, put
``Q_i = C_(i+1)`` on ``0 <= i < m`` and zero elsewhere.  If ``g=C_m`` and
``d=m+g-1``, the first output polynomial is

``D = P + (z-b)Q``

and the next pair polynomial is

``P' = D + R_d D = M'P + beta``.

Here ``M'=2`` when ``g=0``, ``M'=1+z`` when ``g=1``, and
``beta=(z-b)Q+R_d((z-b)Q)``.  This module binds that whole-function identity
to one authenticated :class:`SourceCarryPorts`.  It is a primitive arithmetic
successor clause, not a temporal closure theorem or a source-image publisher.
"""

from __future__ import annotations

from copy import deepcopy
from dataclasses import dataclass

from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.fields.centered_carry import (
    carry_coboundary,
    reflected_innovation,
)
from number_compiler.arithmetic.fields.symbolic_innovation import (
    InnovationID,
    RadialMultiplier,
    SymbolicInnovationArena,
    SymbolicRadialInnovation,
    _Add,
    _Atom,
    _Charted,
    _node_units,
    _Radial,
    _Scale,
    _Zero,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict, LedgerList
from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts


def _copy_reference(reference: InnovationID) -> InnovationID:
    return InnovationID(
        reference.owner, reference.kind, reference.local_id, reference.seal
    )


def _carry_semantic(
    source_owner: int, base: int, extent: int, growth: int
) -> SemanticIdentity:
    return SemanticIdentity(
        "reverse-add-source-carry-v1",
        ("reverse-add-source-carry-v1", source_owner, base, extent, growth),
    )


def _planned_primitive_nodes(
    arena: SymbolicInnovationArena,
    semantic: SemanticIdentity,
    *,
    base: int,
    reflection: int,
) -> tuple[int, int]:
    """Count interner misses and retained units for the fixed construction plan."""
    missing = 0
    units = 0

    def reference(node: _Atom | _Charted | _Scale | _Add) -> InnovationID:
        nonlocal missing, units
        found = arena._keys.get(node)
        if found is not None:
            arena.resolve(found)
            return _copy_reference(found)
        result = arena._handle(arena.node_count + missing)
        missing += 1
        units += _node_units(node)
        return result

    q = reference(_Atom(deepcopy(semantic)))
    shifted = reference(_Charted(CylinderChart(1, -1), _copy_reference(q)))
    scaled = reference(_Scale(-base, _copy_reference(q)))
    left, right = (
        (scaled, shifted) if scaled.local_id < shifted.local_id else (shifted, scaled)
    )
    correction = reference(_Add(_copy_reference(left), _copy_reference(right)))
    reflected = reference(
        _Charted(CylinderChart(-1, reflection), _copy_reference(correction))
    )
    left, right = (
        (correction, reflected)
        if correction.local_id < reflected.local_id
        else (reflected, correction)
    )
    reference(_Add(_copy_reference(left), _copy_reference(right)))
    return missing, units


@dataclass(frozen=True, slots=True)
class PrimitiveCarryAtomBinding:
    """A scoped formal ``Q`` atom backed only by one live source-port owner."""

    _arena: SymbolicInnovationArena
    _ports: SourceCarryPorts
    _source: ExactSource
    _ledger: ResourceLedger
    _source_owner: int
    _extent: int
    _growth: int
    _base: int
    _semantic: SemanticIdentity
    _atom: InnovationID
    _closed: bool = False

    @classmethod
    def create(
        cls,
        arena: SymbolicInnovationArena,
        ports: SourceCarryPorts,
        *,
        source: ExactSource,
        extent: int,
        growth: int,
        base: int,
    ) -> PrimitiveCarryAtomBinding:
        """Create one fixed-size binding after source admission has succeeded."""
        ports.check_source(source)
        if arena.ledger is not ports.ledger:
            raise ValueError("carry atom and symbolic arena require the same ledger")
        if (
            type(extent) is not int
            or extent != ports.width
            or type(growth) is not int
            or growth not in (0, 1)
            or type(base) is not int
            or base != source.base
        ):
            raise ValueError("carry atom geometry differs from its source ports")
        # The cache owner is a monotonic, nonrecycled number in this ledger and
        # is already part of SourceCarryPorts' authenticated authority tuple.
        source_owner = ports._cache.owner
        semantic = _carry_semantic(source_owner, base, extent, growth)
        atom = arena.atom(semantic)
        return cls(
            arena,
            ports,
            source,
            ports.ledger,
            source_owner,
            extent,
            growth,
            base,
            semantic,
            _copy_reference(atom),
        )

    @property
    def atom(self) -> InnovationID:
        self.validate()
        return _copy_reference(self._atom)

    @property
    def semantic(self) -> SemanticIdentity:
        """Return the immutable arithmetic key, without granting source authority."""
        self.validate()
        return self._semantic

    def validate(self) -> None:
        if self._closed:
            raise ValueError("disposed primitive carry atom binding")
        if (
            type(self._arena) is not SymbolicInnovationArena
            or type(self._ports) is not SourceCarryPorts
            or type(self._source) is not ExactSource
            or type(self._ledger) is not ResourceLedger
            or self._arena.ledger is not self._ledger
            or self._ports._ledger is not self._ledger
        ):
            raise ValueError("primitive carry atom has a foreign owner")
        self._ports.check_source(self._source)
        if (
            self._ports._cache.owner != self._source_owner
            or self._ports.width != self._extent
            or self._source.base != self._base
        ):
            raise ValueError("primitive carry atom binding was altered")
        expected_semantic = _carry_semantic(
            self._source_owner, self._base, self._extent, self._growth
        )
        self._semantic.validate()
        if self._semantic != expected_semantic:
            raise ValueError("primitive carry atom semantic binding was altered")
        node = self._arena.resolve(self._atom)
        if type(node) is not _Atom or node.semantic != self._semantic:
            raise ValueError("primitive carry atom no longer names its bound variable")

    def coefficient(self, index: int) -> int:
        """Return ``Q_index`` with exact signed-coordinate zero extension."""
        if type(index) is not int:
            raise TypeError("carry atom coordinates must be exact integers")
        self.validate()
        if not 0 <= index < self._extent:
            return 0
        return self._ports.carry(index + 1)

    def source_pair_coefficient(self, index: int) -> int:
        """Return ``P_index`` with the same signed zero-extension convention."""
        if type(index) is not int:
            raise TypeError("source pair coordinates must be exact integers")
        self.validate()
        if not 0 <= index < self._extent:
            return 0
        return self._ports.first_pair(index)

    def _invalidate(self) -> None:
        object.__setattr__(self, "_closed", True)


def _clause_authority(
    arena: SymbolicInnovationArena,
    binding: PrimitiveCarryAtomBinding,
    *,
    extent: int,
    growth: int,
    output_extent: int,
    base: int,
    correction: InnovationID,
    beta: InnovationID,
    action: SymbolicRadialInnovation,
    binding_owner: int,
    seal_owner: int,
    workspace_owner: int,
) -> SemanticIdentity:
    return SemanticIdentity(
        "reverse-add-primitive-cylinder-clause-v1",
        (
            "reverse-add-primitive-cylinder-clause-v1",
            binding._source_owner,
            arena._node_owner,
            arena._key_owner,
            binding._atom.local_id,
            binding._atom.seal,
            extent,
            growth,
            output_extent,
            base,
            correction.local_id,
            correction.seal,
            beta.local_id,
            beta.seal,
            action.innovation.local_id,
            action.innovation.seal,
            action.multiplier.no_growth,
            action.multiplier.growth,
            binding_owner,
            seal_owner,
            workspace_owner,
        ),
    )


@dataclass(frozen=True, slots=True)
class _PrimitiveClauseRecord:
    source_owner: int
    arena_node_owner: int
    arena_key_owner: int
    q: InnovationID
    extent: int
    growth: int
    output_extent: int
    base: int
    correction: InnovationID
    beta: InnovationID
    action: SymbolicRadialInnovation
    binding_owner: int
    seal_owner: int
    workspace_owner: int
    authority: SemanticIdentity


@dataclass(frozen=True, slots=True, weakref_slot=True)
class PrimitiveSuccessorClause:
    """Exact primitive affine identity bound to one original source occurrence."""

    arena: SymbolicInnovationArena
    carry_atom: PrimitiveCarryAtomBinding
    extent: int
    growth: int
    output_extent: int
    base: int
    action: SymbolicRadialInnovation
    _correction: InnovationID
    _beta: InnovationID
    _record: _PrimitiveClauseRecord
    _binding_owner: int
    _binding_store: LedgerList[_PrimitiveClauseRecord]
    _seal_owner: int
    _seals: LedgerDict[_PrimitiveClauseRecord, int]
    _workspace_owner: int
    _closed: bool = False

    def _record_authority(self) -> SemanticIdentity:
        record = self._record
        return _clause_authority(
            self.arena,
            self.carry_atom,
            extent=record.extent,
            growth=record.growth,
            output_extent=record.output_extent,
            base=record.base,
            correction=record.correction,
            beta=record.beta,
            action=record.action,
            binding_owner=record.binding_owner,
            seal_owner=record.seal_owner,
            workspace_owner=record.workspace_owner,
        )

    def validate(self) -> None:
        if self._closed:
            raise ValueError("disposed primitive successor clause")
        if (
            type(self.arena) is not SymbolicInnovationArena
            or type(self.carry_atom) is not PrimitiveCarryAtomBinding
            or type(self.extent) is not int
            or type(self.growth) is not int
            or type(self.output_extent) is not int
            or type(self.base) is not int
            or type(self.action) is not SymbolicRadialInnovation
            or type(self._correction) is not InnovationID
            or type(self._beta) is not InnovationID
            or type(self._record) is not _PrimitiveClauseRecord
            or type(self._binding_owner) is not int
            or type(self._binding_store) is not LedgerList
            or type(self._seal_owner) is not int
            or type(self._seals) is not LedgerDict
            or type(self._workspace_owner) is not int
        ):
            raise ValueError("malformed primitive successor clause")
        # Authenticate the complete published clause before touching a source
        # coefficient or resolving any supplied expression handle.
        record = self._record
        expected_authority = self._record_authority()
        record.authority.validate()
        binding_account = self.arena.ledger._account(self._binding_owner)
        seal_account = self.arena.ledger._account(self._seal_owner)
        workspace_account = self.arena.ledger._account(self._workspace_owner)
        if (
            record.authority != expected_authority
            or record.source_owner != self.carry_atom._source_owner
            or record.arena_node_owner != self.arena._node_owner
            or record.arena_key_owner != self.arena._key_owner
            or record.q != self.carry_atom._atom
            or self.extent != record.extent
            or self.growth != record.growth
            or record.growth != self.carry_atom._growth
            or self.output_extent != record.output_extent
            or self.base != record.base
            or self._correction != record.correction
            or self._beta != record.beta
            or self.action != record.action
            or self._binding_owner != record.binding_owner
            or self._seal_owner != record.seal_owner
            or self._workspace_owner != record.workspace_owner
            or binding_account.role != "spatial_binding"
            or binding_account.disposed
            or binding_account.entries != 1
            or binding_account.nodes != 1
            or seal_account.role != "reverse_action_interner"
            or seal_account.disposed
            or seal_account.entries != 1
            or seal_account.nodes != 0
            or workspace_account.role != "reverse_primitive_cylinder_workspace"
            or workspace_account.disposed
            or workspace_account.entries != 0
            or workspace_account.nodes != 0
            or self._binding_store.ledger is not self.arena.ledger
            or self._binding_store.owner != self._binding_owner
            or self._binding_store.nodes_per_entry != 1
            or not self._binding_store.append_only
            or len(self._binding_store) != 1
            or self._binding_store[0] is not record
            or self._seals.ledger is not self.arena.ledger
            or self._seals.owner != self._seal_owner
            or self._seals.nodes_per_entry != 0
            or len(self._seals) != 1
            or self._seals.get(record) != 0
        ):
            raise ValueError("primitive successor clause authority was altered")
        expected_multiplier = (
            RadialMultiplier(1, 0) if self.growth == 0 else RadialMultiplier(0, 1)
        )
        if (
            self.arena is not self.carry_atom._arena
            or self.extent != self.carry_atom._extent
            or self.base != self.carry_atom._base
            or self.growth not in (0, 1)
            or self.output_extent != self.extent + self.growth
            or self.action.multiplier != expected_multiplier
            or self.action.innovation != self._beta
        ):
            raise ValueError("primitive successor clause binding was altered")
        self.carry_atom.validate()
        self.arena.resolve(self._correction)
        self.arena.resolve(self.action.innovation)
        self.arena.resolve(self._beta)

    @property
    def beta(self) -> InnovationID:
        self.validate()
        return _copy_reference(self._beta)

    @property
    def correction(self) -> InnovationID:
        self.validate()
        return _copy_reference(self._correction)

    def _innovation_coefficient(self, reference: InnovationID, index: int) -> int:
        """Evaluate one authenticated primitive innovation DAG coordinate."""
        if type(index) is not int:
            raise TypeError("innovation coordinates must be exact integers")
        self.validate()
        total = 0
        pending: list[tuple[InnovationID, int, int]] = []

        def push(item: tuple[InnovationID, int, int]) -> None:
            self.arena.ledger.reserve(self._workspace_owner, nodes=1)
            try:
                pending.append(item)
            except BaseException:
                self.arena.ledger.release(self._workspace_owner, nodes=1)
                raise

        push((_copy_reference(reference), index, 1))
        try:
            while pending:
                reference, coordinate, scale = pending.pop()
                self.arena.ledger.release(self._workspace_owner, nodes=1)
                self.arena.ledger.bump("reverse_primitive_cylinder_dag_visits")
                node = self.arena.resolve(reference)
                if type(node) is _Zero:
                    continue
                if type(node) is _Atom:
                    if node.semantic != self.carry_atom._semantic:
                        raise ValueError(
                            "primitive clause contains a foreign carry atom"
                        )
                    total += scale * self.carry_atom.coefficient(coordinate)
                    continue
                if type(node) is _Scale:
                    push((node.child, coordinate, scale * node.coefficient))
                    continue
                if type(node) is _Charted:
                    chart = node.chart
                    if chart.extent_scale or chart.growth_scale:
                        raise ValueError("primitive beta contains an unbound chart")
                    push(
                        (
                            node.child,
                            chart.slope * coordinate + chart.offset,
                            scale,
                        )
                    )
                    continue
                if type(node) is _Add:
                    push((node.left, coordinate, scale))
                    push((node.right, coordinate, scale))
                    continue
                if type(node) is _Radial:
                    raise ValueError(
                        "primitive beta contains an unexpected radial node"
                    )
                raise TypeError("primitive beta contains an unknown symbolic node")
        finally:
            if pending:
                self.arena.ledger.release(self._workspace_owner, nodes=len(pending))
                pending.clear()
        return total

    def beta_coefficient(self, index: int) -> int:
        """Evaluate the constructed formal beta DAG at one signed coordinate."""
        return self._innovation_coefficient(self._beta, index)

    def output_coefficient(self, index: int) -> int:
        """Evaluate the first output ``D=P+(z-b)Q`` at one coordinate."""
        if type(index) is not int:
            raise TypeError("output coordinates must be exact integers")
        self.validate()
        return self.carry_atom.source_pair_coefficient(
            index
        ) + self._innovation_coefficient(self._correction, index)

    def successor_pair_coefficient(self, index: int) -> int:
        """Evaluate ``P' = M'P + beta`` at one signed coordinate."""
        if type(index) is not int:
            raise TypeError("successor pair coordinates must be exact integers")
        self.validate()
        source = self.carry_atom.source_pair_coefficient
        radial = (
            2 * source(index) if self.growth == 0 else source(index) + source(index - 1)
        )
        return radial + self.beta_coefficient(index)

    def close(self) -> None:
        """Release the binding lease; the shared arena and source ports stay live."""
        if self._closed:
            return
        count = len(self._binding_store)
        self._binding_store._rollback_unpublished(0)
        seal_count = len(self._seals)
        self._seals.clear()
        if count:
            self.arena.ledger.release(self._binding_owner, entries=count, nodes=count)
        self.arena.ledger.mark_disposed(self._binding_owner)
        if seal_count:
            self.arena.ledger.release(self._seal_owner, entries=seal_count)
        self.arena.ledger.mark_disposed(self._seal_owner)
        self.arena.ledger.mark_disposed(self._workspace_owner)
        self.carry_atom._invalidate()
        object.__setattr__(self, "_closed", True)


def primitive_successor_clause(
    arena: SymbolicInnovationArena,
    ports: SourceCarryPorts,
) -> PrimitiveSuccessorClause:
    """Bind the exact primitive whole-function identity to authenticated ports.

    Construction admits only source metadata and the terminal carry.  Point
    coefficients are consumed lazily from the already-owned source carry ports.
    """
    if type(arena) is not SymbolicInnovationArena:
        raise TypeError("primitive cylinder construction requires a symbolic arena")
    if type(ports) is not SourceCarryPorts:
        raise TypeError("primitive cylinder construction requires source carry ports")
    if arena.ledger is not ports._ledger:
        raise ValueError("primitive cylinder ports and arena require one ledger")
    source = ports.source
    extent = ports.width
    growth = ports.terminal
    if growth not in (0, 1):
        raise ValueError("reverse/add terminal carry must be binary")
    base = source.base
    arena.ledger.bump("reverse_primitive_cylinder_source_admissions")

    source_owner = ports._cache.owner
    semantic = _carry_semantic(source_owner, base, extent, growth)
    missing_nodes, missing_units = _planned_primitive_nodes(
        arena, semantic, base=base, reflection=extent + growth - 1
    )
    # Preflight exact interner misses before publishing Q. Each arena node owns
    # one node entry and one key entry; the clause adds binding and seal entries.
    arena.ledger.check_capacity(entries=2 + 2 * missing_nodes, nodes=1 + missing_units)

    binding_owner = arena.ledger.register(
        f"reverse-primitive-cylinder-binding-{arena.ledger.owner_count}",
        "spatial_binding",
    )
    seal_owner = arena.ledger.register(
        f"reverse-primitive-cylinder-seal-{arena.ledger.owner_count}",
        "reverse_action_interner",
    )
    workspace_owner = arena.ledger.register(
        f"reverse-primitive-cylinder-workspace-{arena.ledger.owner_count}",
        "reverse_primitive_cylinder_workspace",
    )
    binding_store: LedgerList[_PrimitiveClauseRecord] = arena.ledger.make_list(
        binding_owner, nodes_per_entry=1, append_only=True
    )
    seals: LedgerDict[_PrimitiveClauseRecord, int] = arena.ledger.make_dict(seal_owner)
    binding: PrimitiveCarryAtomBinding | None = None
    result: PrimitiveSuccessorClause | None = None
    reserved = False
    try:
        # Reserve the fixed source-binding record before adding any source-
        # scoped arithmetic node to the shared append-only innovation arena.
        arena.ledger.reserve_many(((binding_owner, 1, 1), (seal_owner, 1, 0)))
        reserved = True
        binding = PrimitiveCarryAtomBinding.create(
            arena,
            ports,
            source=source,
            extent=extent,
            growth=growth,
            base=base,
        )
        q = binding.atom
        difference = carry_coboundary(arena, q, base=base)
        beta = reflected_innovation(arena, difference, extent=extent, growth=growth)
        multiplier = RadialMultiplier(1, 0) if growth == 0 else RadialMultiplier(0, 1)
        action = arena.action(multiplier, beta)
        beta_reference = _copy_reference(beta)
        authority = _clause_authority(
            arena,
            binding,
            extent=extent,
            growth=growth,
            output_extent=extent + growth,
            base=base,
            correction=difference,
            beta=beta_reference,
            action=action,
            binding_owner=binding_owner,
            seal_owner=seal_owner,
            workspace_owner=workspace_owner,
        )
        record = _PrimitiveClauseRecord(
            binding._source_owner,
            arena._node_owner,
            arena._key_owner,
            _copy_reference(binding._atom),
            extent,
            growth,
            extent + growth,
            base,
            _copy_reference(difference),
            _copy_reference(beta_reference),
            SymbolicRadialInnovation(
                action.multiplier, _copy_reference(action.innovation)
            ),
            binding_owner,
            seal_owner,
            workspace_owner,
            deepcopy(authority),
        )
        binding_store.append(record)
        seals[record] = 0
        result = PrimitiveSuccessorClause(
            arena,
            binding,
            extent,
            growth,
            extent + growth,
            base,
            action,
            _copy_reference(difference),
            beta_reference,
            record,
            binding_owner,
            binding_store,
            seal_owner,
            seals,
            workspace_owner,
        )
        result.validate()
        arena.ledger.register_execution_root(result)
    except BaseException:
        if result is not None:
            result.close()
        else:
            binding_store._rollback_unpublished(0)
            seals.clear()
            if reserved:
                arena.ledger.release(binding_owner, entries=1, nodes=1)
                arena.ledger.release(seal_owner, entries=1)
            arena.ledger.mark_disposed(binding_owner)
            arena.ledger.mark_disposed(seal_owner)
            arena.ledger.mark_disposed(workspace_owner)
            if binding is not None:
                binding._invalidate()
        raise
    arena.ledger.bump("reverse_primitive_cylinder_beta_normalizations")
    assert result is not None
    return result


__all__ = [
    "PrimitiveCarryAtomBinding",
    "PrimitiveSuccessorClause",
    "primitive_successor_clause",
]

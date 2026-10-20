"""Exact checks for the source-bound primitive cylinder identity."""

from __future__ import annotations

from dataclasses import replace
from typing import Protocol, cast

import pytest

import number_compiler.sequences.reverse_add.cylinder_innovation as cylinder
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.fields.centered_carry import (
    carry_coboundary,
    reflected_innovation,
)
from number_compiler.arithmetic.fields.radial_innovation import (
    SymbolicRadialInnovation,
)
from number_compiler.arithmetic.fields.symbolic_innovation import (
    SymbolicInnovationArena,
)
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.sequences.reverse_add.cylinder_innovation import (
    PrimitiveCarryAtomBinding,
    primitive_successor_clause,
)
from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts
from tests.support.arithmetic_fixtures import forge_growth
from tests.support.private_attributes import private_test_attribute


class _PrimitiveNodePlanner(Protocol):
    def __call__(
        self,
        arena: SymbolicInnovationArena,
        semantic: SemanticIdentity,
        *,
        base: int,
        reflection: int,
    ) -> tuple[int, int]: ...


class _ClauseAuthorityBuilder(Protocol):
    def __call__(
        self,
        arena: SymbolicInnovationArena,
        binding: PrimitiveCarryAtomBinding,
        *,
        extent: int,
        growth: int,
        output_extent: int,
        base: int,
        correction: object,
        beta: object,
        action: SymbolicRadialInnovation,
        binding_owner: int,
        seal_owner: int,
        workspace_owner: int,
    ) -> SemanticIdentity: ...


def _digits(value: int, base: int) -> tuple[int, ...]:
    result: list[int] = []
    while True:
        result.append(value % base)
        value //= base
        if not value:
            return tuple(result)


def _source(value: int, base: int) -> ExactSource:
    return ExactSource(_digits(value, base), base, orbit="reverse-add")


def _literal_step(digits: tuple[int, ...], base: int) -> tuple[int, ...]:
    carry = 0
    result: list[int] = []
    for index in range(len(digits)):
        pair = digits[index] + digits[-1 - index]
        total = pair + carry
        result.append(total % base)
        carry = total // base
    if carry:
        result.append(carry)
    return tuple(result)


def test_primitive_arithmetic_preflight_accounts_for_wide_chart_metadata() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    semantic = SemanticIdentity("test", ("primitive-Q",))
    reflection = 1 << 130
    planned_nodes: _PrimitiveNodePlanner = object.__getattribute__(
        cylinder, "_planned_primitive_nodes"
    )
    count, units = planned_nodes(arena, semantic, base=10, reflection=reflection)
    before = ledger.nodes
    q = arena.atom(semantic)
    correction = carry_coboundary(arena, q, base=10)
    reflected_innovation(arena, correction, extent=reflection + 1, growth=0)
    assert count == 6
    assert units == 8
    assert ledger.nodes - before == units
    assert planned_nodes(arena, semantic, base=10, reflection=reflection) == (0, 0)


@pytest.mark.parametrize(
    ("value", "base"),
    (
        (0, 2),
        (1, 2),
        (5, 3),
        (41, 3),
        (0, 10),
        (1, 10),
        (18, 10),
        (99, 10),
        (196, 10),
        (879, 10),
        (909, 10),
        (1041, 10),
        (1051, 10),
        (1593, 10),
    ),
)
def test_clause_matches_literal_beta_and_successor_pair_on_signed_coordinates(
    value: int, base: int
) -> None:
    source = _source(value, base)
    ledger = ResourceLedger()
    ports = SourceCarryPorts(source, ledger)
    arena = SymbolicInnovationArena(ledger)
    clause = primitive_successor_clause(arena, ports)

    pairs = tuple(
        source.digits[i] + source.digits[-1 - i] for i in range(len(source.digits))
    )
    carries = [0]
    for pair in pairs:
        carries.append(int(pair + carries[-1] >= base))
    first = _literal_step(source.digits, base)
    expected_pairs = tuple(first[i] + first[-1 - i] for i in range(len(first)))
    d = len(source.digits) + carries[-1] - 1

    def q(index: int) -> int:
        return carries[index + 1] if 0 <= index < len(source.digits) else 0

    def e(index: int) -> int:
        return q(index - 1) - base * q(index)

    for index in range(-3, len(first) + 3):
        assert clause.beta_coefficient(index) == e(index) + e(d - index)
        expected_output = first[index] if 0 <= index < len(first) else 0
        assert clause.output_coefficient(index) == expected_output
        expected = expected_pairs[index] if 0 <= index < len(first) else 0
        assert clause.successor_pair_coefficient(index) == expected

    assert clause.extent == len(source.digits)
    assert clause.growth == carries[-1]
    assert clause.output_extent == len(first)
    clause.close()
    arena.close()
    ports.dispose()
    assert ledger.entries == ledger.nodes == 0


def test_construction_reads_only_terminal_source_admission(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    source = ExactSource((8,) + (4,) * 126 + (0,), 10, orbit="reverse-add")
    ports = SourceCarryPorts(source, ledger)
    arena = SymbolicInnovationArena(ledger)
    before_reads = ledger.counters.get("reverse_source_ports_source_reads", 0)

    def forbidden(*_args: object, **_kwargs: object) -> int:
        raise AssertionError("primitive construction queried a point output")

    monkeypatch.setattr(SourceCarryPorts, "first_pair", forbidden)
    monkeypatch.setattr(SourceCarryPorts, "second_pair", forbidden)
    clause = primitive_successor_clause(arena, ports)

    assert ledger.counters["reverse_primitive_cylinder_source_admissions"] == 1
    assert ledger.counters["reverse_primitive_cylinder_beta_normalizations"] == 1
    assert (
        ledger.counters.get("reverse_source_ports_source_reads", 0) - before_reads <= 6
    )
    assert "reverse_source_ports_second_pair_queries" not in ledger.counters
    clause.close()


def test_distinct_source_carry_atoms_do_not_cancel_in_one_arena() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    first_ports = SourceCarryPorts(_source(196, 10), ledger)
    second_ports = SourceCarryPorts(_source(99, 10), ledger)
    first = primitive_successor_clause(arena, first_ports)
    second = primitive_successor_clause(arena, second_ports)

    assert first.carry_atom.atom != second.carry_atom.atom
    assert arena.subtract(first.carry_atom.atom, second.carry_atom.atom) != arena.zero

    foreign = arena.action(first.action.multiplier, second.carry_atom.atom)
    object.__setattr__(first, "action", foreign)
    object.__setattr__(first, "_beta", second.carry_atom.atom)
    with pytest.raises(ValueError, match="authority was altered"):
        first.beta_coefficient(0)


def test_consumption_reauthenticates_ports_and_disposable_binding() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    ports = SourceCarryPorts(_source(196, 10), ledger)
    clause = primitive_successor_clause(arena, ports)
    original = ports.audit_snapshot().cache_identity
    owner = ledger.register("foreign-cylinder-cache", "test_foreign_cache")
    foreign: OwnedMemo[tuple[int, int, int], object] = OwnedMemo(ledger, owner)
    object.__setattr__(ports, "_cache", foreign)

    with pytest.raises(ValueError, match="altered"):
        clause.beta_coefficient(0)

    object.__setattr__(ports, "_cache", original)
    foreign.dispose()
    clause.close()
    with pytest.raises(ValueError, match="disposed primitive"):
        clause.beta_coefficient(0)


def test_foreign_ledger_is_rejected_before_binding_publication() -> None:
    source_ledger = ResourceLedger()
    arena_ledger = ResourceLedger()
    ports = SourceCarryPorts(_source(196, 10), source_ledger)
    arena = SymbolicInnovationArena(arena_ledger)

    with pytest.raises(ValueError, match="one ledger"):
        primitive_successor_clause(arena, ports)
    assert source_ledger.counters.get("reverse_source_ports_binding_checks", 0) == 0
    assert not any(row.role == "spatial_binding" for row in arena_ledger.inventory())


def test_refused_binding_lease_is_disposed_without_resource_leak() -> None:
    ledger = ResourceLedger()
    ports = SourceCarryPorts(_source(196, 10), ledger)
    arena = SymbolicInnovationArena(ledger)
    admitted = primitive_successor_clause(arena, ports)
    admitted.close()
    # All arithmetic nodes now exist. Leave no room for a replacement lease.
    ledger.tighten_limits(ledger.nodes, None)
    before = ledger.entries, ledger.nodes, arena.node_count

    with pytest.raises(BlockContextBudgetExceeded):
        primitive_successor_clause(arena, ports)

    binding_rows = [row for row in ledger.inventory() if row.role == "spatial_binding"]
    assert len(binding_rows) == 1
    assert all(row.disposed for row in binding_rows)
    assert all(row.entries == row.nodes == 0 for row in binding_rows)
    assert (ledger.entries, ledger.nodes, arena.node_count) == before
    arena.close()
    ports.dispose()
    assert ledger.entries == ledger.nodes == 0


@pytest.mark.parametrize("tamper", ("growth", "expression"))
def test_published_authority_rejects_coordinated_clause_mutation_before_source_reads(
    monkeypatch: pytest.MonkeyPatch, tamper: str
) -> None:
    ledger = ResourceLedger()
    ports = SourceCarryPorts(_source(196, 10), ledger)
    arena = SymbolicInnovationArena(ledger)
    clause = primitive_successor_clause(arena, ports)
    if tamper == "growth":
        forged_growth = 1 - clause.growth
        forge_growth(clause, forged_growth)
    else:
        foreign = clause.carry_atom.atom
        object.__setattr__(clause, "_beta", foreign)
        object.__setattr__(
            clause,
            "action",
            SymbolicRadialInnovation(clause.action.multiplier, foreign),
        )

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("tampered authority reached source consumption")

    monkeypatch.setattr(SourceCarryPorts, "check_source", forbidden)
    with pytest.raises(ValueError, match="authority was altered"):
        clause.validate()


def test_coordinated_record_and_store_reforge_cannot_replace_publication_seal(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    ports = SourceCarryPorts(_source(196, 10), ledger)
    arena = SymbolicInnovationArena(ledger)
    clause = primitive_successor_clause(arena, ports)
    foreign = clause.carry_atom.atom
    forged_action = SymbolicRadialInnovation(clause.action.multiplier, foreign)
    forged = replace(
        clause.audit_snapshot().record,
        correction=foreign,
        beta=foreign,
        action=forged_action,
    )
    forged = replace(
        forged,
        authority=cast(
            _ClauseAuthorityBuilder,
            private_test_attribute(cylinder, "_clause_authority"),
        )(
            arena,
            clause.carry_atom,
            extent=forged.extent,
            growth=forged.growth,
            output_extent=forged.output_extent,
            base=forged.base,
            correction=forged.correction,
            beta=forged.beta,
            action=forged.action,
            binding_owner=forged.binding_owner,
            seal_owner=forged.seal_owner,
            workspace_owner=forged.workspace_owner,
        ),
    )
    object.__setattr__(clause, "_record", forged)
    object.__setattr__(clause, "_correction", foreign)
    object.__setattr__(clause, "_beta", foreign)
    object.__setattr__(clause, "action", forged_action)
    binding_store = cast(
        list[object],
        object.__getattribute__(clause.audit_snapshot().binding_store, "_data"),
    )
    binding_store[0] = forged

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("forged publication reached source consumption")

    monkeypatch.setattr(SourceCarryPorts, "check_source", forbidden)
    with pytest.raises(ValueError, match="authority was altered"):
        clause.validate()

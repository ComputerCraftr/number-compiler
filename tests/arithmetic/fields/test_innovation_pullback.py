"""Arithmetic substitution foundations, not a 196 temporal-closure certificate."""

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.fields.symbolic_innovation import (
    InnovationID,
    RadialMultiplier,
    SymbolicInnovationArena,
)
from number_compiler.resources.ledger import ResourceLedger


def _arena() -> SymbolicInnovationArena:
    return SymbolicInnovationArena(ResourceLedger())


def _forbidden(*_args: object, **_kwargs: object) -> Never:
    raise AssertionError("symbolic pullback evaluated a polynomial projection")


def test_simultaneous_environment_does_not_rewrite_its_replacements(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena, a, b = _two_atoms()
    difference = arena.subtract(a, b)
    expected = arena.subtract(b, a)
    monkeypatch.setattr(arena, "project_cyclotomic", _forbidden)

    assert arena.substitute_many((a, b, difference), {a: b, b: a}) == (b, a, expected)
    assert all(
        row.entries == row.nodes == 0 and row.disposed
        for row in arena.ledger.inventory()
        if row.name.startswith("innovation-pullback-")
    )


def test_cancellation_and_growth_reflection_use_existing_normalizers() -> None:
    arena, a, b = _two_atoms()
    radial = RadialMultiplier(2, 3)
    chart = CylinderChart(-1, 17)
    roots = (arena.subtract(a, b), arena.chart(a, chart), arena.radial(b, radial))
    replacement = arena.radial(arena.interval(6), radial)
    expected = (
        arena.zero,
        arena.radial(arena.chart(arena.interval(6), CylinderChart(-1, 14)), radial),
        arena.radial(arena.interval(6), RadialMultiplier(4, 6)),
    )

    assert arena.substitute_many(roots, {a: replacement, b: replacement}) == expected


def test_pullback_semantics_agree_with_independent_atom_environment() -> None:
    arena = _arena()
    key_a, key_b = SemanticIdentity("test", ("a",)), SemanticIdentity("test", ("b",))
    a, b = arena.atom(key_a), arena.atom(key_b)
    expression = arena.linear_combination(
        (
            (2, arena.chart(a, CylinderChart(-1, 7))),
            (-3, arena.radial(b, RadialMultiplier(1, 2))),
        )
    )
    # Exact substitutions a=1+z+z^2 and b=-z. Neither output keeps an atom.
    replacement_b = arena.linear_combination(
        ((-1, arena.chart(arena.interval(1), CylinderChart(1, -1))),)
    )
    (result,) = arena.substitute_many(
        (expression,), {a: arena.interval(3), b: replacement_b}
    )
    expected = arena.project_cyclotomic(
        arena.action(RadialMultiplier(), expression),
        order=8,
        bits=8,
        atoms={key_a: (1, 1, 1, 0), key_b: (0, -1, 0, 0)},
    )
    actual = arena.project_cyclotomic(
        arena.action(RadialMultiplier(), result), order=8, bits=8, atoms={}
    )
    assert actual == expected


def test_shared_deep_roots_use_one_iterative_dependency_traversal() -> None:
    arena = _arena()
    atom = arena.atom(SemanticIdentity("test", ("source",)))
    root = atom
    for _ in range(1100):
        root = arena.add(root, atom)
    count = arena.node_count

    assert arena.substitute_many((root,) * 13, {}) == (root,) * 13
    assert arena.node_count == count
    assert arena.ledger.counters["symbolic_innovation_pullback_nodes"] <= count
    assert arena.ledger.counters["symbolic_innovation_pullback_hits"] >= 12


def test_binary_encoded_extent_and_radial_powers_are_not_expanded(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena = _arena()
    atom = arena.atom(SemanticIdentity("test", ("source",)))
    multiplier = RadialMultiplier(1 << 200, 1 << 250)
    expression = arena.radial(atom, multiplier)
    interval = arena.interval(1 << 300)
    expected = arena.radial(interval, multiplier)
    nodes = arena.node_count
    monkeypatch.setattr(arena, "project_cyclotomic", _forbidden)

    assert arena.substitute_many((expression,), {atom: interval}) == (expected,)
    assert arena.node_count == nodes
    assert arena.ledger.counters["symbolic_innovation_pullback_nodes"] == 2


def test_substitution_rejects_foreign_keys_and_values_before_workspace() -> None:
    arena, foreign = _arena(), _arena()
    atom = arena.atom(SemanticIdentity("test", ("source",)))
    other = foreign.atom(SemanticIdentity("test", ("source",)))
    owners, nodes = arena.ledger.owner_count, arena.node_count
    for roots, replacements in (
        ((other,), {}),
        ((atom,), {other: atom}),
        ((atom,), {atom: other}),
        ((atom,), {arena.zero: atom}),
    ):
        with pytest.raises((TypeError, ValueError)):
            arena.substitute_many(roots, replacements)
    assert (arena.ledger.owner_count, arena.node_count) == (owners, nodes)


def test_budget_failure_releases_workspace_and_retry_is_exact() -> None:
    arena = _arena()
    atom = arena.atom(SemanticIdentity("test", ("source",)))
    replacement = arena.interval(7)
    before = arena.ledger.snapshot()
    arena.ledger.max_nodes = before.nodes + 4

    with pytest.raises(BlockContextBudgetExceeded):
        arena.substitute_many((atom,), {atom: replacement})
    after = arena.ledger.snapshot()
    assert (after.nodes, after.entries) == (before.nodes, before.entries)
    assert all(row.accounting_delta in (None, 0) for row in after.inventory)
    assert all(
        row.entries == row.nodes == 0 and row.disposed
        for row in after.inventory
        if row.name.startswith("innovation-pullback-")
    )
    arena.ledger.max_nodes = None
    assert arena.substitute_many((atom,), {atom: replacement}) == (replacement,)


def test_disposed_arena_cannot_publish_even_an_empty_pullback() -> None:
    arena = _arena()
    arena.close()
    with pytest.raises(ValueError, match="disposed"):
        arena.substitute_many((), {})


def _two_atoms() -> tuple[SymbolicInnovationArena, InnovationID, InnovationID]:
    arena = _arena()
    a = arena.atom(SemanticIdentity("test", ("a",)))
    b = arena.atom(SemanticIdentity("test", ("b",)))
    return arena, a, b

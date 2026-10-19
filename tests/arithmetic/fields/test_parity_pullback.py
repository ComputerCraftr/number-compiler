"""Parity erasure is a derived demand, never an exact source-state quotient."""

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.fields.radial_innovation import (
    InnovationID,
    RadialMultiplier,
)
from number_compiler.arithmetic.fields.symbolic_innovation import (
    SymbolicInnovationArena,
)
from number_compiler.resources.ledger import ResourceLedger
from tests.support.symbolic_innovation import evaluate


def _forbidden(*_args: object, **_kwargs: object) -> Never:
    raise AssertionError(
        "parity pullback visited a dead source or scanned coefficients"
    )


@pytest.mark.parametrize("radial", [False, True])
def test_even_homogeneous_source_is_not_visited(
    radial: bool, monkeypatch: pytest.MonkeyPatch
) -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    old = arena.atom(SemanticIdentity("", ("old-source",)))
    dead = (
        arena.radial(old, RadialMultiplier(1, 1 << 200))
        if radial
        else arena.linear_combination(((2, old),))
    )
    forcing = arena.atom(SemanticIdentity("", ("later-source-dependent-forcing",)))
    root = arena.add(dead, forcing)
    replacement = arena.interval(1 << 300)
    resolve = arena.resolve

    def resolve_live(reference: InnovationID) -> object:
        if reference == old:
            _forbidden()
        return resolve(reference)

    monkeypatch.setattr(arena, "resolve", resolve_live)
    monkeypatch.setattr(arena, "project_cyclotomic", _forbidden)
    result = arena.substitute_parity_many((root,), {forcing: replacement})
    assert result == (replacement,)
    assert arena.ledger.counters["symbolic_innovation_parity_pruned"] == 1
    # The later forcing still underwent substitution; it was not treated as
    # a source-independent constant when the homogeneous term disappeared.
    assert arena.ledger.counters["symbolic_innovation_pullback_binding_checks"] == 1


@pytest.mark.parametrize("q", [0, 1, 4])
@pytest.mark.parametrize("coefficient", [-3, -2, 1, 2, 3])
def test_parity_pullback_matches_exact_substitution(q: int, coefficient: int) -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    atom = arena.atom(SemanticIdentity("", ("source",)))
    root = arena.linear_combination(
        (
            (coefficient, arena.radial(atom, RadialMultiplier(q, 3))),
            (1, arena.chart(atom, CylinderChart(-1, 7))),
        )
    )
    replacement = arena.interval(4)
    (exact,) = arena.substitute_many((root,), {atom: replacement})
    (parity,) = arena.substitute_parity_many((root,), {atom: replacement})
    original, reduced = evaluate(arena, exact), evaluate(arena, parity)
    assert {i: v % 2 for i, v in original.items() if v % 2} == {
        i: v % 2 for i, v in reduced.items() if v % 2
    }


def test_parity_request_does_not_change_exact_output_or_replacement_environment() -> (
    None
):
    arena = SymbolicInnovationArena(ResourceLedger())
    a = arena.atom(SemanticIdentity("", ("a",)))
    b = arena.atom(SemanticIdentity("", ("b",)))
    doubled = arena.radial(a, RadialMultiplier(1, 0))
    assert arena.substitute_parity_many((a, b, doubled), {a: b, b: a}) == (
        b,
        a,
        arena.zero,
    )
    assert arena.substitute_many((doubled,), {}) == (doubled,)


def test_parity_pullback_rejects_foreign_operands_and_releases_failed_workspace() -> (
    None
):
    arena = SymbolicInnovationArena(ResourceLedger())
    foreign = SymbolicInnovationArena(ResourceLedger())
    atom = arena.atom(SemanticIdentity("", ("source",)))
    with pytest.raises(ValueError):
        arena.substitute_parity_many((atom,), {atom: foreign.interval(2)})
    before = arena.ledger.snapshot()
    arena.ledger.max_nodes = before.nodes
    with pytest.raises(BlockContextBudgetExceeded):
        arena.substitute_parity_many((atom,), {})
    after = arena.ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    assert all(row.accounting_delta in (None, 0) for row in after.inventory)

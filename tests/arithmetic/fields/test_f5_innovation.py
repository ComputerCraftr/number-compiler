"""Shared F5 forcing construction; no source-discovery claims are made here."""

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.fields.f5_innovation import compose_f5_forcing
from number_compiler.arithmetic.fields.symbolic_innovation import (
    RadialMultiplier,
    SymbolicInnovationArena,
)
from number_compiler.arithmetic.polynomials.centered_f5 import CenteredF5Transport
from number_compiler.arithmetic.polynomials.f5_transport import (
    F5AffineTransport,
    F5SpatialTransport,
)
from number_compiler.resources.ledger import ResourceLedger
from tests.arithmetic.fields.test_centered_carry import _evaluate, _polynomial


@pytest.mark.parametrize("growth", [0, 1, 4, 5, 9, 20])
def test_f5_handle_composition_matches_exact_integer_lift(growth: int) -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    left = _polynomial(arena, [2, -1, 4])
    right = _polynomial(arena, [-3, 1, 0, 2])
    before = F5AffineTransport(F5SpatialTransport(1, 2), left)
    after = F5AffineTransport(F5SpatialTransport(3, growth), right)
    result = compose_f5_forcing(arena, before, after)
    exact = arena.add(arena.radial(left, RadialMultiplier(3, growth)), right)

    got = _evaluate(arena, result.forcing)
    expected = _evaluate(arena, exact)
    assert {i: v % 5 for i, v in got.items() if v % 5} == {
        i: v % 5 for i, v in expected.items() if v % 5
    }
    assert result.linear == before.linear.then(after.linear)
    arena.close()


def test_dense_operator_reuses_ledger_handles_without_atom_evaluation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    left = arena.atom(SemanticIdentity("", ("left-forcing",)))
    right = arena.atom(SemanticIdentity("", ("right-pulled-forcing",)))
    before = F5AffineTransport(F5SpatialTransport(1, 2), left)
    after = F5AffineTransport(F5SpatialTransport(3, 5**64 - 1), right)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("forcing construction evaluated an observation")

    monkeypatch.setattr(arena, "project_cyclotomic", forbidden)
    monkeypatch.setattr(F5SpatialTransport, "coefficient", forbidden)
    monkeypatch.setattr(F5SpatialTransport, "shifts", forbidden)
    monkeypatch.setattr(CenteredF5Transport, "shifts", forbidden)
    nodes = arena.node_count
    result = compose_f5_forcing(arena, before, after)
    assert arena.node_count - nodes == 2 * 256 + 2
    assert arena.ledger.counters["symbolic_innovation_f5_shift_requests"] == 256
    assert arena.ledger.counters["symbolic_innovation_f5_compositions"] == 1
    retained = arena.node_count
    assert compose_f5_forcing(arena, before, after) == result
    assert arena.node_count == retained
    # Warm memoization validates handles but does not repeat construction.
    assert arena.ledger.counters["symbolic_innovation_f5_shift_requests"] == 256
    assert arena.ledger.counters["symbolic_innovation_f5_composition_hits"] == 1
    arena._f5_composition_cache().clear()
    assert compose_f5_forcing(arena, before, after) == result
    assert arena.node_count == retained
    assert arena.ledger.counters["symbolic_innovation_f5_shift_requests"] == 512
    assert all(row.accounting_delta in (None, 0) for row in arena.ledger.inventory())
    arena.close()


def test_foreign_closed_and_budget_limited_forcing_cannot_publish() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    foreign = SymbolicInnovationArena(ResourceLedger())
    left = F5AffineTransport(F5SpatialTransport(), arena.interval(1))
    other = F5AffineTransport(F5SpatialTransport(1, 2), foreign.interval(1))
    count = arena.node_count
    with pytest.raises(ValueError):
        compose_f5_forcing(arena, left, other)
    assert arena.node_count == count
    local = F5AffineTransport(other.linear, left.forcing)
    arena.ledger.max_nodes = arena.ledger.snapshot().nodes
    with pytest.raises(BlockContextBudgetExceeded):
        compose_f5_forcing(arena, left, local)
    assert arena.node_count == count
    arena.close()
    with pytest.raises(ValueError):
        compose_f5_forcing(arena, left, local)
    foreign.close()

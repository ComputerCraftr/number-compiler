"""Bounded forcing residues, with literal polynomials used only as test oracles."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.fields.live_forcing import (
    LiveForcingProjection,
    ResidueRun,
)
from number_compiler.arithmetic.fields.radial_innovation import (
    InnovationID,
    RadialMultiplier,
)
from number_compiler.arithmetic.fields.symbolic_innovation import (
    SymbolicInnovationArena,
)
from number_compiler.resources.ledger import ResourceLedger
from tests.support.symbolic_innovation import evaluate


def test_dead_forcing_is_pruned_before_child_access(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    atom = arena.atom(SemanticIdentity("", ("old-forcing",)))
    dead = arena.radial(atom, RadialMultiplier(10**100, 10**100))
    original = arena.resolve

    def resolve(reference: InnovationID) -> object:
        if reference == atom:
            raise AssertionError("dead atom visited")
        return original(reference)

    monkeypatch.setattr(arena, "resolve", resolve)
    retained = ledger.entries, ledger.nodes
    with LiveForcingProjection(arena, dead) as view:
        assert tuple(view.packets()) == ()
        assert view.residue_runs(-(10**100), 10**100) == (
            ResidueRun(-(10**100), 10**100, 0),
        )
    assert (ledger.entries, ledger.nodes) == retained
    assert ledger.counters["live_forcing_dead_contexts"] == 1


def test_shared_atom_has_distinct_live_and_dead_contexts() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    atom = arena.atom(SemanticIdentity("", ("shared-forcing",)))
    expression = arena.add(arena.radial(atom, RadialMultiplier(5, 0)), atom)
    with LiveForcingProjection(arena, expression) as view:
        assert len(tuple(view.packets())) == 1
        assert next(view.packets()).atom == atom
        with pytest.raises(TypeError, match="unresolved atom"):
            view.residue_runs(0, 10)
    assert arena.resolve(atom) is not None


@pytest.mark.parametrize("slope", [-1, 1])
@pytest.mark.parametrize("offset", [-7, 4])
@pytest.mark.parametrize("q", [0, 4, 5])
@pytest.mark.parametrize("r", [0, 3, 15])
def test_modular_packets_match_literal_laurent_oracle(
    slope: int, offset: int, q: int, r: int
) -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    inner = arena.chart(
        arena.radial(arena.interval(5), RadialMultiplier(q, r)),
        CylinderChart(slope, offset),
    )
    expression = arena.linear_combination(((7, inner), (-3, arena.interval(7))))
    expected = evaluate(arena, expression)
    retained = ledger.entries, ledger.nodes
    with LiveForcingProjection(arena, expression) as view:
        runs = view.residue_runs(-40, 40)
        actual = {i: run.residue for run in runs for i in range(run.start, run.stop)}
        assert actual == {i: expected.get(i, 0) % 32 for i in range(-40, 40)}
        held = ledger.entries, ledger.nodes
        assert view.residue_runs(-40, 40) == runs
        assert (ledger.entries, ledger.nodes) == held
    assert (ledger.entries, ledger.nodes) == retained


def test_radial_content_accumulates_across_charts_and_scales() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    atom = arena.atom(SemanticIdentity("", ("nested-forcing",)))
    inner = arena.radial(atom, RadialMultiplier(2, 4))
    inner = arena.chart(inner, CylinderChart(-1, 8))
    inner = arena.linear_combination(((3, inner),))
    expression = arena.radial(inner, RadialMultiplier(3, 5))
    with LiveForcingProjection(arena, expression) as view:
        assert not tuple(view.packets())


def test_wide_interval_uses_bounded_stencil_not_span() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    width = 10**200
    expression = arena.radial(arena.interval(width), RadialMultiplier(4, 15))
    with LiveForcingProjection(arena, expression) as view:
        runs = view.residue_runs(-1, width + 16)
        assert len(runs) <= 33
    assert ledger.counters["live_forcing_stencil_terms"] == 16


def test_modular_cancellation_does_not_erase_exact_expression() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    expression = arena.linear_combination(((32, arena.interval(1)),))
    with LiveForcingProjection(arena, expression) as view:
        assert not tuple(view.packets())
    assert evaluate(arena, expression) == {0: 32}


def test_unadmitted_live_growth_refuses_without_leaking() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    expression = arena.radial(arena.interval(1), RadialMultiplier(0, 16))
    retained = ledger.entries, ledger.nodes
    with pytest.raises(ValueError, match="growth bound"):
        LiveForcingProjection(arena, expression)
    assert (ledger.entries, ledger.nodes) == retained


def test_failed_demand_releases_scratch_and_retains_live_atom() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    expression = arena.atom(SemanticIdentity("", ("unresolved-forcing",)))
    with LiveForcingProjection(arena, expression) as view:
        retained = ledger.entries, ledger.nodes
        with pytest.raises(TypeError, match="unresolved atom"):
            view.residue_runs(0, 100)
        assert (ledger.entries, ledger.nodes) == retained
        assert len(tuple(view.packets())) == 1


def test_budget_failure_cleans_constructor_transaction() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    expression = arena.interval(12)
    retained = ledger.entries, ledger.nodes
    ledger.tighten_limits(ledger.nodes + 5, ledger.entries + 5)
    with pytest.raises(BlockContextBudgetExceeded):
        LiveForcingProjection(arena, expression)
    assert (ledger.entries, ledger.nodes) == retained


def test_foreign_and_closed_authorities_are_rejected() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    other = SymbolicInnovationArena(ResourceLedger())
    with pytest.raises(ValueError):
        LiveForcingProjection(arena, other.interval(1))
    view = LiveForcingProjection(arena, arena.interval(1))
    view.close()
    with pytest.raises(ValueError, match="closed"):
        view.residue_runs(0, 1)


def test_closed_arena_invalidates_projection() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    view = LiveForcingProjection(arena, arena.interval(1))
    arena.close()
    with pytest.raises(ValueError, match="disposed"):
        view.residue_runs(0, 1)
    view.close()


def test_modular_projection_cannot_be_published_as_exact_source() -> None:
    from number_compiler.sequences.reverse_add.source_images import (
        ReverseSourceImageWorkspace,
    )

    ledger = ResourceLedger()
    workspace = ReverseSourceImageWorkspace(ledger, 196, 0)
    arena = SymbolicInnovationArena(ledger)
    with LiveForcingProjection(arena, arena.interval(1)) as view:
        for payload in (view, next(view.packets()), view.residue_runs(0, 1)):
            with pytest.raises(TypeError, match="payload sort"):
                workspace.adapter.validate_payload(payload)
    arena.close()
    workspace.dispose()
    assert ledger.entries == ledger.nodes == 0


def test_construction_workspace_is_not_retained_by_empty_view() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    expression = arena.radial(arena.interval(10**200), RadialMultiplier(5, 15))
    retained = ledger.entries, ledger.nodes
    with LiveForcingProjection(arena, expression) as view:
        assert tuple(view.packets()) == ()
        assert (ledger.entries, ledger.nodes) == retained

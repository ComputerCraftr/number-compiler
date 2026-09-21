"""Exact cyclotomic forgetting of intrinsically dead innovation occurrences."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.fields.symbolic_innovation import (
    InnovationID,
    RadialMultiplier,
    SymbolicInnovationArena,
)
from number_compiler.arithmetic.polynomials.cyclotomic_ring import CyclotomicRing
from number_compiler.arithmetic.polynomials.cyclotomic_transport import (
    power_two_cyclotomic_radial_quotient,
)
from number_compiler.resources.ledger import ResourceLedger


def _key(name: str) -> SemanticIdentity:
    return SemanticIdentity("", ("projection-forgetting", name))


def test_dead_radial_occurrence_skips_atom_lookup_and_child_traversal(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    atom = arena.atom(_key("poisoned"))
    dead = arena.radial(atom, RadialMultiplier(5, 0))
    original_resolve = arena.resolve

    def poisoned_resolve(reference: InnovationID) -> object:
        if reference == atom:
            raise AssertionError("dead radial child was traversed")
        return original_resolve(reference)

    monkeypatch.setattr(arena, "resolve", poisoned_resolve)
    retained = ledger.entries, ledger.nodes
    projected = arena.project_cyclotomic(
        arena.action(RadialMultiplier(), dead), order=8, bits=5, atoms={}
    )

    assert projected.innovation == (0, 0, 0, 0)
    assert (ledger.entries, ledger.nodes) == retained
    assert ledger.counters["symbolic_innovation_projection_pruned_occurrences"] == 1


def test_composed_radials_prune_through_scale_and_chart() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    atom = arena.atom(_key("composed"))
    inner = arena.radial(atom, RadialMultiplier(2, 0))
    scaled = arena.linear_combination(((3, inner),))
    charted = arena.chart(scaled, CylinderChart(-1, 7))
    dead = arena.radial(charted, RadialMultiplier(3, 0))

    projected = arena.project_cyclotomic(
        arena.action(RadialMultiplier(), dead), order=8, bits=5, atoms={}
    )

    assert projected.innovation == (0, 0, 0, 0)


def test_dead_and_live_occurrences_of_one_atom_are_kept_distinct() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    key = _key("shared")
    shared = arena.atom(key)
    dead = arena.radial(shared, RadialMultiplier(5, 0))
    live = arena.chart(shared, CylinderChart(1, -2))
    mixed = arena.add(dead, live)
    atoms = {key: (1, 4, 2, 3)}

    actual = arena.project_cyclotomic(
        arena.action(RadialMultiplier(), mixed), order=8, bits=5, atoms=atoms
    )
    expected = arena.project_cyclotomic(
        arena.action(RadialMultiplier(), live), order=8, bits=5, atoms=atoms
    )

    assert actual.innovation == expected.innovation


def test_exact_live_chain_matches_direct_quotient_arithmetic() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    key = _key("live-differential")
    atom = arena.atom(key)
    inner = arena.radial(atom, RadialMultiplier(1, 0))
    scaled = arena.linear_combination(((3, inner),))
    charted = arena.chart(scaled, CylinderChart(1, -2))
    expression = arena.radial(charted, RadialMultiplier(1, 0))
    supplied = (1, 4, 2, 3)

    actual = arena.project_cyclotomic(
        arena.action(RadialMultiplier(), expression),
        order=8,
        bits=5,
        atoms={key: supplied},
    )

    ring = CyclotomicRing(8, 32)
    radial = power_two_cyclotomic_radial_quotient(4, 1, 0, bits=5).multiplier_residue()
    expected = ring.multiply(supplied, radial)
    expected = ring.scale(expected, 3)
    charted_expected = ring.zero
    z = ring.reduce((0, 1))
    for index, coefficient in enumerate(expected):
        z_power = ring.power_residue(z, index + 2).value
        charted_expected = ring.add(charted_expected, ring.scale(z_power, coefficient))
    expected = ring.multiply(charted_expected, radial)
    assert actual.innovation == expected


def test_deep_live_unary_chain_computes_each_suffix_once() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    key = _key("deep-live")
    expression = arena.atom(key)
    depth = 128
    for _ in range(depth):
        expression = arena.linear_combination(((2, expression),))
        expression = arena.chart(expression, CylinderChart(1, -1))
    retained = ledger.entries, ledger.nodes

    projected = arena.project_cyclotomic(
        arena.action(RadialMultiplier(), expression),
        order=8,
        bits=5,
        atoms={key: (1, 0, 0, 0)},
    )

    assert len(projected.innovation) == 4
    assert (
        ledger.counters["symbolic_innovation_projection_dependency_visits"]
        == 2 * depth + 1
    )
    assert (ledger.entries, ledger.nodes) == retained


def test_exact_zero_may_prune_wide_intrinsic_radial_metadata() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    atom = arena.atom(_key("wide-dead"))
    dead = arena.radial(atom, RadialMultiplier(1 << 100, 0))

    projected = arena.project_cyclotomic(
        arena.action(RadialMultiplier(), dead), order=8, bits=5, atoms={}
    )

    assert projected.innovation == (0, 0, 0, 0)


def test_live_projection_failure_charges_work_and_releases_retention() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    atom = arena.atom(_key("missing-live"))
    retained = ledger.entries, ledger.nodes

    with pytest.raises(ValueError, match="unresolved atom"):
        arena.project_cyclotomic(
            arena.action(RadialMultiplier(), atom), order=8, bits=5, atoms={}
        )

    assert (ledger.entries, ledger.nodes) == retained
    assert ledger.counters["symbolic_innovation_projection_dependency_visits"] > 0
    assert ledger.counters["symbolic_innovation_projection_workspace_frames"] > 0


def test_pruned_result_is_still_charged_to_projection_retention() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    atom = arena.atom(_key("bounded-retention"))
    dead = arena.radial(atom, RadialMultiplier(5, 0))
    retained = ledger.entries, ledger.nodes
    # The active frame and suffix summary fit. Publishing the third temporary
    # entry (the projected zero) must still pass through OwnedMemo admission.
    ledger.tighten_limits(ledger.nodes + 16, ledger.entries + 2)

    with pytest.raises(BlockContextBudgetExceeded):
        arena.project_cyclotomic(
            arena.action(RadialMultiplier(), dead), order=8, bits=5, atoms={}
        )

    assert (ledger.entries, ledger.nodes) == retained
    assert ledger.counters["symbolic_innovation_projection_pruned_occurrences"] == 1

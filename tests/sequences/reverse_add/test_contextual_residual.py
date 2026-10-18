"""Contextual successor congruence, with physical carry derivation."""

from collections.abc import Sequence
from itertools import product

import pytest

from number_compiler.arithmetic.carry.event_memory import pair_step
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
    FactoredFunctionID,
)
from number_compiler.hashlife.tiles.tiles import TileArena
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.ownership import audit_execution_ownership
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.resources.reverse_residual_inventory import audit_reverse_residuals
from number_compiler.sequences.reverse_add.active_output import PAIR
from number_compiler.sequences.reverse_add.contextual_residual import (
    ResidualSuccessorConflict,
    ReverseContextualResidualArena,
)


def _runtime() -> tuple[
    ReverseContextualResidualArena,
    tuple[FinitePort, ...],
    tuple[FactoredFunctionID, ...],
]:
    arena = ReverseContextualResidualArena(BitFunctionArena(ResourceLedger()))
    ports = tuple(
        FinitePort(PortVariable(0, i, "pair-context", 0), 19) for i in range(2)
    )
    values = tuple(arena.bits.variable(ports, p, PAIR) for p in ports)
    return arena, ports, values


def _q7(
    arena: ReverseContextualResidualArena, value: FactoredFunctionID
) -> FactoredFunctionID:
    starts = (0, 4, 5, 9, 10, 14, 15)
    return arena.bits.map_atoms(
        value,
        AtomSort("reverse-seven-bands", 7),
        tuple(sum(s >= start for start in starts) - 1 for s in range(19)),
    )


def test_derived_carries_and_three_stencils_match_all_symmetric_width_four_fields() -> (
    None
):
    arena, ports, s, t, ds, dt, growth = _symmetric_context()
    outer = arena.no_growth(s, (), (ds, dt, dt))
    inner = arena.no_growth(t, (ds,), (ds, dt))
    edge = arena.growth_edge(s)
    stagger = arena.growth_interior(t, s, (ds,), (ds, dt, dt))
    for a, b in product(range(19), repeat=2):
        expected, g = pair_step((a, b, b, a), 10)
        bind = {ports[0].variable: a, ports[1].variable: b}
        assert arena.bits.evaluate(growth, bind) == g
        observed = (edge, stagger) if g else (outer, inner)
        assert tuple(arena.bits.evaluate(f, bind) for f in observed) == expected[:2]


def test_no_growth_seven_bands_transport_next_domain_and_updated_neighbor() -> None:
    arena, ports, s, t, ds, dt, growth = _symmetric_context()
    allowed = arena.bits.map_atoms(growth, BOOL, (1, 0))
    outer = arena.no_growth(s, (), (ds, dt, dt))
    inner = arena.no_growth(t, (ds,), (ds, dt))
    before = arena.profile(ds, (_q7(arena, s), t), allowed, frame="same-coordinate")
    after = arena.profile(
        arena.domain(outer), (inner,), allowed, frame="same-coordinate"
    )
    count = arena.certify(before, after, ports[0])
    assert count < 19
    for a in range(19):
        residual = arena.residual(before, ports[0], a)
        assert arena.advance(before, after, ports[0], residual) == arena.residual(
            after, ports[0], a
        )
    assert arena.residual(before, ports[0], 0) == arena.residual(before, ports[0], 3)


def test_growth_refines_only_observable_contextual_distinctions() -> None:
    arena, ports, s, t, ds, dt, growth = _symmetric_context()
    neighbor = arena.bits.map_atoms(s, BOOL, tuple(int(i == 10) for i in range(19)))
    allowed = arena.bits.restrict(growth, neighbor)
    edge = arena.growth_edge(s)
    interior = arena.growth_interior(t, s, (ds,), (ds, dt, dt))
    before = arena.profile(dt, (_q7(arena, t), s), allowed, frame="growth-interior")
    after = arena.profile(
        arena.domain(interior), (edge,), allowed, frame="growth-interior"
    )
    assert arena.residual(before, ports[1], 7) == arena.residual(before, ports[1], 8)
    assert arena.residual(after, ports[1], 7) != arena.residual(after, ports[1], 8)
    with pytest.raises(ResidualSuccessorConflict):
        arena.certify(before, after, ports[1])
    assert not arena._successors
    refined = arena.refine(before, after, ports[1])
    assert arena.residual(refined, ports[1], 5) == arena.residual(refined, ports[1], 7)
    assert arena.residual(refined, ports[1], 7) != arena.residual(refined, ports[1], 8)
    for value in range(19):
        actual = arena.advance(
            refined, after, ports[1], arena.residual(refined, ports[1], value)
        )
        assert actual == arena.residual(after, ports[1], value)


def test_updated_context_must_factor_even_when_carry_observation_is_constant() -> None:
    arena, ports, (s, _t) = _runtime()
    zero = arena.bits.constant(FunctionSignature(ports, PAIR), 0)
    allowed = arena.bits.constant(FunctionSignature(ports, BOOL), 1)
    before = arena.profile(arena.domain(zero), (), allowed, frame="same-coordinate")
    after = arena.profile(arena.domain(zero), (s,), allowed, frame="growth-interior")
    with pytest.raises(ResidualSuccessorConflict):
        arena.certify(before, after, ports[0])
    refined = arena.refine(before, after, ports[0])
    # Exact context transport really requires all 19 values in this profile.
    assert len({arena.residual(refined, ports[0], i) for i in range(19)}) == 19
    narrowed = arena.bits.restrict(
        after, arena.bits.map_atoms(s, BOOL, tuple(int(i < 10) for i in range(19)))
    )
    with pytest.raises(ValueError, match="admitted domain"):
        arena.certify(before, narrowed, ports[0])


def test_complete_two_event_growth_alignment_chain_advances_without_source(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena, ports, (s, _t) = _runtime()
    allowed = arena.bits.map_atoms(
        s, BOOL, tuple(int(i in (10, 12, 14, 16, 18)) for i in range(19))
    )
    d0 = arena.domain(s)
    g0 = arena.carry_prefix((d0,))
    first = arena.growth_edge(s)
    d1 = arena.domain(first)
    g1 = arena.carry_prefix((d1, d1))
    second = arena.no_growth(first, (), (d1,))
    d2 = arena.domain(second)
    g2 = arena.carry_prefix((d2, d2))
    one = arena.bits.constant(
        FunctionSignature(ports, AtomSort("relative-width", 3)), 1
    )
    two = arena.bits.constant(
        FunctionSignature(ports, AtomSort("relative-width", 3)), 2
    )
    profiles = (
        arena.profile(d0, (g0, one), allowed, frame="same-coordinate"),
        arena.profile(d1, (g1, two), allowed, frame="growth-edge"),
        arena.profile(d2, (g2, two), allowed, frame="same-coordinate"),
    )
    with pytest.raises(ResidualSuccessorConflict):
        arena.certify(profiles[0], profiles[1], ports[0])
    closed = arena.compile_chain(profiles, ports[0])
    states = {i: arena.residual(closed[0], ports[0], i) for i in (10, 12, 14, 16, 18)}
    targets = {i: arena.residual(profiles[-1], ports[0], i) for i in states}
    assert states[10] == states[12] and states[14] == states[16]
    assert len(set(states.values())) == 3
    for i in states:
        y, g = pair_step((i,), 10)
        z, h = pair_step(y, 10)
        assert (g, len(y), len(z)) == (1, 2, 2)
        binding = {ports[0].variable: i, ports[1].variable: 0}
        assert arena.bits.evaluate(first, binding) == y[0]
        assert arena.bits.evaluate(second, binding) == z[0]
        assert arena.bits.evaluate(g1, binding) == h

    # The finite two-event merge must not become an all-future certificate.
    ordinary = arena.no_growth(second, (), (d2,))
    third_edge = arena.bits.select(g2, arena.growth_edge(second), ordinary)
    third_middle = arena.bits.select(
        g2, arena.growth_interior(second, second, (d2,), (d2,)), ordinary
    )
    de, dm = arena.domain(third_edge), arena.domain(third_middle)
    g3 = arena.bits.select(
        g2, arena.carry_prefix((de, dm, de)), arena.carry_prefix((de, de))
    )
    width3 = arena.bits.map_atoms(g2, AtomSort("relative-width", 4), (2, 3))
    profile3 = arena.profile(de, (dm, g2, g3, width3), allowed, frame="same-coordinate")
    with pytest.raises(ResidualSuccessorConflict):
        arena.certify(closed[0], profile3, ports[0])
    extended = arena.compile_chain((*profiles, profile3), ports[0])
    assert len({arena.residual(extended[0], ports[0], i) for i in states}) == 5

    def advance_row(row: tuple[int, ...]) -> tuple[int, ...]:
        return pair_step(row, 10)[0]

    def middle_symbol(row: Sequence[int]) -> int:
        return row[1]

    for i in states:
        row: tuple[int, ...] = (i,)
        for _ in range(3):
            row = advance_row(row)
        assert len(row) > 1
        binding = {ports[0].variable: i, ports[1].variable: 0}
        assert arena.bits.evaluate(third_edge, binding) == row[0]
        assert arena.bits.evaluate(third_middle, binding) == middle_symbol(row)
        assert arena.bits.evaluate(width3, binding) == len(row)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("certified residual advance revisited source arithmetic")

    monkeypatch.setattr(arena.bits, "evaluate", forbidden)
    monkeypatch.setattr(arena, "residual", forbidden)
    monkeypatch.setattr(arena, "_cofactors", forbidden)
    monkeypatch.setattr(TileArena, "leaf", forbidden)
    monkeypatch.setattr(TileArena, "join", forbidden)
    for i, state in states.items():
        state = arena.advance(closed[0], closed[1], ports[0], state)
        state = arena.advance(closed[1], closed[2], ports[0], state)
        assert state == targets[i]


def test_transport_budget_and_foreign_profiles_fail_closed_and_payloads_are_owned() -> (
    None
):
    arena, ports, (s, _t) = _runtime()
    profile = arena.domain(s)
    arena._rows(profile, profile, ports[0])
    before = arena.ledger.snapshot()
    arena.ledger.max_cache_entries = arena.ledger.entries
    with pytest.raises(BlockContextBudgetExceeded):
        arena.certify(profile, profile, ports[0])
    assert not arena._successors
    assert (arena.ledger.entries, arena.ledger.nodes) == (before.entries, before.nodes)
    arena.ledger.max_cache_entries = None
    assert arena.certify(profile, profile, ports[0]) == 3
    foreign, _, (other, _) = _runtime()
    with pytest.raises(ValueError):
        arena.certify(profile, foreign.domain(other), ports[0])
    assert not audit_execution_ownership(arena.ledger).violations
    report = audit_registered_payloads(arena.ledger)
    assert (
        report.unknown_payloads,
        report.forbidden_future_payloads,
        report.unbounded_future_integers,
    ) == (0, 0, 0)
    snapshot = arena.ledger.snapshot()
    assert not audit_reverse_residuals(
        arena.ledger, tuple(arena.ledger.iter_execution_roots())
    )
    audited = arena.ledger.snapshot()
    audit_counter = "payload_audit_contract_member_visits"
    assert (audited.entries, audited.nodes) == (snapshot.entries, snapshot.nodes)
    assert audited.counters.get(audit_counter, 0) - snapshot.counters.get(
        audit_counter, 0
    ) == 2 * len(arena._successors)
    assert {
        key: value for key, value in audited.counters.items() if key != audit_counter
    } == {
        key: value for key, value in snapshot.counters.items() if key != audit_counter
    }
    key = next(iter(arena._successors))
    original = arena._successors[key]
    arena._successors[key] = arena.residual(profile, ports[0], 18)
    assert audit_registered_payloads(arena.ledger).forbidden_future_payloads > 0
    arena._successors[key] = original
    assert not audit_reverse_residuals(
        arena.ledger, tuple(arena.ledger.iter_execution_roots())
    )


def test_pullback_transports_context_and_invalid_domains_are_not_erased() -> None:
    arena, ports, (s, t) = _runtime()
    allowed = arena.bits.map_atoms(t, BOOL, tuple(int(i < 9) for i in range(19)))
    target = arena.profile(arena.domain(s), (t,), allowed, frame="growth-interior")
    output = arena.growth_edge(s)
    moved = arena.bits.map_atoms(t, PAIR, tuple((i + 1) % 19 for i in range(19)))
    pulled = arena.pullback(
        target, {ports[0].variable: output, ports[1].variable: moved}
    )
    explicit = arena.profile(
        arena.domain(output),
        (moved,),
        arena.bits.map_atoms(moved, BOOL, tuple(int(i < 9) for i in range(19))),
        frame="growth-interior",
    )
    assert pulled == explicit
    for a, b in product((10, 16, 18), (0, 7, 8, 18)):
        bind = {ports[0].variable: a, ports[1].variable: b}
        assert (arena.bits.evaluate(pulled, bind) is not None) == ((b + 1) % 19 < 9)


def test_context_layout_is_part_of_residual_identity() -> None:
    arena, ports, (s, t) = _runtime()
    allowed = arena.bits.constant(FunctionSignature(ports, BOOL), 1)
    other = arena.bits.map_atoms(t, AtomSort("relative-extent", 19), tuple(range(19)))
    pair_context = arena.profile(
        arena.domain(s), (t,), allowed, frame="growth-interior"
    )
    extent_context = arena.profile(
        arena.domain(s), (other,), allowed, frame="growth-interior"
    )
    assert (
        arena.bits.resolve(pair_context).bits == arena.bits.resolve(extent_context).bits
    )
    assert pair_context != extent_context
    arena.certify(pair_context, pair_context, ports[0])
    foreign_layout = arena.residual(extent_context, ports[0], 10)
    with pytest.raises(ValueError, match="no certified successor"):
        arena.advance(pair_context, pair_context, ports[0], foreign_layout)


def _symmetric_context() -> tuple[
    ReverseContextualResidualArena,
    tuple[FinitePort, ...],
    FactoredFunctionID,
    FactoredFunctionID,
    FactoredFunctionID,
    FactoredFunctionID,
    FactoredFunctionID,
]:
    arena, ports, (s, t) = _runtime()
    ds, dt = arena.domain(s), arena.domain(t)
    growth = arena.carry_prefix((ds, dt, dt, ds))
    return arena, ports, s, t, ds, dt, growth

from itertools import product
from typing import Never

import pytest

from devtools.proofs.collatz_spacetime import (
    CollatzCausalSpacetimeEngine,
    CollatzRadixField,
)
from devtools.proofs.collatz_symbolic_action import CollatzSymbolicActionArena
from number_compiler.arithmetic.automata.action_power import ActionPowerArena


def test_symbolic_composition_is_associative_on_action_ids() -> None:
    arena = CollatzSymbolicActionArena()
    for a, b, c in product((1, 2, 3), repeat=3):
        x, y, z = arena.atom(a), arena.atom(b), arena.atom(c)
        assert arena.compose(arena.compose(x, y), z) == arena.compose(
            x, arena.compose(y, z)
        )
    source = CollatzRadixField.from_value(27).span
    action = arena.compose(arena.atom(1), arena.atom(2))
    # (3 * ((3*27+1)/2) + 1)/4 = 31.
    assert arena.residue(source, action, 8) == 31
    assert arena.node(action).h == 2
    assert arena.node(action).k == 3


def test_symbolic_power_retains_exponents_and_ids_without_coefficients() -> None:
    arena = CollatzSymbolicActionArena()
    powers = ActionPowerArena(arena.identity, arena.compose, validate=arena.validate)
    action = powers.power(arena.atom(2), 1 << 30)
    node = arena.node(action)
    assert node.h == 1 << 30
    assert node.k == 1 << 31
    assert arena.action_count == 32
    assert not hasattr(arena, "_offset_ports")
    assert not hasattr(arena, "_tile_ports")
    assert all(isinstance(part, int) for key in powers._compositions for part in key)


def test_production_symbolic_power_never_projects_intermediate_fields(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    engine = CollatzCausalSpacetimeEngine()
    source = CollatzRadixField.from_value((1 << 130) + 27)

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("eager field or scalar arithmetic during action discovery")

    monkeypatch.setattr(CollatzCausalSpacetimeEngine, "_mul3_plus_one", forbidden)
    monkeypatch.setattr(CollatzRadixField, "value", forbidden)
    monkeypatch.setattr(CollatzRadixField, "digits", forbidden)
    target, event = engine.advance_event_power(source, 16)
    expected = (1 << 130) + 27
    shift = 0
    for _ in range(16):
        raw = 3 * expected + 1
        valuation = (raw & -raw).bit_length() - 1
        expected = raw >> valuation
        shift += valuation
    # Only the explicitly requested endpoint is projected.
    from number_compiler.arithmetic.fields.dyadic_tile import iter_symbols

    assert (
        sum(d << (2 * i) for i, d in enumerate(iter_symbols(target.span))) == expected
    )
    assert event.effect.shift == shift
    metrics = engine.metrics()
    assert metrics.primitive_forcing_steps == 0
    assert metrics.nonlinear_branch_evaluations == 16
    assert metrics.exact_endpoint_entries == metrics.macro_applications == 1
    assert engine.symbolic_actions.endpoint_projections == 0
    assert metrics.forcing_occurrences == 0
    assert metrics.symbolic_maximum_port_bits <= 2


def test_symbolic_port_can_observe_an_unbounded_valuation_without_intermediate_tail() -> (
    None
):
    value = ((1 << 140) - 1) // 3
    engine = CollatzCausalSpacetimeEngine()
    target, transport = engine.advance_event_power(
        CollatzRadixField.from_value(value), 1000
    )
    assert target.value() == 1
    assert transport.effect.shift == 140 + 2 * 999
    assert engine.metrics().nonlinear_branch_evaluations == 1


def test_symbolic_endpoints_and_cocycles_match_independent_random_orbits() -> None:
    from random import Random

    rng = Random(196)
    for width in (4, 16, 80, 160):
        for _ in range(4):
            seed = rng.getrandbits(width) | 1
            events = rng.choice((1, 2, 7, 16, 33))
            expected, shift = seed, 0
            for _event in range(events):
                raw = 3 * expected + 1
                valuation = (raw & -raw).bit_length() - 1
                expected = raw >> valuation
                shift += valuation
            engine = CollatzCausalSpacetimeEngine()
            target, transport = engine.advance_event_power(
                CollatzRadixField.from_value(seed), events
            )
            assert target.value() == expected
            assert transport.effect.events == events
            assert transport.effect.shift == shift
            assert transport.effect.physical_steps == events + shift
            assert engine.event_arena.cocycle_materializations == 0


def test_action_canonicalization_erases_different_binary_parenthesizations() -> None:
    arena = CollatzSymbolicActionArena()
    atoms = [arena.atom(value) for value in (1, 3, 2, 2, 4, 1, 6, 2, 1)]
    left = arena.identity
    for atom in atoms:
        left = arena.compose(left, atom)
    right = arena.identity
    for atom in reversed(atoms):
        right = arena.compose(atom, right)
    assert left == right


def test_exact_endpoint_budget_is_separate_from_symbolic_action_interning() -> None:
    source = CollatzRadixField.from_value(27)
    uncached = CollatzCausalSpacetimeEngine(max_jump_entries=0)
    first, first_event = uncached.advance_event_power(source, 2)
    second, second_event = uncached.advance_event_power(source, 2)
    assert first.value() == second.value()
    assert first_event.effect == second_event.effect
    assert uncached.metrics().exact_endpoint_entries == 0
    assert uncached.metrics().macro_applications == 2
    assert uncached.metrics().macro_actions > 0

    bounded = CollatzCausalSpacetimeEngine(max_jump_entries=2)
    for events in (1, 2, 1, 3):
        bounded.advance_event_power(source, events)
    assert bounded.metrics().exact_endpoint_entries == 2
    assert bounded.metrics().macro_applications == 3
    # The read of request1 refreshed it; request2 was the oldest entry.
    assert [key[1] for key in bounded._action_endpoints] == [1, 3]
    bounded.advance_event_power(source, 2)
    assert bounded.metrics().macro_applications == 4
    assert bounded.metrics().exact_endpoint_entries == 2

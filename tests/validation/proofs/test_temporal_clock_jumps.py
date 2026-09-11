"""Executable scope gates for closed clock actions and their formal jump laws.

Finite deck compilation is charged separately from powering. Affine powering
has a supplied event law, not an oracle for future arithmetic births.
"""

from __future__ import annotations

from itertools import product
from typing import Never

import pytest

from devtools.experiments.power_numbers.square_consumer_congruence import (
    _class_ids,
    _terminal_deck_key,
)
from number_compiler.arithmetic.functions.finite_unary import (
    UnaryPowerArena,
    UnaryTransitionEffect,
    quotient_machine_from_moore,
)
from number_compiler.arithmetic.polynomials.arithmetic_tile import ArithmeticTile
from number_compiler.arithmetic.polynomials.primary_jet import (
    PrimaryJetAffineMorphism,
)


def _forbidden(*args: object, **kwargs: object) -> Never:
    raise AssertionError("powered composition evaluated a primitive occurrence")


@pytest.mark.parametrize(
    "family,parameter", (("fermat", 2), ("fermat", 3), ("mersenne", 5), ("mersenne", 7))
)
def test_precompiled_terminal_deck_jumps_without_primitive_occurrences(
    monkeypatch: pytest.MonkeyPatch, family: str, parameter: int
) -> None:
    width = 2**parameter if family == "fermat" else parameter
    modulus = 2**width + (1 if family == "fermat" else -1)
    addend = 0 if family == "fermat" else -2
    transition = tuple((x * x + addend) % modulus for x in range(modulus))
    keys = tuple(_terminal_deck_key(family, x, modulus) for x in range(modulus))
    ids = _class_ids(keys)
    target = modulus - 1 if family == "fermat" else 0
    machine = quotient_machine_from_moore(
        transition, tuple(x == target for x in range(modulus)), ids
    )
    assert machine.classes == (modulus + 1) // 2

    # Build exact reference outputs before poisoning. This work is validation,
    # not hidden inside the jump evaluator or its measured composition count.
    expected: dict[int, tuple[int, ...]] = {}
    points = tuple(range(modulus))
    for duration in range(1, 1025):
        points = tuple(transition[x] for x in points)
        if duration & (duration - 1) == 0:
            expected[duration] = tuple(ids[x] for x in points)

    monkeypatch.setattr(ArithmeticTile, "step", _forbidden)
    monkeypatch.setattr(UnaryTransitionEffect, "apply", _forbidden)
    arena = UnaryPowerArena(machine.transition)
    action = arena.atom
    for level in range(11):
        duration = 2**level
        if level:
            action = arena.compose(action, action)
        assert arena.composition_operations == level
        assert action.effect.classes == machine.classes
        assert tuple(action.effect.transition[q] for q in ids) == expected[duration]
        assert len(action.effect.transition) == machine.classes
    # Each retained action is an extensional table, not a tree of N children.
    assert arena.node_count <= 12


@pytest.mark.parametrize("growth", (0, 1))
def test_supplied_primary_action_powers_without_birth_or_state_evaluation(
    monkeypatch: pytest.MonkeyPatch, growth: int
) -> None:
    atom = PrimaryJetAffineMorphism.reverse_add_event(
        (1, -3, 2), growth, degree=5, modulus=32
    )
    state: tuple[int, ...] = (1, 2, 3, 4, 5)
    references: dict[int, tuple[int, ...]] = {}
    output = state
    for duration in range(1, 1025):
        output = atom.apply(output)
        if duration & (duration - 1) == 0:
            references[duration] = output
    apply = PrimaryJetAffineMorphism.apply
    monkeypatch.setattr(PrimaryJetAffineMorphism, "reverse_add_event", _forbidden)
    monkeypatch.setattr(PrimaryJetAffineMorphism, "apply", _forbidden)
    for level in range(11):
        duration = 2**level
        action = atom.power(duration)
        # Shared general binary_power includes one identity composition.
        assert action.compositions == level + 1
        assert action.steps == duration
        assert len(action.kernel) == len(action.offset) == 5
        assert apply(action, state) == references[duration]


def test_any_nine_decimal_transport_events_kill_old_source_but_eight_need_not() -> None:
    atoms = tuple(
        PrimaryJetAffineMorphism.reverse_add_event((), growth, degree=5, modulus=32)
        for growth in (0, 1)
    )
    for itinerary in product((0, 1), repeat=9):
        action = PrimaryJetAffineMorphism.identity(5, 32)
        for growth in itinerary:
            action = action.then(atoms[growth])
        assert action.source_annihilated
    eight = atoms[0].power(4).then(atoms[1].power(4))
    assert eight.kernel == (0, 0, 0, 0, 16)
    assert not eight.source_annihilated


@pytest.mark.parametrize("family", ("fermat", "mersenne"))
def test_certified_order_clock_skips_huge_duration_without_giant_exponent(
    family: str,
) -> None:
    from number_compiler.arithmetic.fields.morphism_core import modular_power

    duration = 10**100 + 17
    modulus, value, order = (257, 3, 256) if family == "fermat" else (127, 2, 7)
    # A checked order annihilator is a premise, not an assumed primality fact.
    assert pow(value, order, modulus) == 1
    clock = modular_power(2, duration, order)
    assert clock.compositions <= 2 * duration.bit_length()
    forward = modular_power(value, clock.value, modulus).value
    if family == "fermat":
        assert forward == 1
    else:
        inverse = pow(value, -1, modulus)
        assert (value * inverse) % modulus == 1
        result = (
            forward + modular_power(inverse, clock.value, modulus).value
        ) % modulus
        # The order-seven unit has a three-step exponent-doubling orbit.
        assert pow(2, 3, order) == 1
        expected = (value + inverse) % modulus
        for _ in range(duration % 3):
            expected = (expected * expected - 2) % modulus
        assert result == expected

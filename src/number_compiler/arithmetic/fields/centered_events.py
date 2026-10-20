"""Carry-jump and centered-clock event arithmetic on shared arena handles.

Inputs are supplied exact arithmetic. A complete clock extractor must still
authenticate the reset, tail, growth and source predicate before publication.
"""

from __future__ import annotations

from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    apply_carry_fn,
    centered_carry_fn,
)
from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.fields.centered_carry import (
    carry_coboundary,
    validate_extent,
    validate_growth,
)
from number_compiler.arithmetic.fields.event_innovation import normalize_event_sum
from number_compiler.arithmetic.fields.radial_innovation import (
    InnovationID,
    RadialMultiplier,
)
from number_compiler.arithmetic.fields.symbolic_innovation import (
    SymbolicInnovationArena,
)
from number_compiler.resources.metric_keys import (
    arithmetic_fields as _fields_keys,
)


def _nonnegative(value: int) -> None:
    if type(value) is not int:
        raise TypeError("carry event coordinate must be an exact integer")
    if value < 0:
        raise ValueError("carry event coordinate must be nonnegative")


def neutral_carry_jump(
    arena: SymbolicInnovationArena, *, extent: int, incoming: int
) -> InnovationID:
    """J_ell(0,c) = -c z^ell, including ell=0; no interior events."""
    _nonnegative(extent)
    carry = apply_carry_fn(CarryFn.ID, incoming)
    arena.resolve(arena.zero)
    if not carry:
        return arena.zero
    end = arena.chart(arena.interval(1), CylinderChart(1, -extent))
    return arena.linear_combination(((-carry, end),))


def reset_carry_jump(
    arena: SymbolicInnovationArena,
    tail_jump: InnovationID,
    *,
    prefix: int,
    leading: int,
    incoming: int,
) -> InnovationID:
    """J = (b-c) z^h + z^(h+1) J_tail, using the canonical carry monoid.

    A reset to the already-present bit emits zero at h. Its tail and terminal
    boundary remain; equality of that one port cannot erase the whole effect.
    """
    _nonnegative(prefix)
    port = centered_carry_fn(leading)
    if port is CarryFn.ID:
        raise ValueError("first reset requires a nonzero leading coefficient")
    outgoing = apply_carry_fn(port, incoming)
    arena.resolve(tail_jump)
    tail = arena.chart(tail_jump, CylinderChart(1, -prefix - 1))
    if outgoing == incoming:
        return normalize_event_sum(arena, tail)
    reset = arena.chart(arena.interval(1), CylinderChart(1, -prefix))
    return normalize_event_sum(
        arena, arena.linear_combination(((outgoing - incoming, reset), (1, tail)))
    )


def clock_event_tail(
    arena: SymbolicInnovationArena,
    events: InnovationID,
    *,
    extent: int,
    prefix: int,
    leading: int,
) -> InnovationID:
    """Transport a supplied Delta=z^h(d+z Delta1) factorization to its event tail.

    H1 = z^(-h-1) H - d z^(-1) + d. Simply dropping H's leading event
    would lose the +d compensation and can change the next carry reset.
    This arithmetic identity does not certify the supplied h or d.
    """
    validate_extent(extent)
    _nonnegative(prefix)
    if prefix >= extent:
        raise ValueError("first reset must lie inside the active extent")
    if centered_carry_fn(leading) is CarryFn.ID:
        raise ValueError("first reset requires a nonzero leading coefficient")
    arena.resolve(events)
    shifted = arena.chart(events, CylinderChart(1, prefix + 1))
    one = arena.interval(1)
    previous = arena.chart(one, CylinderChart(1, 1))
    return normalize_event_sum(
        arena,
        arena.linear_combination(((1, shifted), (-leading, previous), (leading, one))),
    )


def advance_centered_events(
    arena: SymbolicInnovationArena,
    events: InnovationID,
    carry_events: InnovationID,
    *,
    extent: int,
    growth: int,
) -> InnovationID:
    """Construct H+ directly from H and C_Q, without integrating either field."""
    validate_extent(extent)
    validate_growth(growth)
    arena.resolve(events)
    arena.resolve(carry_events)
    correction = carry_coboundary(arena, carry_events, base=10)
    reflected = arena.chart(correction, CylinderChart(-1, extent + growth))
    radial = arena.radial(events, RadialMultiplier(1 - growth, growth))
    one = arena.interval(1)
    start = arena.chart(one, CylinderChart(1, -growth))
    end = arena.chart(one, CylinderChart(1, -extent))
    result = arena.linear_combination(
        ((1, radial), (1, correction), (-1, reflected), (9, start), (-9, end))
    )
    arena.ledger.bump(_fields_keys.CENTERED_EVENT_ADVANCE_ATTEMPTS)
    return normalize_event_sum(arena, result)

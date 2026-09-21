"""Carry-event consumer of exact common-growth signs; no source admission.

The extractor works on supplied arithmetic packets. This bridge uses the
production carry monoid and innovation arena, but does not authorize a future
source occurrence or complete a temporal constructor.
"""

from dataclasses import dataclass

from devtools.experiments.reverse_add.radial_sign_runs import (
    ShiftTerm,
    SignLimits,
    SignWork,
    isolate_common_growth_signs,
)
from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    apply_carry_fn,
    centered_carry_fn,
)
from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.fields.event_innovation import normalize_event_sum
from number_compiler.arithmetic.fields.symbolic_innovation import (
    InnovationID,
    SymbolicInnovationArena,
)


@dataclass(frozen=True, slots=True)
class RadialCarryEvents:
    """J=(1-z)Q-c, C_Q=(1-z)Q, and terminal carry, with no source authority."""

    jump: InnovationID
    coboundary: InnovationID
    terminal: int
    sign_intervals: int


def common_growth_carry_events(
    arena: SymbolicInnovationArena,
    row: int,
    terms: tuple[ShiftTerm, ...],
    *,
    extent: int,
    incoming: int,
    work: SignWork,
    limits: SignLimits | None = None,
) -> RadialCarryEvents:
    """Derive carry events from sign intervals, never a coefficient/carry word."""
    if type(extent) is not int or extent < 0:
        raise ValueError("carry extent must be a nonnegative exact integer")
    carry = apply_carry_fn(CarryFn.ID, incoming)
    arena.resolve(arena.zero)
    runs = isolate_common_growth_signs(row, terms, 0, extent, work=work, limits=limits)
    terms_out: list[tuple[int, InnovationID]] = []
    one = arena.interval(1)
    for run in runs:
        arena.ledger.bump("radial_sign_carry_intervals")
        next_carry = apply_carry_fn(centered_carry_fn(run.sign), carry)
        if next_carry != carry:
            marker = arena.chart(one, CylinderChart(1, -run.start))
            terms_out.append((next_carry - carry, marker))
        carry = next_carry
    if carry:
        terms_out.append((-carry, arena.chart(one, CylinderChart(1, -extent))))
    jump = normalize_event_sum(arena, arena.linear_combination(tuple(terms_out)))
    coboundary = normalize_event_sum(
        arena, arena.linear_combination(((1, jump), (incoming, one)))
    )
    return RadialCarryEvents(jump, coboundary, carry, len(runs))

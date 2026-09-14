"""Bounded differential audit of the decimal carry/primary-jet cylinder.

The cylinder is a phase-neutral two-port operator. This audit deliberately
keeps the current primary-jet value outside its identity: applying an operator
to a trajectory value is a measurement, not an interning key.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.carry.carry_monoid import scan_carry_automaton
from number_compiler.arithmetic.carry.decimal_jet_cylinder import (
    DecimalCarryJetBlock,
)
from number_compiler.arithmetic.carry.event_memory import (
    carry_field,
    forcing_event,
    forcing_event_from_carry,
    pair_step,
)
from number_compiler.arithmetic.fields.radix import reverse_pair_sums
from number_compiler.arithmetic.polynomials.primary_jet import (
    PrimaryJetAffineMorphism,
    primary_jet_from_digits,
)


@dataclass(frozen=True, slots=True)
class DecimalClockCylinderAudit:
    seeds: int
    transitions: int
    source_positions: int
    events: int
    spatial_compositions: int
    leaf_cylinder_classes: int
    evaluated_source_death_max: int
    neutral_kernel_death_max: int


def _jet(values: tuple[int, ...]) -> tuple[int, ...]:
    return primary_jet_from_digits(values, degree=5, modulus=32).jet


def _assert_spatial_views(pair: tuple[int, ...], carry: tuple[int, ...]) -> None:
    """Check every emitted boundary while composing the neutral cylinder."""
    block = DecimalCarryJetBlock.identity()
    port_carries = tuple(
        scan_carry_automaton(pair, incoming=port).boundaries for port in (0, 1)
    )
    assert port_carries[0] == carry
    for index, symbol in enumerate(pair):
        block = block.then(DecimalCarryJetBlock.digit(symbol))
        for port in (0, 1):
            assert block.cylinder.rows[port].outgoing == port_carries[port][index + 1]
    for port in (0, 1):
        assert block.cylinder.rows[port].jet == _jet(port_carries[port][:-1])
        assert block.following_jet(port) == _jet(port_carries[port][1:])
    assert block.forcing_jet() == _jet(forcing_event_from_carry(carry))


def audit_decimal_clock_cylinder(
    *, first_seed: int = 176, last_seed: int = 216, steps: int = 96
) -> DecimalClockCylinderAudit:
    """Run the documented broad finite audit with independently exact values."""
    if first_seed > last_seed or steps <= 0:
        raise ValueError((first_seed, last_seed, steps))
    source_positions = spatial_compositions = events = 0
    evaluated_deaths: list[int] = []
    neutral_deaths: list[int] = []
    for seed in range(first_seed, last_seed + 1):
        pair = reverse_pair_sums(seed, 10)
        initial_jet = _jet(pair)
        action = PrimaryJetAffineMorphism.identity(5, 32)
        evaluated_death: int | None = None
        neutral_death: int | None = None
        for step in range(1, steps + 1):
            carry = carry_field(pair, base=10)
            target, growth = pair_step(pair, 10)
            event = forcing_event(pair, target, growth)
            assert event == forcing_event_from_carry(carry)
            _assert_spatial_views(pair, carry)

            primitive = PrimaryJetAffineMorphism.reverse_add_event(
                event, growth, degree=5, modulus=32
            )
            assert primitive.apply(_jet(pair)) == _jet(target)
            action = action.then(primitive)
            evaluated = action.apply(initial_jet)
            zero_evaluated = action.apply((0,) * 5)
            if evaluated_death is None and evaluated == zero_evaluated:
                evaluated_death = step
            if neutral_death is None and action.source_annihilated:
                neutral_death = step

            source_positions += len(pair)
            spatial_compositions += len(pair) - 1
            events += 1
            pair = target
        if evaluated_death is None or neutral_death is None:
            raise AssertionError((seed, evaluated_death, neutral_death))
        evaluated_deaths.append(evaluated_death)
        neutral_deaths.append(neutral_death)

    leaf_classes = len(
        {DecimalCarryJetBlock.digit(symbol).cylinder for symbol in range(19)}
    )
    return DecimalClockCylinderAudit(
        seeds=last_seed - first_seed + 1,
        transitions=(last_seed - first_seed + 1) * steps,
        source_positions=source_positions,
        events=events,
        spatial_compositions=spatial_compositions,
        leaf_cylinder_classes=leaf_classes,
        evaluated_source_death_max=max(evaluated_deaths),
        neutral_kernel_death_max=max(neutral_deaths),
    )


def audit_seed_196_births(*, steps: int = 4096) -> None:
    """Check the carry-owned event formula on the long named control orbit."""
    if steps <= 0:
        raise ValueError(steps)
    pair = reverse_pair_sums(196, 10)
    for _ in range(steps):
        carry = carry_field(pair, base=10)
        target, growth = pair_step(pair, 10)
        assert forcing_event(pair, target, growth) == forcing_event_from_carry(carry)
        pair = target


__all__ = [
    "DecimalClockCylinderAudit",
    "audit_decimal_clock_cylinder",
    "audit_seed_196_births",
]

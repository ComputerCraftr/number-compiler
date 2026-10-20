"""Full guarded-word identities for finite reverse/add border occurrences."""

from collections.abc import Callable
from dataclasses import replace
from typing import cast

from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.contracts.family_identity import FamilyId
from number_compiler.hashlife.interfaces.border_macros import (
    BorderMacroIdentity,
    BorderMacroKind,
    BorderMacroPhase,
    BorderSourceCursor,
)
from number_compiler.sequences.reverse_add import border_occurrences as occurrence_owner
from number_compiler.sequences.reverse_add.border_carry_safety import (
    BilateralCyclePort,
    BorderTile,
    enumerate_one_digit_cycles,
)
from number_compiler.sequences.reverse_add.border_occurrences import (
    ReverseAddBorderOccurrence,
    ReverseAddBorderPhaseOccurrence,
    ReverseAddPortSignature,
    ReverseAddWordSignature,
)
from tests.support.private_attributes import private_test_attribute

edge_signature = cast(
    Callable[[BilateralCyclePort], ReverseAddPortSignature],
    private_test_attribute(occurrence_owner, "_edge_signature"),
)
canonical_edge_cycle = cast(
    Callable[
        [tuple[ReverseAddPortSignature, ...]],
        tuple[tuple[ReverseAddPortSignature, ...], int],
    ],
    private_test_attribute(occurrence_owner, "_canonical_edge_cycle"),
)
find_returns = cast(
    Callable[
        [tuple[ReverseAddBorderPhaseOccurrence | None, ...]],
        tuple[ReverseAddBorderOccurrence, ...],
    ],
    private_test_attribute(occurrence_owner, "_find_returns"),
)


def _clocked_cycle(
    ports: tuple[BilateralCyclePort, ...],
) -> tuple[ReverseAddBorderPhaseOccurrence, ...]:
    owner = object()
    phases: list[ReverseAddBorderPhaseOccurrence] = []
    width = 5
    for tick, port in enumerate(ports):
        source = BorderSourceCursor(
            FamilyId.REVERSE_ADD, owner, tick, tick, 1, width % 2
        )
        target = BorderSourceCursor(
            FamilyId.REVERSE_ADD,
            owner,
            tick + 1,
            tick + 1,
            1,
            (width + port.growth) % 2,
        )
        phase = BorderMacroPhase(
            BorderMacroIdentity(
                FamilyId.REVERSE_ADD,
                BorderMacroKind.EDGE,
                ReverseAddWordSignature(port.source.k, (edge_signature(port),)),
            ),
            tick,
            source,
            target,
            (port.source.k, port.source.high, port.source.low),
            (port.target.k, port.target.high, port.target.low),
            width,
            width + port.growth,
            (0, 0),
            (0, 0),
        )
        phases.append(ReverseAddBorderPhaseOccurrence(phase, port))
        width += port.growth
    return tuple(phases)


def test_cycle_identity_is_rotation_invariant_and_carries_entry_phase() -> None:
    cycle = next(cycle for cycle in enumerate_one_digit_cycles() if cycle.steps >= 2)
    ports = cycle.bilateral_ports()
    base = next(
        macro
        for macro in find_returns(_clocked_cycle(ports))
        if macro.start == 0 and macro.end == len(ports)
    )

    for offset in range(1, len(ports)):
        rotated = ports[offset:] + ports[:offset]
        macro = next(
            item
            for item in find_returns(_clocked_cycle(rotated))
            if item.start == 0 and item.end == len(ports)
        )
        assert macro.identity == base.identity
        assert macro.entry_phase == (base.entry_phase + offset) % len(ports)

    guarded_change = (replace(ports[0], low_carry=1 - ports[0].low_carry),) + ports[1:]
    changed = next(
        macro
        for macro in find_returns(_clocked_cycle(guarded_change))
        if macro.start == 0 and macro.end == len(ports)
    )
    assert changed.identity != base.identity


def test_canonical_guard_word_preserves_repeated_states_and_guard_distinctions() -> (
    None
):
    source = BorderTile(1, 1, 7)
    target = BorderTile(1, 9, 8)
    return_state = BorderTile(1, 9, 8)
    returned = BorderTile(1, 1, 7)
    first = ReverseAddPortSignature(
        source=source,
        target=target,
        growth=0,
        low_carry=0,
        admitted_middle=(CarryFn.CONST0,),
    )
    second = ReverseAddPortSignature(
        source,
        target,
        0,
        1,
        (CarryFn.CONST1,),
    )
    third = ReverseAddPortSignature(
        return_state,
        returned,
        1,
        1,
        (CarryFn.ID,),
    )
    word = (first, second, third)
    canonical, _offset = canonical_edge_cycle(word)
    for offset in range(len(word)):
        rotated, _rotation = canonical_edge_cycle(word[offset:] + word[:offset])
        assert rotated == canonical

    changed_guard = (
        first,
        ReverseAddPortSignature(
            source,
            target,
            0,
            1,
            (CarryFn.CONST0,),
        ),
        third,
    )
    changed, _changed_offset = canonical_edge_cycle(changed_guard)
    assert changed != canonical

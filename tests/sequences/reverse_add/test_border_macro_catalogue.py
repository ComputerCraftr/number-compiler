"""Full guarded-word identities for finite reverse/add border catalogues."""

from dataclasses import replace

from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.hashlife.interfaces.border_macros import (
    BorderFamilyId,
    BorderMacroIdentity,
    BorderMacroKind,
    BorderMacroPhase,
    BorderSourceCursor,
)
from number_compiler.sequences.reverse_add.border_carry_safety import (
    BilateralCyclePort,
    enumerate_one_digit_cycles,
)
from number_compiler.sequences.reverse_add.border_macro_catalogue import (
    ClockedBorderPhase,
    _canonical_edge_cycle,
    _edge_signature,
    _find_returns,
)


def _clocked_cycle(
    ports: tuple[BilateralCyclePort, ...],
) -> tuple[ClockedBorderPhase, ...]:
    owner = object()
    phases: list[ClockedBorderPhase] = []
    width = 5
    for tick, port in enumerate(ports):
        source = BorderSourceCursor(
            BorderFamilyId.REVERSE_ADD, owner, tick, tick, 1, width % 2
        )
        target = BorderSourceCursor(
            BorderFamilyId.REVERSE_ADD,
            owner,
            tick + 1,
            tick + 1,
            1,
            (width + port.growth) % 2,
        )
        phase = BorderMacroPhase(
            BorderMacroIdentity(
                BorderFamilyId.REVERSE_ADD,
                BorderMacroKind.EDGE,
                _edge_signature(port),
            ),
            tick,
            source,
            target,
            (port.source.k, port.source.high, port.source.low),
            (port.target.k, port.target.high, port.target.low),
            width,
            width + port.growth,
        )
        phases.append(ClockedBorderPhase(phase, tick, width, port, 0, 0, 0, 0))
        width += port.growth
    return tuple(phases)


def test_cycle_identity_is_rotation_invariant_and_carries_entry_phase() -> None:
    cycle = next(cycle for cycle in enumerate_one_digit_cycles() if cycle.steps >= 2)
    ports = cycle.bilateral_ports()
    base = next(
        macro
        for macro in _find_returns(_clocked_cycle(ports))
        if macro.start == 0 and macro.end == len(ports)
    )

    for offset in range(1, len(ports)):
        rotated = ports[offset:] + ports[:offset]
        macro = next(
            item
            for item in _find_returns(_clocked_cycle(rotated))
            if item.start == 0 and item.end == len(ports)
        )
        assert macro.identity == base.identity
        assert macro.entry_phase == (base.entry_phase + offset) % len(ports)

    guarded_change = (replace(ports[0], low_carry=1 - ports[0].low_carry),) + ports[1:]
    changed = next(
        macro
        for macro in _find_returns(_clocked_cycle(guarded_change))
        if macro.start == 0 and macro.end == len(ports)
    )
    assert changed.identity != base.identity


def test_canonical_guard_word_preserves_repeated_states_and_guard_distinctions() -> (
    None
):
    first: tuple[
        int, tuple[int, int, int], tuple[int, int, int], int, int, tuple[str, ...]
    ] = (
        1,
        (1, 1, 7),
        (1, 9, 8),
        0,
        0,
        (CarryFn.CONST0.value,),
    )
    second = (1, (1, 1, 7), (1, 9, 8), 0, 1, (CarryFn.CONST1.value,))
    third = (1, (1, 9, 8), (1, 1, 7), 1, 1, (CarryFn.ID.value,))
    word = (first, second, third)
    canonical, _offset = _canonical_edge_cycle(word)
    for offset in range(len(word)):
        rotated, _rotation = _canonical_edge_cycle(word[offset:] + word[:offset])
        assert rotated == canonical

    changed_guard = (
        first,
        (1, (1, 1, 7), (1, 9, 8), 0, 1, (CarryFn.CONST0.value,)),
        third,
    )
    changed, _changed_offset = _canonical_edge_cycle(changed_guard)
    assert changed != canonical

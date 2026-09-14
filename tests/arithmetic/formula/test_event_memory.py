from __future__ import annotations

import random
from collections.abc import Sequence
from typing import TYPE_CHECKING

from number_compiler.arithmetic.carry.event_memory import (
    carry_field,
    endpoint_width_from_event_window,
    event_memory_horizon,
    forcing_event,
    forcing_event_from_carry,
    growths_from_event_widths,
    next_carry_from_window,
    next_event_from_window,
    pair_step,
    reconstruct_pair_from_carry_window,
    reconstruct_pair_from_event_window,
)
from number_compiler.arithmetic.formula.event_formula import carry_event_formula_view
from number_compiler.arithmetic.formula.formula import FormulaArena, root_from_values
from number_compiler.arithmetic.formula.summary import (
    register_summary,
    summary_from_values,
)
from number_compiler.arithmetic.formula.types import RadixSpec

if TYPE_CHECKING:
    from number_compiler.arithmetic.formula.event_formula import CarryEventFormulaView


def _materialize_event_sets(
    arena: FormulaArena,
    view: CarryEventFormulaView,
) -> tuple[int, ...]:
    out = []
    for i in range(view.target_width):
        hits = [
            value for value, mask in view.event_sets if arena.eval_closed_bit(mask, i)
        ]
        assert len(hits) == 1, (i, hits)
        out.append(hits[0])
    return tuple(out)


def _orbit(
    seed_pair: Sequence[int], base: int, steps: int
) -> tuple[list[tuple[int, ...]], list[tuple[int, ...]], list[tuple[int, ...]]]:
    source = tuple(seed_pair)
    states = [source]
    carries = []
    events = []
    for _ in range(steps):
        carry = carry_field(source, base=base)
        target, growth = pair_step(source, base)
        event = forcing_event(source, target, growth)
        assert event == forcing_event_from_carry(carry, base=base)
        carries.append(carry)
        events.append(event)
        source = target
        states.append(source)
    return states, carries, events


def test_event_position_sets_are_exact_derived_formula_views() -> None:
    rng = random.Random(0xE71E196)
    for base in range(3, 17):
        spec = RadixSpec(base)
        for _ in range(30):
            width = rng.randrange(1, 10)
            half = [
                rng.randrange(0, 2 * (base - 1) + 1) for _ in range((width + 1) // 2)
            ]
            source = tuple(
                half[i] if i < len(half) else half[width - 1 - i] for i in range(width)
            )
            # Ensure symmetry construction for the second half explicitly.
            source = tuple(
                source[i] if i < (width + 1) // 2 else source[width - 1 - i]
                for i in range(width)
            )
            target, growth = pair_step(source, base)
            carry = carry_field(source, base=base)
            expected = forcing_event(source, target, growth)
            arena = FormulaArena()
            root = root_from_values(source, arena, spec)
            register_summary(arena, root, spec, summary_from_values(source, spec))
            view = carry_event_formula_view(arena, root, spec, growth=growth)
            assert view.target_width == len(expected)
            assert _materialize_event_sets(arena, view) == expected
            assert (
                tuple(
                    arena.eval_closed_bit(view.carry_out, i) for i in range(root.width)
                )
                == carry[1:]
            )
            # X_v remains a derived partition, not a semantic state copy.
            for i, value in enumerate(source):
                assert (
                    sum(arena.eval_closed_bit(mask, i) for mask in view.value_sets) == 1
                )
                assert arena.eval_closed_bit(view.value_sets[value], i) == 1


def test_decimal_196_pair_and_length_are_exactly_last_20_events() -> None:
    H = event_memory_horizon(10)
    assert H == 20
    states, carries, events = _orbit((7, 18, 7), 10, H + 120)
    for t in range(H, len(states)):
        window = events[t - H : t]
        assert reconstruct_pair_from_event_window(window, base=10) == states[t]
        assert endpoint_width_from_event_window(window) == len(states[t])
        assert growths_from_event_widths(window) == tuple(
            len(events[j + 1]) - len(events[j]) for j in range(t - H, t - 1)
        )
        carry_window = carries[t - H : t]
        assert reconstruct_pair_from_carry_window(carry_window, base=10) == states[t]
        if t < len(events):
            assert next_event_from_window(window, base=10) == events[t]
            assert next_carry_from_window(carry_window, base=10) == carries[t]


def test_bounded_carry_memory_generalizes_random_bases() -> None:
    rng = random.Random(0xC411196)
    for base in range(3, 17):
        H = event_memory_horizon(base)
        for _ in range(3):
            width = rng.randrange(1, 7)
            half = [
                rng.randrange(0, 2 * (base - 1) + 1) for _ in range((width + 1) // 2)
            ]
            source = tuple(
                half[i] if i < (width + 1) // 2 else half[width - 1 - i]
                for i in range(width)
            )
            states, carries, events = _orbit(source, base, H + 10)
            for t in range(H, H + 10):
                assert (
                    reconstruct_pair_from_event_window(events[t - H : t], base=base)
                    == states[t]
                )
                assert (
                    reconstruct_pair_from_carry_window(carries[t - H : t], base=base)
                    == states[t]
                )


def test_event_formula_synthesis_is_forbidden_inside_powered_jump() -> None:
    import pytest

    from number_compiler.arithmetic.automata.guard import (
        JumpAudit,
        JumpGuardViolation,
        powered_jump_scope,
    )

    spec = RadixSpec(10)
    arena = FormulaArena()
    source = (7, 18, 7)
    root = root_from_values(source, arena, spec)
    audit = JumpAudit()
    with powered_jump_scope(audit), pytest.raises(JumpGuardViolation):
        carry_event_formula_view(arena, root, spec, growth=1)
    assert audit.forbidden_attempts["carry_event_formula"] == 1


def test_event_views_do_not_expand_semantic_formula_root_state() -> None:
    from number_compiler.arithmetic.formula.formula import FormulaRoot

    assert tuple(FormulaRoot.__dataclass_fields__) == ("planes",)

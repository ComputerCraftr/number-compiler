"""Explicit event/germ endpoint projection through the exact proof engine."""

from __future__ import annotations

from typing import TypeGuard

from number_compiler.arithmetic.automata.program_word import CanonicalWord
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.sequences.collatz.frame import (
    CollatzAffineSuffixEventProjection,
    CollatzAffineSuffixGerm,
)
from number_compiler.sequences.collatz.germ_cache import CollatzGermTransitionCache
from number_compiler.sequences.collatz.power import CollatzEventArena


def _is_event_arena(value: object) -> TypeGuard[CollatzEventArena]:
    return isinstance(value, CollatzEventArena)


def _is_transition_cache(value: object) -> TypeGuard[CollatzGermTransitionCache]:
    return isinstance(value, CollatzGermTransitionCache)


def collatz_affine_suffix_event_power_word(
    word: CanonicalWord,
    steps: int,
    *,
    arena: CollatzEventArena | None = None,
    transition_cache: CollatzGermTransitionCache | None = None,
) -> CollatzAffineSuffixEventProjection:
    """Feed root-germ valuations straight into the lazy event morphism arena.

    The generator is consumed synchronously by ``CollatzEventArena``.  No
    valuation tuple, parity word, E/O program, dyadic domain residue, or eager
    multi-event affine offset is constructed.
    """
    from number_compiler.sequences.collatz.germ_cache import CollatzGermTransitionCache
    from number_compiler.sequences.collatz.power import CollatzEventArena

    if type(steps) is not int:
        raise TypeError("Collatz event count must be an exact integer")
    if steps < 0:
        raise ValueError(steps)
    if arena is None:
        arena = CollatzEventArena()
    if not _is_event_arena(arena):
        raise TypeError(type(arena))
    germ = CollatzAffineSuffixGerm.from_word(word)
    if transition_cache is None:
        transition_cache = CollatzGermTransitionCache()
    if not _is_transition_cache(transition_cache):
        raise TypeError(type(transition_cache))
    before = arena.composition_operations
    powered = transition_cache.advance_event_power(germ, steps, arena=arena)
    root = powered.root
    germ = powered.target
    return CollatzAffineSuffixEventProjection(
        root,
        germ,
        steps,
        arena.composition_operations - before,
    )


def collatz_affine_suffix_event_power_value(
    value: int,
    steps: int,
    *,
    arena: CollatzEventArena | None = None,
    transition_cache: CollatzGermTransitionCache | None = None,
) -> CollatzAffineSuffixEventProjection:
    """Power a concrete odd source through the canonical radix-field engine.

    The concrete-value path no longer discovers events by repeatedly advancing
    whole affine suffix germs.  A caller that explicitly supplies a legacy
    ``transition_cache`` retains the symbolic-germ compatibility path; otherwise
    finite directed carry cells + structural normalization produce the event DAG.
    """
    from number_compiler.arithmetic.automata.program_word import from_values

    if type(value) is not int or type(steps) is not int:
        raise TypeError("Collatz value and event count require exact integers")
    if value <= 0 or not (value & 1) or steps < 0:
        raise ValueError((value, steps))
    if transition_cache is not None:
        return collatz_affine_suffix_event_power_word(
            from_values(digits_lsd(value, 4)),
            steps,
            arena=arena,
            transition_cache=transition_cache,
        )

    from devtools.verification.collatz_spacetime import (
        CollatzCausalSpacetimeEngine,
        CollatzRadixField,
    )
    from number_compiler.sequences.collatz.power import CollatzEventArena

    if arena is None:
        arena = CollatzEventArena()
    if not _is_event_arena(arena):
        raise TypeError(type(arena))
    before = arena.composition_operations
    engine = CollatzCausalSpacetimeEngine(event_arena=arena)
    target_field, root = engine.advance_event_power(
        CollatzRadixField.from_value(value), steps
    )
    target_word = from_values(target_field.digits())
    target = CollatzAffineSuffixGerm.from_word(target_word)
    target = CollatzAffineSuffixGerm(
        target.multiplier,
        target.offset,
        target.suffix,
        steps,
    )
    return CollatzAffineSuffixEventProjection(
        root,
        target,
        steps,
        arena.composition_operations - before,
    )

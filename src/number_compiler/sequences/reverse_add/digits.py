"""Exact output-digit formulas for arbitrary reverse-and-add orbits.

For a pair coefficient word ``s_i`` in radix ``b`` and incoming carry
``L_i`` (with ``L_0=0``), the next decimal/radix digit is exactly

    y_i = (s_i + L_i) mod b,

while ``L_(i+1)=floor((s_i+L_i)/b)``.  The pair FormulaRoot and the parallel
carry monoid therefore determine every next output digit symbolically at its
exact position.  No seed-196 assumption appears here.
"""

from __future__ import annotations

from number_compiler.arithmetic.contracts.input_validation import (
    normalized_integer_pair,
)
from number_compiler.arithmetic.fields.digit_formula import (
    DigitSpec,
    digit_root_from_values,
)
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.arithmetic.formula.derived import carry_out, successor
from number_compiler.arithmetic.formula.formula import (
    FormulaArena,
    FormulaRoot,
    canonical_root_key,
    root_from_values,
)
from number_compiler.arithmetic.formula.types import Expr, RadixSpec


def _pair_value_masks(
    arena: FormulaArena, root: FormulaRoot, spec: RadixSpec
) -> tuple[Expr, ...]:
    if root.plane_count != spec.plane_count:
        raise ValueError((root.plane_count, spec.plane_count))
    key = ("pair-value-masks", spec.base, canonical_root_key(root, arena))
    cached = arena.metadata_get(key)
    if isinstance(cached, tuple) and len(cached) == spec.pair_max + 1:
        return cached
    masks = tuple(
        arena.predicate("EQ", s, root.planes) for s in range(spec.pair_max + 1)
    )
    arena.metadata_set(key, masks)
    return masks


def next_digit_formula(
    arena: FormulaArena, pair_root: FormulaRoot, spec: RadixSpec
) -> FormulaRoot:
    """Return exact positional digit formulas for the reverse-add result.

    The returned width includes the terminal carry if one exists.  Determining
    that one boundary bit is a closed formula query, not a materialized carry
    vector.
    """
    b = spec.base
    dspec = DigitSpec(b)
    cache_key = ("next-digit-formula", b, canonical_root_key(pair_root, arena))
    cached = arena.metadata_get(cache_key)
    if isinstance(cached, FormulaRoot):
        return cached
    # Width growth is the first non-neutral boundary phase of the symmetric
    # pair field.  It is already carried by BlockSummary, so do not evaluate
    # the far-edge carry merely to decide whether an output digit is appended.
    from number_compiler.arithmetic.formula.summary import (
        get_summary,
        synthesize_symmetric_summary,
    )

    summary = get_summary(arena, pair_root, spec)
    if summary is None:
        summary = synthesize_symmetric_summary(arena, pair_root, spec)
    growth = summary.growth_from_outer_symmetry

    carry = carry_out(arena, pair_root, spec)  # L_(i+1), needed by digits
    incoming = arena.shl(carry, 1)  # L_i, L_0=0
    pmasks = _pair_value_masks(arena, pair_root, spec)
    width = pair_root.width

    digit_masks: list[list[Expr]] = [[] for _ in range(b)]
    not_in = arena.not_(incoming)
    for s, smask in enumerate(pmasks):
        digit_masks[s % b].append(arena.and_(smask, not_in))
        digit_masks[(s + 1) % b].append(arena.and_(smask, incoming))
    values = tuple(arena.or_many(xs, width) for xs in digit_masks)
    planes = tuple(
        arena.or_many((values[v] for v in range(b) if (v >> bit) & 1), width)
        for bit in range(dspec.plane_count)
    )
    root = FormulaRoot(planes)

    if not growth:
        arena.metadata_set(cache_key, root)
        return root

    # Append terminal digit 1 using one symbolic zero-extension + final range bit.
    out_width = width + 1
    edge = arena.range_mask(width, out_width, out_width)
    out = []
    for bit, plane in enumerate(root.planes):
        p = arena.resize(plane, out_width)
        if bit == 0:
            p = arena.or_(p, edge)
        out.append(p)
    result = FormulaRoot(tuple(out))
    arena.metadata_set(cache_key, result)
    return result


def pair_root_from_integer(
    value: int, arena: FormulaArena, spec: RadixSpec
) -> FormulaRoot:
    digits = digits_lsd(value, spec.base)
    pair = tuple(digits[i] + digits[-1 - i] for i in range(len(digits)))
    return root_from_values(pair, arena, spec)


def reverse_add_nth_digit(
    seed: int, index: int, position: int, *, base: int = 10
) -> int:
    """Project one digit through the exact binary-powered temporal operator.

    No ordinary successor loop is executed.  ``T**(index-1)`` is retained as a
    logarithmic operator DAG and composed directly with the finite digit/carry
    terminal; only the requested final symbol is emitted.  Higher-order
    residual-state growth is reported by :mod:`reverse_power` rather than being
    hidden as a logarithmic claim.
    """
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

    return ReverseAddPoweredTerm(int(seed), int(index), base=int(base)).digit(
        int(position)
    )


def reverse_add_nth_formula(
    seed: int, index: int, *, base: int = 10
) -> tuple[FormulaArena, FormulaRoot]:
    """Build only the requested reverse-add digit word.

    Unlike :func:`reverse_add_orbit_formulas`, this projection does not retain
    every intermediate digit root and does not construct the pair successor
    *after* the requested term.  The latter was pure eager work in the public
    nth/digit API.
    """
    seed, index = normalized_integer_pair(seed, index)
    spec = RadixSpec(base)
    dspec = DigitSpec(base)
    arena = FormulaArena()
    digits = digit_root_from_values(digits_lsd(seed, base), arena, dspec)
    if index == 0:
        return arena, digits
    pair = pair_root_from_integer(seed, arena, spec)
    for step in range(index):
        digits = next_digit_formula(arena, pair, spec)
        if step + 1 < index:
            pair = successor(arena, pair, spec)
    return arena, digits


def reverse_add_orbit_formulas(
    seed: int, steps: int, *, base: int = 10
) -> tuple[FormulaArena, tuple[FormulaRoot, ...], tuple[FormulaRoot, ...]]:
    """Generate exact closed digit formulas for a concrete reverse-add orbit.

    Returns ``(arena, digit_roots, pair_roots)``.  ``digit_roots[0]`` is the
    literal seed.  For k>=0, ``pair_roots[k]`` is the exact pair field of
    ``digit_roots[k]`` and ``digit_roots[k+1]`` is derived from it by the exact
    digit normalization formula above.
    """
    seed, steps = normalized_integer_pair(seed, steps)
    spec = RadixSpec(base)
    dspec = DigitSpec(base)
    arena = FormulaArena()
    seed_digits = digits_lsd(seed, base)
    digit_roots = [digit_root_from_values(seed_digits, arena, dspec)]
    pair_roots = [pair_root_from_integer(seed, arena, spec)]
    for _ in range(steps):
        source = pair_roots[-1]
        digit_roots.append(next_digit_formula(arena, source, spec))
        pair_roots.append(successor(arena, source, spec))
    return arena, tuple(digit_roots), tuple(pair_roots)


__all__ = [
    "digits_lsd",
    "next_digit_formula",
    "pair_root_from_integer",
    "reverse_add_nth_digit",
    "reverse_add_nth_formula",
    "reverse_add_orbit_formulas",
]

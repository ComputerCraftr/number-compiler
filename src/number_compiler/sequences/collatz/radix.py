"""Alternative exact radix realizations of the concrete Collatz orbit.

Binary makes the even branch a literal right shift.  Ternary makes the odd
branch ``3*n+1`` a literal radix shift plus LSD 1, while parity/even division is
one two-state long-division scan.  This module measures that dual coordinate
instead of assuming binary is globally optimal.
"""

from __future__ import annotations

from number_compiler.arithmetic.fields.digit_formula import (
    CompiledDigitTransduction,
    DigitSpec,
    closed_digit_at,
    digit_root_from_value_masks,
    digit_value_masks,
    divide_formula,
    trim_closed_root,
)
from number_compiler.arithmetic.formula.formula import FormulaArena, FormulaRoot
from number_compiler.arithmetic.formula.types import Expr
from number_compiler.sequences.collatz.orbit import CollatzStep

TERNARY = DigitSpec(3)
SENARY = DigitSpec(6)
DUODECIMAL = DigitSpec(12)


def ternary_multiply3_add1(arena: FormulaArena, root: FormulaRoot) -> FormulaRoot:
    """Exact ``3*n+1`` in base 3 as a structural digit shift, with no carry scan."""
    if root.plane_count != TERNARY.plane_count:
        raise ValueError((root.plane_count, TERNARY.plane_count))
    width = root.width + 1
    shifted = tuple(arena.shl(arena.resize(p, width), 1) for p in root.planes)
    one = arena.range_mask(0, 1, width)
    return FormulaRoot((arena.or_(shifted[0], one), shifted[1]))


def collatz_successor_formula_ternary(
    arena: FormulaArena,
    root: FormulaRoot,
) -> tuple[FormulaRoot, str, CompiledDigitTransduction]:
    """Exact original Collatz step in ternary.

    Long division by two is compiled once.  Its final remainder is the parity
    predicate and, on the even branch, its quotient is already the successor.
    On the odd branch the quotient is discarded and ``3*n+1`` is the structural
    ternary shift above.
    """
    quotient, compiled = divide_formula(arena, root, TERNARY, 2, require_exact=False)
    if compiled.final_state(arena) == 0:
        return quotient, "divide_2", compiled
    return ternary_multiply3_add1(arena, root), "multiply_3_add_1_radix_shift", compiled


def local_divide2_even_radix(
    arena: FormulaArena,
    root: FormulaRoot,
    spec: DigitSpec,
) -> tuple[FormulaRoot, int]:
    """Exact division by two in an even radix using only adjacent digits.

    For ``b`` even and LSF digits ``d_i``, the quotient digit is
    ``floor(d_i/2) + (b/2)*(d_{i+1} mod 2)``.  There is therefore no prefix
    remainder scan; the MSD-to-LSD remainder is simply the parity of the next
    more-significant digit.
    """
    if spec.base % 2:
        raise ValueError("local divide-by-two requires an even radix")
    if root.plane_count != spec.plane_count:
        raise ValueError((root.plane_count, spec.plane_count))
    masks = digit_value_masks(arena, root, spec)
    odd = arena.or_many((masks[d] for d in range(1, spec.base, 2)), root.width)
    higher_odd = arena.shr(odd, 1)
    higher_even = arena.not_(higher_odd)
    out_masks: list[list[Expr]] = [[] for _ in range(spec.base)]
    half = spec.base // 2
    for d in range(spec.base):
        lo = d // 2
        out_masks[lo].append(arena.and_(masks[d], higher_even))
        out_masks[lo + half].append(arena.and_(masks[d], higher_odd))
    values = tuple(arena.or_many(group, root.width) for group in out_masks)
    quotient = trim_closed_root(arena, digit_root_from_value_masks(arena, values, spec))
    remainder = closed_digit_at(arena, root, 0) & 1
    return quotient, remainder


def local_multiply3_add1_radix_multiple3(
    arena: FormulaArena,
    root: FormulaRoot,
    spec: DigitSpec,
) -> FormulaRoot:
    """Exact ``3*n+1`` when the radix is divisible by three, without a scan.

    Write ``d=(b/3)q+r``.  For the reachable carry ``c in {0,1,2}``,
    ``3d+c=bq+(3r+c)`` and ``3r+c < b``.  Thus the outgoing carry is exactly
    ``q`` and is independent of the incoming carry.  Each output digit depends
    only on the current digit and its immediate lower neighbour (plus the LSD
    initializer ``c_0=1``).
    """
    if spec.base % 3:
        raise ValueError("local multiply-by-three requires radix divisible by three")
    if root.plane_count != spec.plane_count:
        raise ValueError((root.plane_count, spec.plane_count))
    width = root.width + 1
    padded = FormulaRoot(tuple(arena.resize(p, width) for p in root.planes))
    masks = digit_value_masks(arena, padded, spec)
    chunk = spec.base // 3
    carry_class = []
    for q in range(3):
        carry_class.append(
            arena.or_many((masks[d] for d in range(q * chunk, (q + 1) * chunk)), width)
        )
    first = arena.range_mask(0, 1, width)
    incoming = (
        arena.shl(carry_class[0], 1),
        arena.or_(arena.shl(carry_class[1], 1), first),
        arena.shl(carry_class[2], 1),
    )
    out_masks: list[list[Expr]] = [[] for _ in range(spec.base)]
    for d in range(spec.base):
        r = d % chunk
        for c in range(3):
            out_masks[3 * r + c].append(arena.and_(masks[d], incoming[c]))
    values = tuple(arena.or_many(group, width) for group in out_masks)
    return trim_closed_root(arena, digit_root_from_value_masks(arena, values, spec))


def collatz_successor_formula_local_composite_radix(
    arena: FormulaArena,
    root: FormulaRoot,
    spec: DigitSpec,
) -> tuple[FormulaRoot, str, None]:
    """Original Collatz step in any radix divisible by six using radius-1 maps."""
    if spec.base % 6:
        raise ValueError("local Collatz radix must be divisible by six")
    quotient, remainder = local_divide2_even_radix(arena, root, spec)
    if remainder == 0:
        return quotient, "divide_2_local", None
    return (
        local_multiply3_add1_radix_multiple3(arena, root, spec),
        "multiply_3_add_1_local",
        None,
    )


def collatz_orbit_formulas_ternary(
    seed: int,
    *,
    max_steps: int = 10000,
    stop_at_one: bool = True,
    materialize_values: bool = False,
) -> tuple[FormulaArena, tuple[CollatzStep, ...]]:
    """Forward an explicit ternary orbit request to the proof oracle."""
    from number_compiler.projection.collatz_orbits.radix import (
        collatz_orbit_formulas_ternary as lower_orbit,
    )

    return lower_orbit(
        seed,
        max_steps=max_steps,
        stop_at_one=stop_at_one,
        materialize_values=materialize_values,
    )


def collatz_orbit_formulas_local_composite_radix(
    seed: int,
    *,
    radix: int = 6,
    max_steps: int = 10000,
    stop_at_one: bool = True,
    materialize_values: bool = False,
) -> tuple[FormulaArena, tuple[CollatzStep, ...]]:
    """Forward an explicit composite-radix orbit request to the proof oracle."""
    from number_compiler.projection.collatz_orbits.radix import (
        collatz_orbit_formulas_local_composite_radix as lower_orbit,
    )

    return lower_orbit(
        seed,
        radix=radix,
        max_steps=max_steps,
        stop_at_one=stop_at_one,
        materialize_values=materialize_values,
    )


__all__ = [
    "DUODECIMAL",
    "SENARY",
    "TERNARY",
    "collatz_orbit_formulas_local_composite_radix",
    "collatz_orbit_formulas_ternary",
    "collatz_successor_formula_local_composite_radix",
    "collatz_successor_formula_ternary",
    "local_divide2_even_radix",
    "local_multiply3_add1_radix_multiple3",
    "ternary_multiply3_add1",
]

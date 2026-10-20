"""Root-free algebraic templates for reverse-and-add pair coefficients.

This module is intentionally below the semantic :class:`FormulaRoot` layer.
Every function consumes/returns only hash-consed :class:`Expr` planes, so the
same recurrence can be reused by the ordinary successor compiler and by native
temporal elimination without creating an intermediate state representation.
"""

from __future__ import annotations

from collections.abc import Sequence

from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    apply_carry_fn,
    compose_carry_fn,
)
from number_compiler.arithmetic.carry.prefix_monoid import (
    RESET_PREFIX_MONOID,
    FormulaPrefixMonoidProjection,
    compile_reset_prefix_monoid,
)
from number_compiler.arithmetic.formula.formula import FormulaArena
from number_compiler.arithmetic.formula.types import Expr, RadixSpec


def check_pair_planes(planes: Sequence[Expr], spec: RadixSpec) -> tuple[Expr, ...]:
    planes = tuple(planes)
    if len(planes) != spec.plane_count:
        raise ValueError((len(planes), spec.plane_count))
    if not planes:
        raise ValueError("empty pair planes")
    width = planes[0].width
    if any(p.width != width for p in planes):
        raise ValueError("plane width mismatch")
    return planes


def threshold_plane_views(
    arena: FormulaArena,
    planes: Sequence[Expr],
    spec: RadixSpec,
) -> tuple[Expr, Expr, Expr]:
    """Return exact ``(<b-1, =b-1, >b-1)`` masks for one plane family."""
    planes = check_pair_planes(planes, spec)
    equal = arena.predicate("EQ", spec.threshold, planes)
    greater = arena.predicate("GT", spec.threshold, planes)
    less = arena.not_(arena.or_(equal, greater))
    return less, equal, greater


_CARRY_ELEMENTS = (CarryFn.CONST0, CarryFn.ID, CarryFn.CONST1)
_CARRY_ID = {fn: i for i, fn in enumerate(_CARRY_ELEMENTS)}
if RESET_PREFIX_MONOID.composition != tuple(
    tuple(_CARRY_ID[compose_carry_fn(after, before)] for before in _CARRY_ELEMENTS)
    for after in _CARRY_ELEMENTS
):
    raise AssertionError("shared reset-prefix monoid disagrees with carry composition")


def carry_prefix_projection(
    arena: FormulaArena,
    planes: Sequence[Expr],
    spec: RadixSpec,
) -> FormulaPrefixMonoidProjection:
    """Compile the ``LT/EQ/GT`` carry-domain word into one prefix monoid.

    The three local domains are exactly ``CONST0 / ID / CONST1``.  Prefix
    products are built by the shared logarithmic spatial compiler also used by
    Collatz/radix digit transducers.  No recursive carry row is retained.
    """
    planes = check_pair_planes(planes, spec)
    for plane in planes:
        arena.require_owned(plane)
    key = ("carry-prefix-monoid", spec.base, tuple(p.id for p in planes))
    cached = arena.metadata_get(key)
    if isinstance(cached, FormulaPrefixMonoidProjection):
        return cached
    less, equal, greater = threshold_plane_views(arena, planes, spec)
    projection = compile_reset_prefix_monoid(arena, less, equal, greater)
    arena.metadata_set(key, projection)
    return projection


def carry_plane_scan(
    arena: FormulaArena,
    planes: Sequence[Expr],
    spec: RadixSpec,
) -> Expr:
    """Exact outgoing carry mask ``C_(i+1)`` in logarithmic spatial depth."""
    projection = carry_prefix_projection(arena, planes, spec)
    # Incoming C_0 is zero; only CONST1 maps it to one.
    return projection.masks[_CARRY_ID[CarryFn.CONST1]]


def carry_boundary_at(
    arena: FormulaArena,
    projection: FormulaPrefixMonoidProjection,
    boundary: int,
    *,
    incoming: int = 0,
) -> int:
    """Random-access carry boundary ``C_boundary`` from a prefix projection."""
    boundary, incoming = int(boundary), int(incoming)
    if incoming not in (0, 1):
        raise ValueError(incoming)
    if not 0 <= boundary <= projection.width:
        raise IndexError(boundary)
    if boundary == 0:
        return incoming
    element = projection.state_at(arena, boundary - 1)
    return apply_carry_fn(_CARRY_ELEMENTS[element], incoming)


def growth_carry_views(
    arena: FormulaArena, carry: Expr, width: int
) -> tuple[Expr, Expr, Expr, Expr]:
    """Aligned forward and mirrored carry planes for a one-digit growth edge."""
    resized = arena.resize(carry, width)
    left = arena.shl(resized, 1)
    right = arena.resize(arena.mirror(carry), width)
    return resized, left, right, arena.shl(right, 1)


def branch_coefficient_planes(
    arena: FormulaArena,
    source_planes: Sequence[Expr],
    growth: int,
    spec: RadixSpec,
    carry: Expr,
) -> tuple[Expr, ...]:
    """Apply one pair recurrence as a root-free algebraic expression family.

    ``carry[i]`` denotes ``L_(i+1)``.  For no growth this emits

        2*S_i + L_i + R_(i+1) - b*(L_(i+1)+R_i).

    For growth it emits the edge and shifted-internal formulas.  The returned
    tuple has no semantic/cache identity until an outer compiler chooses to
    wrap it in a FormulaRoot.
    """
    source_planes = check_pair_planes(source_planes, spec)
    growth = int(growth)
    if growth not in (0, 1):
        raise ValueError(growth)
    width = source_planes[0].width
    if carry.width != width:
        raise ValueError((carry.width, width))
    nplanes = spec.plane_count

    if growth == 0:
        Li = arena.shl(carry, 1)
        Ri = arena.mirror(carry)
        Rip1 = arena.shr(Ri, 1)
        args = source_planes + (Li, carry, Ri, Rip1)
        return tuple(
            arena.coeffmap("NO_GROWTH", bit, spec.base, nplanes, args)
            for bit in range(nplanes)
        )

    out_width = width + 1
    cur = tuple(arena.resize(p, out_width) for p in source_planes)
    prev = tuple(arena.shl(p, 1) for p in cur)
    carry_p, Li, Ri, Rim1 = growth_carry_views(arena, carry, out_width)
    internal = cur + prev + (Li, carry_p, Ri, Rim1)
    edge = cur + (carry_p,)
    interior_mask = arena.range_mask(1, width, out_width)
    result: list[Expr] = []
    for bit in range(nplanes):
        core = arena.and_(
            arena.coeffmap("GROWTH_INTERNAL", bit, spec.base, nplanes, internal),
            interior_mask,
        )
        edges = arena.coeffmap("GROWTH_EDGE", bit, spec.base, nplanes, edge)
        result.append(arena.or_(core, edges))
    return tuple(result)


__all__ = [
    "branch_coefficient_planes",
    "carry_boundary_at",
    "carry_plane_scan",
    "carry_prefix_projection",
    "check_pair_planes",
    "threshold_plane_views",
]

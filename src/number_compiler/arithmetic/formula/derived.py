"""Ephemeral threshold/carry views and the canonical self-branching step."""

from __future__ import annotations

from number_compiler.arithmetic.automata.guard import forbid_in_powered_jump
from number_compiler.arithmetic.formula.formula import (
    FormulaArena,
    FormulaRoot,
    canonical_root_key,
)
from number_compiler.arithmetic.formula.pair_algebra import (
    branch_coefficient_planes,
    carry_plane_scan,
    threshold_plane_views,
)
from number_compiler.arithmetic.formula.types import Expr, RadixSpec


def threshold_views(
    arena: FormulaArena, root: FormulaRoot, spec: RadixSpec
) -> tuple[Expr, Expr, Expr]:
    forbid_in_powered_jump("threshold_views")
    return threshold_plane_views(arena, root.planes, spec)


def carry_out(arena: FormulaArena, root: FormulaRoot, spec: RadixSpec) -> Expr:
    forbid_in_powered_jump("carry_out")
    """Exact outgoing carry mask ``L_(i+1)`` in O(log width) IR depth."""
    key = ("carry", spec.base, canonical_root_key(root))
    cached = arena.derived_get(key)
    if cached is not None:
        return cached
    return arena.derived_set(key, carry_plane_scan(arena, root.planes, spec))


def growth_predicate(
    arena: FormulaArena, root: FormulaRoot, spec: RadixSpec
) -> tuple[Expr, int]:
    forbid_in_powered_jump("growth_predicate")
    """Return the derived terminal-carry predicate and queried bit position."""
    carry = carry_out(arena, root, spec)
    return carry, root.width - 1


def growth_bit(arena: FormulaArena, root: FormulaRoot, spec: RadixSpec) -> int:
    forbid_in_powered_jump("growth_bit")
    """Return the reverse-add growth bit from the boundary phase summary.

    For symmetric pair fields the first low-edge non-neutral coefficient has
    the same sign as the final effective carry reset.  Building a carry-prefix word
    merely to query its last bit is therefore eager forcing work.
    """
    from number_compiler.arithmetic.formula.summary import (
        get_summary,
        synthesize_symmetric_summary,
    )

    summary = get_summary(arena, root, spec)
    if summary is None:
        summary = synthesize_symmetric_summary(arena, root, spec)
    return summary.growth_from_outer_symmetry


def border_view(arena: FormulaArena, root: FormulaRoot, spec: RadixSpec) -> Expr:
    forbid_in_powered_jump("border_view")
    carry = carry_out(arena, root, spec)
    return arena.xor(arena.shl(carry, 1), carry)


def compile_branch(
    arena: FormulaArena,
    source: FormulaRoot,
    growth: int,
    spec: RadixSpec,
    carry: Expr | None = None,
) -> FormulaRoot:
    forbid_in_powered_jump("compile_branch")
    """Compile one exact branch; growth is derived by callers, never persistent state."""
    growth = int(growth)
    if growth not in (0, 1):
        raise ValueError(growth)
    carry = carry_out(arena, source, spec) if carry is None else carry
    return FormulaRoot(
        branch_coefficient_planes(arena, source.planes, growth, spec, carry)
    )


def successor(arena: FormulaArena, source: FormulaRoot, spec: RadixSpec) -> FormulaRoot:
    forbid_in_powered_jump("successor")
    """Canonical successor with event-selective growth metadata.

    The semantic source remains only the coefficient planes.  A cached symmetric
    BlockSummary supplies growth in O(1); missing summaries are synthesized from
    only the outer threshold run on the ordinary/reference path.
    """
    from number_compiler.arithmetic.formula.summary import (
        get_summary,
        synthesize_symmetric_summary,
    )

    summary = get_summary(arena, source, spec)
    if summary is None:
        summary = synthesize_symmetric_summary(arena, source, spec)
    growth = summary.growth_from_outer_symmetry
    carry = carry_out(arena, source, spec)
    target = compile_branch(arena, source, growth, spec, carry)
    # Populate non-semantic compiler metadata for the next ordinary step.  A
    # powered backend is forbidden from using this positional synthesis path.
    synthesize_symmetric_summary(arena, target, spec)
    return target


__all__ = [
    "border_view",
    "carry_out",
    "compile_branch",
    "growth_bit",
    "growth_predicate",
    "successor",
    "threshold_views",
]

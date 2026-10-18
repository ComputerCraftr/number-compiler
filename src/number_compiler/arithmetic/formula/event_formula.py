"""Root-free exact position-set formulas for carry forcing events.

These objects are *compiler views* of the canonical FormulaRoot planes.  They do
not own semantic state.  In particular the one-hot coefficient sets ``X_v``, the
forward carry set, carry border, and signed event-value sets are all derived by
hash-consed Boolean formulas from the source planes.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass

from number_compiler.arithmetic.automata.guard import forbid_in_powered_jump
from number_compiler.arithmetic.carry.event_memory import forcing_event_alphabet
from number_compiler.arithmetic.formula.formula import (
    FormulaArena,
    FormulaRoot,
    canonical_root_key,
    reachable,
)
from number_compiler.arithmetic.formula.pair_algebra import (
    carry_plane_scan,
    check_pair_planes,
    growth_carry_views,
)
from number_compiler.arithmetic.formula.types import Expr, RadixSpec


def value_position_sets(
    arena: FormulaArena, planes: Sequence[Expr], spec: RadixSpec
) -> tuple[Expr, ...]:
    """Exact one-hot sets ``X_v={i:S_i=v}`` for ``0 <= v <= 2(b-1)``."""
    planes = check_pair_planes(planes, spec)
    return tuple(
        arena.predicate("EQ", value, planes) for value in range(spec.pair_max + 1)
    )


def _assignment_mask(
    arena: FormulaArena, masks: Sequence[Expr], bits: int, *, domain: Expr | None = None
) -> Expr:
    width = masks[0].width
    terms: list[Expr] = []
    for index, mask in enumerate(masks):
        terms.append(mask if (bits >> index) & 1 else arena.not_(mask))
    if domain is not None:
        terms.append(domain)
    return arena.and_many(terms, width)


def _linear_boolean_value_sets(
    arena: FormulaArena,
    masks: Sequence[Expr],
    coefficients: Sequence[int],
    *,
    domain: Expr | None = None,
) -> dict[int, Expr]:
    masks = tuple(masks)
    coefficients = tuple(map(int, coefficients))
    if not masks or len(masks) != len(coefficients):
        raise ValueError((len(masks), len(coefficients)))
    width = masks[0].width
    if any(mask.width != width for mask in masks):
        raise ValueError("mask width mismatch")
    grouped: dict[int, list[Expr]] = {}
    for bits in range(1 << len(masks)):
        value = sum(c for i, c in enumerate(coefficients) if (bits >> i) & 1)
        grouped.setdefault(value, []).append(
            _assignment_mask(arena, masks, bits, domain=domain)
        )
    return {value: arena.or_many(parts, width) for value, parts in grouped.items()}


@dataclass(frozen=True, slots=True)
class CarryEventFormulaView:
    """Exact derived carry/event position-set view for one branch."""

    base: int
    source_width: int
    target_width: int
    growth: int
    carry_out: Expr  # position i is C_(i+1), source width
    carry_border: Expr  # C_i xor C_(i+1), source width
    value_sets: tuple[Expr, ...]  # X_v over the source pair field
    event_sets: tuple[tuple[int, Expr], ...]
    event_support: Expr

    def event_mask(self, value: int) -> Expr:
        for item, mask in self.event_sets:
            if item == value:
                return mask
        raise KeyError(value)

    @property
    def event_values(self) -> tuple[int, ...]:
        return tuple(value for value, _ in self.event_sets)


def carry_event_formula_from_planes(
    arena: FormulaArena,
    planes: Sequence[Expr],
    growth: int,
    spec: RadixSpec,
    *,
    carry: Expr | None = None,
) -> CarryEventFormulaView:
    """Compile exact signed event position sets from source coefficient planes.

    ``growth`` is branch metadata, not semantic state.  No target FormulaRoot is
    constructed.  For no growth the four Boolean terms implement

        E_i=C_i+C_(d-i-1)-b(C_(i+1)+C_(d-i)).

    For growth the two edge values and the shifted interior formula are compiled
    directly from the same forward carry field.
    """
    forbid_in_powered_jump("carry_event_formula")
    planes = check_pair_planes(planes, spec)
    growth = int(growth)
    if growth not in (0, 1):
        raise ValueError(growth)
    width = planes[0].width
    carry = carry_plane_scan(arena, planes, spec) if carry is None else carry
    if carry.width != width:
        raise ValueError((carry.width, width))
    X = value_position_sets(arena, planes, spec)
    border = arena.xor(arena.shl(carry, 1), carry)

    if growth == 0:
        Ci = arena.shl(carry, 1)
        Cd_i = arena.mirror(carry)
        Cd_i_minus_1 = arena.shr(Cd_i, 1)
        grouped = _linear_boolean_value_sets(
            arena, (Ci, Cd_i_minus_1, carry, Cd_i), (1, 1, -spec.base, -spec.base)
        )
        target_width = width
    else:
        target_width = width + 1
        carry_p, Ci, Cd_i, Cd_i_plus_1 = growth_carry_views(arena, carry, target_width)
        interior = arena.range_mask(1, width, target_width)
        grouped = _linear_boolean_value_sets(
            arena,
            (Ci, Cd_i, carry_p, Cd_i_plus_1),
            (1, 1, -spec.base, -spec.base),
            domain=interior,
        )
        # Both growth edges depend on C_1 only.  Duplicate source position 0 to
        # the far edge by mirroring the one-bit edge mask; this is still a pure
        # positional formula, not point evaluation.
        c1_at_zero = arena.and_(carry_p, arena.range_mask(0, 1, target_width))
        edge_c1 = arena.or_(c1_at_zero, arena.mirror(c1_at_zero))
        edges = arena.or_(
            arena.range_mask(0, 1, target_width),
            arena.range_mask(target_width - 1, target_width, target_width),
        )
        edge_zero = arena.and_(edges, arena.not_(edge_c1))
        grouped.setdefault(1, arena.zero(target_width))
        grouped[1] = arena.or_(grouped[1], edge_zero)
        edge_value = 1 - spec.base
        grouped.setdefault(edge_value, arena.zero(target_width))
        grouped[edge_value] = arena.or_(grouped[edge_value], edge_c1)

    allowed = set(forcing_event_alphabet(spec.base))
    event_sets = tuple(
        sorted((value, mask) for value, mask in grouped.items() if value in allowed)
    )
    support = arena.or_many(
        (mask for value, mask in event_sets if value != 0), target_width
    )
    return CarryEventFormulaView(
        base=spec.base,
        source_width=width,
        target_width=target_width,
        growth=growth,
        carry_out=carry,
        carry_border=border,
        value_sets=X,
        event_sets=event_sets,
        event_support=support,
    )


def carry_event_formula_metrics(view: CarryEventFormulaView) -> dict[str, int]:
    """Charged DAG metrics for the complete derived event view."""
    roots = (
        view.carry_out,
        view.carry_border,
        view.event_support,
        *view.value_sets,
        *(mask for _value, mask in view.event_sets),
    )
    nodes = reachable(roots)
    refs = sum(len(node.args) for node in nodes.values())
    return {
        "nodes": len(nodes),
        "references": refs,
        "source_width": view.source_width,
        "target_width": view.target_width,
        "event_value_count": len(view.event_sets),
        "value_set_count": len(view.value_sets),
    }


def carry_event_formula_view(
    arena: FormulaArena,
    root: FormulaRoot,
    spec: RadixSpec,
    *,
    growth: int | None = None,
) -> CarryEventFormulaView:
    """Derived FormulaRoot wrapper for ordinary/research compilation.

    If ``growth`` is omitted the registered symmetric summary is used.  No
    positional scan is performed here; a missing summary is an error so this
    helper cannot silently reintroduce the old sequential growth probe.
    """
    from number_compiler.arithmetic.formula.summary import get_summary

    if growth is None:
        summary = get_summary(arena, root, spec, required=True)
        growth = summary.growth_from_outer_symmetry
    key = ("carry-event-view", spec.base, canonical_root_key(root, arena), int(growth))
    cached = arena.metadata_get(key)
    if isinstance(cached, CarryEventFormulaView):
        return cached
    view = carry_event_formula_from_planes(arena, root.planes, int(growth), spec)
    arena.metadata_set(key, view)
    return view


__all__ = [
    "CarryEventFormulaView",
    "carry_event_formula_from_planes",
    "carry_event_formula_metrics",
    "carry_event_formula_view",
    "value_position_sets",
]

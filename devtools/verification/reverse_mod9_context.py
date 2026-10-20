"""Replacement geometry/mod9 primitive for the bounded threshold compiler.

Both spatial branches share the same direct domain consumer. Value transport
is affine modulo nine with forcing supplied by the geometry prefix monoid.
No exact pair, normalized decimal digit, q chart, or reset field is interned.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from devtools.verification.threshold_expressions import Expr

if TYPE_CHECKING:
    from devtools.verification.reverse_geometry_context import (
        GeometryAction,
        ReverseGeometryContext,
    )


def primitive_mod9(context: ReverseGeometryContext) -> GeometryAction:
    e, capacity = context.expressions, context.capacity
    e.work = 0
    width = context.inputs[0]
    width_is = tuple(context.equal_constant(width, m) for m in range(1, capacity + 1))
    domain_inputs, residues = context.inputs[1::2], context.inputs[2::2]
    zero, one = context.zero, context.one
    blank_domain, blank_value = e.constant(3, 0), e.constant(9, 0)
    admitted = context.not_expression(context.equal_constant(width, 0))
    for i, (domain, residue) in enumerate(zip(domain_inputs, residues, strict=True)):
        is_eq = context.equal_constant(domain, 1)
        valid = e.select(is_eq, context.equal_constant(residue, 0), one)
        padding = context.and_expression(
            context.equal_constant(domain, 0), context.equal_constant(residue, 0)
        )
        inactive = e.table(
            width, 2, tuple(int(m <= 2 * i) for m in range(capacity + 1))
        )
        admitted = context.and_expression(admitted, e.select(inactive, padding, valid))
        # GT u=0 decodes to18; other GT residues decode to u+9.
        low_even = e.table(residue, 2, tuple(int(u % 2 == 0) for u in range(9)))
        high_even = e.table(
            residue, 2, tuple(int(u == 0 or u % 2 == 1) for u in range(9))
        )
        even = e.select(
            is_eq,
            zero,
            e.select(context.equal_constant(domain, 2), high_even, low_even),
        )
        admitted = context.and_expression(
            admitted, e.select(width_is[2 * i], even, one)
        )
    domains: list[Expr] = []
    for i in range(capacity):
        domain = blank_domain
        for m, condition in enumerate(width_is, 1):
            if i < m:
                domain = e.select(condition, domain_inputs[min(i, m - 1 - i)], domain)
        domains.append(domain)
    source_geometry = context.geometry.from_domains(tuple(domains))
    carry, _unused_growth_binding, admitted, next_width = context.transport_extent(
        width, width_is, source_geometry, admitted
    )
    out_domain, out_value = (
        [blank_domain] * context.slots,
        [blank_value] * context.slots,
    )

    def channels(m: int, left: int, right: int) -> tuple[Expr, Expr]:
        operands: list[Expr] = []
        terms: list[tuple[Expr, int]] = []
        for position in (left, right):
            if position == m:
                # New growth edge is the ordinary constant normalized digit1.
                operands.extend((blank_domain, e.constant(9, 1), zero))
                terms.append((e.constant(9, 1), 1))
            else:
                orbit = min(position, m - 1 - position)
                operands.extend(
                    (domain_inputs[orbit], residues[orbit], carry[position])
                )
                terms.extend(
                    (
                        (residues[orbit], 1),
                        (carry[position], 1),
                        (carry[position + 1], -1),
                    )
                )
        return e.skew_pair_domain(*operands), e.affine(9, terms)

    for m, condition in enumerate(width_is, 1):
        for i in range(min((m + 2) // 2, context.slots)):
            low = (
                channels(m, i, m - 1 - i)
                if i < (m + 1) // 2
                else (blank_domain, blank_value)
            )
            if m < capacity:
                high = channels(m, i, m - i)
                chosen = tuple(
                    e.select(carry[m], a, b) for a, b in zip(high, low, strict=True)
                )
            else:
                chosen = low
            out_domain[i] = e.select(condition, chosen[0], out_domain[i])
            out_value[i] = e.select(condition, chosen[1], out_value[i])
    outputs = (
        next_width,
        *(v for pair in zip(out_domain, out_value, strict=True) for v in pair),
    )
    context.primitive_successors += 1
    return context.build_action(outputs, admitted, 1)

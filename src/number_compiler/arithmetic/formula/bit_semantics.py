"""Shared scalar semantics for coefficient-formula evaluator owners.

These helpers read declared expression metadata and requested cached child bits;
they neither grant execution authority nor own caches or semantic state.
"""

from __future__ import annotations
from collections.abc import Callable
from number_compiler.arithmetic.formula.types import Expr
from number_compiler.arithmetic.formula.skew_residue_laws import (
    pair_growth_edge,
    pair_growth_interior,
    pair_no_growth,
)


def constant_bit(node: Expr, position: int) -> int | None:
    if node.kind == "ZERO":
        return 0
    if node.kind == "ONES":
        return 1
    if node.kind == "LITERAL":
        return (int(node.param[0]) >> position) & 1
    if node.kind == "RANGE":
        low, high = map(int, node.param)
        return int(low <= position < high)
    return None


def shift_position(node: Expr, position: int) -> int:
    offset = int(node.param[0])
    return position - offset if node.kind == "SHL" else position + offset


def coefficient_dependencies(
    node: Expr, position: int
) -> tuple[tuple[Expr, int], ...] | None:
    if str(node.param[0]) == "GROWTH_EDGE":
        if position not in (0, node.width - 1):
            return None
        planes = int(node.param[3])
        return tuple((node.args[index], 0) for index in range(planes + 1))
    return tuple((child, position) for child in node.args)


def predicate_bit(node: Expr, coefficient: int) -> int:
    operation, threshold = str(node.param[0]), int(node.param[1])
    return (
        int(coefficient == threshold)
        if operation == "EQ"
        else int(coefficient > threshold)
    )


def coefficient_bit(node: Expr, pos: int, get: Callable[[Expr, int], int]) -> int:
    mode, bit, base, nplanes = (
        str(node.param[0]),
        int(node.param[1]),
        int(node.param[2]),
        int(node.param[3]),
    )
    if mode == "NO_GROWTH":
        coeff = sum(get(node.args[b], pos) << b for b in range(nplanes))
        Li, Li1, Ri, Ri1 = (get(node.args[j], pos) for j in range(nplanes, nplanes + 4))
        coeff = pair_no_growth(coeff, Li, Li1, Ri1, Ri, base)
    elif mode == "GROWTH_INTERNAL":
        coeff = sum(get(node.args[b], pos) << b for b in range(nplanes))
        prev = sum(get(node.args[nplanes + b], pos) << b for b in range(nplanes))
        off = 2 * nplanes
        Li, Li1, Ri, Rim1 = (get(node.args[j], pos) for j in range(off, off + 4))
        coeff = pair_growth_interior(coeff, prev, Li, Li1, Ri, Rim1, base)
    elif mode == "GROWTH_EDGE":
        coeff = sum(get(node.args[b], 0) << b for b in range(nplanes))
        coeff = pair_growth_edge(coeff, get(node.args[nplanes], 0), base)
    elif mode == "DIGIT_NORMALIZE":
        coeff = sum(get(node.args[b], pos) << b for b in range(nplanes))
        incoming = get(node.args[nplanes], pos)
        outgoing = get(node.args[nplanes + 1], pos)
        coeff = coeff + incoming - base * outgoing
    else:
        raise AssertionError(mode)
    return (coeff >> bit) & 1

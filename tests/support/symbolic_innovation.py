"""Independent bounded polynomial oracles for symbolic innovation tests."""

from __future__ import annotations

from typing import assert_never

from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.fields.radial_innovation import (
    InnovationAdd,
    InnovationAtom,
    InnovationCharted,
    InnovationID,
    InnovationInterval,
    InnovationNode,
    InnovationRadial,
    InnovationScale,
    InnovationZero,
)
from number_compiler.arithmetic.fields.symbolic_innovation import (
    SymbolicInnovationArena,
)


def polynomial(arena: SymbolicInnovationArena, word: list[int]) -> InnovationID:
    one = arena.interval(1)
    return arena.linear_combination(
        tuple(
            (coefficient, arena.chart(one, CylinderChart(1, -index)))
            for index, coefficient in enumerate(word)
            if coefficient
        )
    )


def _children(node: InnovationNode) -> tuple[InnovationID, ...]:
    match node:
        case InnovationAdd():
            return (node.left, node.right)
        case InnovationCharted() | InnovationRadial() | InnovationScale():
            return (node.child,)
        case InnovationAtom() | InnovationInterval() | InnovationZero():
            return ()
        case _:
            assert_never(node)


def evaluate(arena: SymbolicInnovationArena, root: InnovationID) -> dict[int, int]:
    """Expand a bounded Laurent polynomial without quotient loss."""
    memo: dict[InnovationID, dict[int, int]] = {}
    stack: list[tuple[InnovationID, bool]] = [(root, False)]
    while stack:
        ref, ready = stack.pop()
        if ref in memo:
            continue
        node = arena.resolve(ref)
        if not ready:
            stack.append((ref, True))
            stack.extend((child, False) for child in _children(node))
            continue
        result: dict[int, int]
        if isinstance(node, InnovationZero):
            result = {}
        elif isinstance(node, InnovationAtom):
            raise TypeError("test oracle received an unevaluated source atom")
        elif isinstance(node, InnovationInterval):
            assert node.length <= 32
            result = dict.fromkeys(range(node.length), 1)
        elif isinstance(node, InnovationAdd):
            result = memo[node.left].copy()
            for index, value in memo[node.right].items():
                result[index] = result.get(index, 0) + value
        elif isinstance(node, InnovationScale):
            result = {
                index: node.coefficient * value
                for index, value in memo[node.child].items()
            }
        elif isinstance(node, InnovationCharted):
            assert node.chart.extent_scale == node.chart.growth_scale == 0
            result = {
                node.chart.slope * (index - node.chart.offset): value
                for index, value in memo[node.child].items()
            }
        else:
            assert node.multiplier.growth <= 20
            assert node.multiplier.no_growth <= 20
            result = {
                index: (1 << node.multiplier.no_growth) * value
                for index, value in memo[node.child].items()
            }
            for _ in range(node.multiplier.growth):
                before = result.copy()
                for index, value in before.items():
                    result[index + 1] = result.get(index + 1, 0) + value
        memo[ref] = {index: value for index, value in result.items() if value}
    return memo[root]

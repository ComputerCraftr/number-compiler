"""Independent Laurent-polynomial references for exact innovation transport."""

from __future__ import annotations

from collections.abc import Sequence
from typing import cast

import pytest

from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.fields.radial_innovation import RadialMultiplier
from number_compiler.arithmetic.fields.symbolic_innovation import (
    SymbolicInnovationArena,
)
from number_compiler.resources.ledger import ResourceLedger


def _chart(values: dict[int, int], slope: int, offset: int) -> dict[int, int]:
    # p(slope*i+offset) has a contribution at i=slope*(j-offset).
    return {slope * (index - offset): value for index, value in values.items()}


def _radial(values: dict[int, int], q: int, r: int) -> dict[int, int]:
    result = {index: value * 2**q for index, value in values.items()}
    for _ in range(r):
        following = dict(result)
        for index, value in result.items():
            following[index + 1] = following.get(index + 1, 0) + value
        result = following
    return result


def _fold(values: dict[int, int]) -> tuple[int, ...]:
    result = [0] * 4
    for exponent, coefficient in values.items():
        wraps, position = divmod(exponent, 4)
        result[position] += coefficient * (-1 if wraps % 2 else 1)
    return tuple(value % 128 for value in result)


@pytest.mark.parametrize("first_slope", [-1, 1])
@pytest.mark.parametrize("second_slope", [-1, 1])
@pytest.mark.parametrize("first_offset", [-5, 0, 7])
@pytest.mark.parametrize("second_offset", [-4, 1, 6])
def test_mixed_radial_chart_transport_matches_exact_laurent_coefficients(
    first_slope: int, second_slope: int, first_offset: int, second_offset: int
) -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    key = SemanticIdentity("", ("primitive-test-atom", "signed-boundary"))
    atom = arena.atom(key)
    node = arena.radial(atom, RadialMultiplier(1, 2))
    node = arena.chart(node, CylinderChart(first_slope, first_offset))
    node = arena.radial(node, RadialMultiplier(2, 3))
    node = arena.chart(node, CylinderChart(second_slope, second_offset))
    expected = _radial({0: 1, 1: -2, 3: 4}, 1, 2)
    expected = _chart(expected, first_slope, first_offset)
    expected = _radial(expected, 2, 3)
    expected = _chart(expected, second_slope, second_offset)
    retained = ledger.entries, ledger.nodes
    projected = arena.project_cyclotomic(
        arena.action(RadialMultiplier(), node),
        order=8,
        bits=7,
        atoms={key: (1, -2, 0, 4)},
    )
    assert projected.innovation == _fold(expected)
    assert (ledger.entries, ledger.nodes) == retained
    arena.close()
    assert ledger.entries == ledger.nodes == 0


def test_failed_atom_projection_releases_temporary_storage() -> None:
    ledger = ResourceLedger()
    arena = SymbolicInnovationArena(ledger)
    key = SemanticIdentity("", ("primitive-test-atom", "missing"))
    action = arena.action(RadialMultiplier(1, 2), arena.atom(key))
    retained = ledger.entries, ledger.nodes
    with pytest.raises(ValueError, match="unresolved atom"):
        arena.project_cyclotomic(action, order=8, bits=7, atoms={})
    assert (ledger.entries, ledger.nodes) == retained
    arena.close()


def test_caller_chart_and_radial_metadata_are_detached() -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    key = SemanticIdentity("", ("test", "metadata"))
    atom = arena.atom(key)
    multiplier, chart = RadialMultiplier(1, 2), CylinderChart(-1, 7)
    scaled = arena.radial(atom, multiplier)
    charted = arena.chart(atom, chart)
    object.__setattr__(multiplier, "growth", 9)
    object.__setattr__(chart, "offset", 20)
    assert scaled == arena.radial(atom, RadialMultiplier(1, 2))
    assert charted == arena.chart(atom, CylinderChart(-1, 7))
    arena.close()


@pytest.mark.parametrize("coefficient", [1 << 10000, 1.5])
def test_projection_rejects_unbounded_or_noninteger_atom_words(
    coefficient: object,
) -> None:
    arena = SymbolicInnovationArena(ResourceLedger())
    key = SemanticIdentity("", ("test", "atom-word-budget"))
    expression = arena.action(RadialMultiplier(), arena.atom(key))
    with pytest.raises(ValueError, match="local word bound"):
        # Wrongly typed external mappings must be rejected at the runtime edge.
        arena.project_cyclotomic(
            expression,
            order=2,
            bits=5,
            atoms={key: cast(Sequence[int], (coefficient,))},
        )
    arena.close()

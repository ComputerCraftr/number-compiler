"""Exact small-domain oracles for symbolic midpoint execution."""

from __future__ import annotations

from itertools import product

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.exact_tree_context import source_reads_only
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from tests.support.collatz_diamond_fixtures import build_collatz_diamond_runtime
from tests.support.diamond_runtime import build, oracle


@pytest.mark.parametrize("base", [2, 3, 4, 5, 10])
@pytest.mark.parametrize("steps", [0, 1, 2, 3, 4])
def test_reverse_diamonds_against_exact_bimachine(base: int, steps: int) -> None:
    effect = BaseBlockEffect(base)
    source = (base - 1, 2 * base - 2, base - 1)
    runtime, action = build(effect, source, 8, steps)
    expected = oracle(effect, source, 8, steps)

    @source_reads_only
    def point(position: int) -> int:
        return runtime.point(action, position)

    assert [point(i) for i in range(8)] == expected
    assert runtime.ledger.counters.get("sequential_generation_advances", 0) == 0
    assert all(row.accounting_delta == 0 for row in runtime.ledger.inventory())


@pytest.mark.parametrize("steps", [0, 1, 2, 3, 4, 8])
def test_physical_collatz_diamonds_on_small_sources(steps: int) -> None:
    effect = CollatzPhysicalBlockEffect()
    for source in product((0, 1), repeat=2):
        runtime, action = build_collatz_diamond_runtime(effect, (*source, 1), 8, steps)
        expected = oracle(effect, (*source, 1), 8, steps)
        assert [runtime.point(action, i) for i in range(8)] == expected

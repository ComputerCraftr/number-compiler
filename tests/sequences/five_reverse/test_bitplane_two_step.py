"""Dense bitplane kernel: physical parity, limits, work and actual dispatch."""

from __future__ import annotations

import sys
from collections.abc import Callable
from itertools import product
from random import Random

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.metric_keys import five_reverse as keys
from number_compiler.sequences.five_reverse import packed_two_step as packed
from number_compiler.sequences.five_reverse import term as term_module
from number_compiler.sequences.five_reverse.bitplane_two_step import (
    execute_bitplane_five,
)
from number_compiler.sequences.five_reverse.term import FiveReverseTerm


def run(
    execute: Callable[[int, int, int, packed.PackedFiveWork], int],
    seed: int,
    n: int,
    bits: int,
) -> tuple[int | None, int, int, int]:
    work = packed.PackedFiveWork()
    try:
        result = execute(seed, n, bits, work)
    except BlockContextBudgetExceeded:
        result = None
    return result, work.attempted, work.digit_reads, work.executed_pairs


def test_dense_planes_all_small_and_random_budget_equivalence() -> None:
    rng = Random(8)
    for seed, n in product(range(1000), (1, 2, 3, 7, 16)):
        assert run(execute_bitplane_five, seed, n, 4096) == run(
            packed.execute_packed_five, seed, n, 4096
        )
    for _ in range(1200):
        seed = rng.randrange(10 ** rng.randrange(1, 30))
        n = rng.randrange(1, 40)
        bits = max(1, seed.bit_length() + rng.randrange(-2, 20))
        assert run(execute_bitplane_five, seed, n, bits) == run(
            packed.execute_packed_five, seed, n, bits
        )


def test_bitplane_does_not_change_decimal_limit() -> None:
    limit = sys.get_int_max_str_digits()
    try:
        sys.set_int_max_str_digits(640)
        for seed, n in ((10**699, 2), (10**699 + 3, 17), (10**699 + 73, 16)):
            assert run(execute_bitplane_five, seed, n, 10000) == run(
                packed.execute_packed_five, seed, n, 10000
            )
        assert sys.get_int_max_str_digits() == 640
    finally:
        sys.set_int_max_str_digits(limit)


@pytest.mark.parametrize(
    ("seed", "bits", "attempted", "reads", "pairs"),
    ((6, 4, 1, 0, 0), (1, 3, 2, 1, 1)),
)
def test_bitplane_refuses_first_inadmissible_state(
    seed: int, bits: int, attempted: int, reads: int, pairs: int
) -> None:
    assert run(execute_bitplane_five, seed, 2, bits) == (
        None,
        attempted,
        reads,
        pairs,
    )


def test_source_owner_can_measure_the_candidate(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    expected = run(packed.execute_packed_five, 73, 128, 4096)
    monkeypatch.setattr(term_module, "_BITPLANE_MIN_STEPS", 64)
    with FiveReverseTerm(73, 128, max_steps=128, max_state_bits=4096) as term:
        assert term.materialize(max_bits=4096) == expected[0]
        ledger = term.resource_ledger
        assert ledger.counters[keys.FIVE_REVERSE_BITPLANE_PAIRS] == 64
        assert (
            ledger.counters[keys.FIVE_REVERSE_PACKED_LOGICAL_DIGIT_READS] == expected[2]
        )
    assert ledger.entries == ledger.nodes == 0


def test_capped_owner_keeps_the_existing_executor(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(term_module, "_BITPLANE_MIN_STEPS", 1)
    with FiveReverseTerm(
        6, 2, max_steps=2, max_state_bits=4, max_context_nodes=500
    ) as term:
        with pytest.raises(BlockContextBudgetExceeded):
            term.packed_value(6, 2)
        assert term.resource_ledger.counters[keys.FIVE_REVERSE_EXACT_STEPS] == 1
        assert (
            term.resource_ledger.counters.get(keys.FIVE_REVERSE_BITPLANE_PAIRS, 0) == 0
        )

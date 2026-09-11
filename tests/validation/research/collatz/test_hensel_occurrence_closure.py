"""Exhaustive bounded successor closure from the direct U-squared image."""

import pytest

from devtools.proofs import exact_oracle
from number_compiler.sequences.collatz.hensel_occurrence import (
    CollatzHenselOccurrenceCarrier,
)
from number_compiler.sequences.collatz.pair import accelerated_odd_collatz


@pytest.mark.parametrize("shard", range(16))
def test_all_odd_sixteen_bit_occurrences_eight_successors(shard: int) -> None:
    with exact_oracle():
        for seed in range(1 + 2 * shard, 1 << 16, 32):
            carrier = CollatzHenselOccurrenceCarrier()
            first = accelerated_odd_collatz(seed)
            second = accelerated_odd_collatz(first.target)
            occurrence = carrier.image_second(seed)
            assert occurrence.value == second.target
            value = second.target
            assert occurrence.h == 2
            for _ in range(8):
                expected = accelerated_odd_collatz(value)
                step = carrier.next_step(occurrence)
                assert step.target.a in (1, 2)
                assert step.target.h == occurrence.h + 1
                assert step.valuation == expected.valuation
                assert step.target.value == expected.target
                occurrence, value = step.target, expected.target

"""A shared causal cone agrees with independently requested source digits."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.automata.slp_walks import symbol_at
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.temporal_hashlife import growth_ports


@pytest.mark.parametrize("seed", [1, 196, 2001, 99999])
@pytest.mark.parametrize("generation", [32, 64, 96])
def test_batched_center_window_matches_pointed_stencils(
    seed: int, generation: int
) -> None:
    with DoubleReverseTerm(seed, generation, max_state_bits=16384) as term:
        _, source = term._prepare_bank_source(max_prefix=32)
        engine = source.engine
        for f in sorted({0, 1, 3, min(8, source.f_steps), min(15, source.f_steps)}):
            left, right = growth_ports(source.phase, f)
            width = source.width_in + left + right
            count = min(width, 10)
            starts = {0, max(0, (width - count) // 2), width - count}
            for start in starts:
                observed = engine.pointed_window(
                    source.root, f, source.phase, start, count
                )
                if f == 0:
                    expected = tuple(
                        symbol_at(source.arena, source.root, i)
                        for i in range(start, start + count)
                    )
                else:
                    expected = tuple(
                        engine.pointed_stencil(source.root, f, source.phase, i).digit
                        for i in range(start, start + count)
                    )
                assert observed == expected


def test_batched_window_checks_its_complete_interval() -> None:
    with DoubleReverseTerm(196, 32, max_state_bits=16384) as term:
        _, source = term._prepare_bank_source(max_prefix=32)
        width = source.width_in + sum(growth_ports(source.phase, 0))
        with pytest.raises(IndexError):
            source.engine.pointed_window(source.root, 0, source.phase, width - 1, 2)
        with pytest.raises(ValueError):
            source.engine.pointed_window(source.root, 0, source.phase, 0, 19)

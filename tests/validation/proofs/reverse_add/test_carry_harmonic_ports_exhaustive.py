"""Check the harmonic forcing projection against complete exact pair fields."""

from itertools import product

import pytest

from devtools.proofs.carry_harmonic_ports import CarryHarmonicPortAction, harmonic_sum
from number_compiler.arithmetic.carry.carry_monoid import value_carry_fn
from number_compiler.arithmetic.carry.event_memory import forcing_event, pair_step


@pytest.mark.parametrize("width", range(1, 9))
def test_all_symmetric_forcing_harmonics(width: int) -> None:
    alphabets = [range(19)] * (width // 2) + ([range(0, 19, 2)] if width % 2 else [])
    count = 0
    for half in product(*alphabets):
        source = half + (half[:-1] if width % 2 else half)[::-1]
        action = CarryHarmonicPortAction.from_domains(
            value_carry_fn(v, 10) for v in source
        )
        target, growth = pair_step(source, 10)
        assert action.forcing_harmonics() == harmonic_sum(
            forcing_event(source, target, growth)
        )
        count += 1
    assert count == 19 ** (width // 2) * (10 if width % 2 else 1)

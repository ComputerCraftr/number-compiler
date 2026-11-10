"""Binary harmonic output of the certified physical mod-99 quotient."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.pair_numeric_ports import (
    DecimalPairNumericPort,
)
from number_compiler.sequences.reverse_add.q19_output import (
    ReversePairQ19OutputOwner,
)
from number_compiler.sequences.reverse_add.temporal_residue99 import (
    ReverseAddResidue99,
    from_issued_pair,
    from_seed,
)


def _advance(pair: tuple[int, int]) -> tuple[int, int]:
    first, second = pair
    return second, first ^ second


def test_seed196_mod99_ray_has_the_third_cyclotomic_binary_output() -> None:
    assert tuple(from_seed(196, n).target_mod99 for n in range(3, 9)) == (
        11,
        22,
        44,
        88,
        77,
        55,
    )
    expected = ((8, 64), (64, 72), (72, 8))
    for generation in (6, 7, 8, 9, 10, 11, 12, 32, 100, 10**40):
        harmonic = from_seed(196, generation).binary_harmonic_phi3
        assert harmonic == expected[generation % 3]
        assert from_seed(196, generation + 1).binary_harmonic_phi3 == _advance(harmonic)


def test_binary_projection_obeys_one_matrix_step_for_certified_rays() -> None:
    for seed in (0, 1, 10, 100, 196, 789, 889, 987654321):
        for generation in (6, 7, 12, 1001, 10**30):
            current = from_seed(seed, generation)
            following = from_seed(seed, generation + 1)
            assert following.binary_harmonic_phi3 == _advance(
                current.binary_harmonic_phi3
            )


def test_issued_q19_residue_exposes_the_same_bounded_harmonic() -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(196, 10), base=10)
    try:
        issued = from_issued_pair(owner, owner.initial, 6)
        assert issued.source_certified and not issued.control_needed
        assert issued.binary_harmonic_phi3 == from_seed(196, 6).binary_harmonic_phi3
    finally:
        owner.dispose()
    assert ledger.entries == ledger.nodes == 0


def test_binary_projection_refuses_an_early_or_conditional_result() -> None:
    with pytest.raises(ValueError, match="certified six-tick"):
        _ = from_seed(196, 5).binary_harmonic_phi3

    conditional = ReverseAddResidue99(
        duration=6,
        target_mod99=11,
        source_mod9=1,
        source_mod99=11,
        source_width_parity=1,
        control_needed=True,
        source_certified=False,
        proof="conditional input word",
    )
    with pytest.raises(ValueError, match="certified six-tick"):
        _ = conditional.binary_harmonic_phi3


def test_numeric_pair_port_is_an_output_witness_not_a_state_key() -> None:
    with pytest.raises(TypeError):
        hash(DecimalPairNumericPort.atom(9, 99))

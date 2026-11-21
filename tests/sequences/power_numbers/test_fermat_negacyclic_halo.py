"""Source-bound fixed-tripling ring projection and signed seam checks."""

from dataclasses import replace

import pytest

from number_compiler.sequences.power_numbers.fermat_negacyclic_halo import (
    demand_fixed_multiplier_halo,
)


@pytest.mark.parametrize("index", range(5))
@pytest.mark.parametrize("steps", (1, 2, 11))
def test_source_halo_matches_independent_integer_arithmetic(
    index: int, steps: int
) -> None:
    level = (1 << index) - 1
    halo = demand_fixed_multiplier_halo(index, level, steps, wrap_bits=8)
    modulus = (1 << (1 << index)) + 1
    root = pow(3, 1 << level, modulus)
    exact = root * 3**steps
    assert halo.producer_verified
    assert halo.source_residue == root
    assert halo.endpoint_residue == exact % modulus
    assert halo.canonical_source_wrap == (exact // modulus) % 256
    high, low = divmod(3 * root, modulus - 1)
    assert (halo.inlet_low, halo.inlet_high_correction) == (low, -high)
    assert (low - high) % modulus == (3 * root) % modulus
    assert halo.packet()["raw_source_carry"] is None
    assert halo.packet()["primality_authority"] is False


def test_halo_authority_bounds_and_minus_one() -> None:
    halo = demand_fixed_multiplier_halo(4, 15, 1)
    assert halo.endpoint_bits((0, halo.width)) == (
        halo.endpoint_residue & 1,
        halo.endpoint_residue >> halo.width,
    )
    minus_one = demand_fixed_multiplier_halo(1, 1, 4)
    assert minus_one.endpoint_residue == 1 << minus_one.width
    assert minus_one.endpoint_bits((0, minus_one.width)) == (0, 1)
    with pytest.raises(ValueError, match="unissued"):
        replace(halo, endpoint_residue=0).packet()
    with pytest.raises(ValueError, match="unissued"):
        replace(halo, source=replace(halo.source, level=0)).packet()
    for index, level, steps, bits in ((9, 511, 1, 0), (2, 3, 0, 0), (2, 3, 1, 257)):
        with pytest.raises(ValueError, match="work bound"):
            demand_fixed_multiplier_halo(index, level, steps, wrap_bits=bits)


def test_halo_wrap_precision_endpoints() -> None:
    without_wrap = demand_fixed_multiplier_halo(2, 3, 11, wrap_bits=0)
    maximal = demand_fixed_multiplier_halo(2, 3, 11, wrap_bits=256)
    assert without_wrap.canonical_source_wrap is None
    assert maximal.canonical_source_wrap == (16 * 3**11 // 17) % (1 << 256)
    assert without_wrap.endpoint_residue == maximal.endpoint_residue

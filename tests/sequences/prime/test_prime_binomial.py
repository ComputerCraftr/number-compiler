from math import comb

import pytest

from number_compiler.sequences.prime.binomial import (
    binomial_composite,
    pascal_row_prefix,
    project_binomial_prime_block,
    translate_pascal_row_prefix,
    translate_pascal_row_prefix_mod_pow2,
    witness_requires_shared_factor,
)
from number_compiler.sequences.prime.set import project_odd_prime_block


def test_pascal_translation_is_exact_powered_I_plus_S_action() -> None:
    row = pascal_row_prefix(37, 12)
    assert translate_pascal_row_prefix(row, 19) == pascal_row_prefix(56, 12)


def test_pascal_translation_mod_pow2_matches_exact_translation() -> None:
    row = pascal_row_prefix(123, 16)
    for bits in (1, 2, 3, 5, 8):
        modulus = 1 << bits
        exact = translate_pascal_row_prefix(row, 257)
        got = translate_pascal_row_prefix_mod_pow2(row, 257, bits)
        assert got == tuple(x % modulus for x in exact)


@pytest.mark.validation  # Exhaustive binomial/factor primality differential through 299.
def test_binomial_primality_field_matches_multiplication_field_small_range() -> None:
    for n in range(2, 300):
        by_binomial = binomial_composite(n)
        by_factor = any(n % a == 0 for a in range(2, int(n**0.5) + 1))
        assert by_binomial == by_factor


@pytest.mark.validation  # Exhaustive shared-factor witness sweep over 2,500 lanes.
def test_binomial_witness_lane_requires_shared_factor() -> None:
    for n in range(20, 180):
        for k in range(2, min(18, n) + 1):
            assert witness_requires_shared_factor(n, k)


def test_binomial_lane_canonicalization_rediscovers_prime_factor_lanes() -> None:
    start, length = 9_993, 64
    projection = project_binomial_prime_block(start, length)
    factors = [lane.k for lane in projection.canonical_lanes]
    # No prime list is supplied to the construction. Composite k lanes are
    # semantically contained in the earlier prime-divisor witness union.
    assert factors[:8] == [3, 5, 7, 11, 13, 17, 19, 23]
    assert all(k not in factors for k in (9, 15, 21, 25, 27, 33, 35))
    multiplicative = project_odd_prime_block(start, length)
    assert projection.composite_mask == multiplicative.composite_mask


def test_prime_witness_is_pascal_diagonal_identity() -> None:
    # n | C(n,k) iff k | C(n-1,k-1).  This is the algebraic reason the
    # variable candidate modulus can be moved onto the Pascal row coordinate.
    for n in range(10, 60):
        for k in range(2, min(n - 1, 12)):
            assert (comb(n, k) % n == 0) == (comb(n - 1, k - 1) % k == 0)

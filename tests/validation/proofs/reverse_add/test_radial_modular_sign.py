"""Exact bounded modular-sign checks; supplied bounds remain hypotheses."""

from __future__ import annotations

from math import comb

import pytest

from devtools.experiments.reverse_add.radial_modular_sign import (
    ModularSignLimits,
    ModularSignOracle,
    ModularSignWork,
)


@pytest.mark.parametrize("prime", [2, 3, 5, 7, 11, 13])
def test_lucas_binomial_matches_small_exact_rows(prime: int) -> None:
    oracle = ModularSignOracle()
    for row in range(24):
        for index in range(-1, row + 2):
            expected = comb(row, index) % prime if 0 <= index <= row else 0
            assert oracle.binomial_mod(row, index, prime) == expected


def test_huge_binary_row_near_support_edges_never_expands_the_row() -> None:
    row = 10**200
    work = ModularSignWork()
    oracle = ModularSignOracle(work=work)
    assert oracle.sign(row, ((0, 3),), 0, bound=3) == 1
    constructed = work.primes_constructed
    entries = work.factorial_entries
    assert oracle.sign(row, ((17, -2),), row + 17, bound=2) == -1
    assert work.primes_constructed == constructed
    assert work.factorial_entries == entries
    assert work.lucas_digits < 10_000
    assert work.peak_integer_bits < 1024


def test_cancellation_zero_and_negative_values_lift_exactly() -> None:
    oracle = ModularSignOracle()
    row = 40
    index = 17
    assert oracle.sign(row, ((0, 19), (0, -19)), index, bound=1) == 0
    value = 3 * comb(row, index) - 5 * comb(row, index - 1)
    assert value < 0
    assert oracle.sign(row, ((0, 3), (1, -5)), index, bound=abs(value)) == -1


def test_context_reuses_tables_across_many_queries() -> None:
    work = ModularSignWork()
    oracle = ModularSignOracle(work=work)
    for coefficient in range(-8, 9):
        expected = (coefficient > 0) - (coefficient < 0)
        assert oracle.sign(10**50, ((0, coefficient),), 0, bound=8) == expected
    assert work.primes_constructed == 3
    assert work.factorial_entries == 20
    assert work.retained_items == 23


def test_insufficient_modulus_and_inconsistent_hypothesis_refuse() -> None:
    one_prime = ModularSignOracle(limits=ModularSignLimits(max_primes=1))
    with pytest.raises(ValueError, match="insufficient"):
        one_prime.sign(10, ((0, 1),), 0, bound=2)
    with pytest.raises(ValueError, match="inconsistent"):
        ModularSignOracle().sign(10, ((0, 3),), 0, bound=1)


def test_table_budget_refuses_before_retaining_a_partial_table() -> None:
    work = ModularSignWork()
    oracle = ModularSignOracle(limits=ModularSignLimits(max_table_entries=3), work=work)
    with pytest.raises(ValueError, match="factorial-table budget"):
        oracle.binomial_mod(5, 2, 2)
    assert work.primes_constructed == 0
    assert work.factorial_entries == 0
    assert work.retained_items == 0


def test_transient_table_retention_is_preflighted_before_allocation() -> None:
    work = ModularSignWork()
    oracle = ModularSignOracle(
        limits=ModularSignLimits(max_retained_items=8), work=work
    )
    with pytest.raises(ValueError, match="retention budget"):
        oracle.binomial_mod(5, 2, 2)
    assert work.primes_constructed == 0
    assert work.factorial_entries == 0
    assert work.retained_items == 0


def test_failed_table_request_preserves_cache_until_explicit_clear() -> None:
    work = ModularSignWork()
    oracle = ModularSignOracle(
        limits=ModularSignLimits(max_retained_items=12), work=work
    )
    assert oracle.binomial_mod(5, 1, 2) == comb(5, 1) % 2
    assert work.retained_items == 5
    with pytest.raises(ValueError, match="retention budget"):
        oracle.binomial_mod(5, 1, 3)
    assert work.retained_items == 5
    assert oracle.binomial_mod(5, 1, 2) == comb(5, 1) % 2

    oracle.clear()
    assert work.retained_items == 0
    oracle.close()
    assert work.retained_items == 0


def test_small_binomial_reduces_before_the_third_residue_product() -> None:
    # For p=7, two residues fit the seven-bit precharge; three unrestricted
    # residue factors would require a larger intermediate than this limit.
    oracle = ModularSignOracle(limits=ModularSignLimits(max_integer_bits=7))
    assert oracle.binomial_mod(6, 3, 7) == comb(6, 3) % 7


def test_input_and_lucas_digit_budgets_fail_closed() -> None:
    with pytest.raises(TypeError, match="integer pairs"):
        ModularSignOracle().sign(3, ((0, 1.5),), 1, bound=3)  # type: ignore[arg-type]
    oracle = ModularSignOracle(limits=ModularSignLimits(max_lucas_digits=1))
    with pytest.raises(ValueError, match="Lucas-digit budget"):
        oracle.sign(10**20, ((0, 1),), 1, bound=1)

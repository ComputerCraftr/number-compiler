"""Independent C1 2-adic return saturation regressions."""

from __future__ import annotations

from math import gcd

import pytest

from number_compiler.sequences.comma.carry_generator import C1Phase, C1Return
from tests.sequences.comma.c1_reconstruction_oracle import (
    c1_entry_return_residue,
    c1_saturation_summary,
)


@pytest.mark.parametrize(
    ("leading", "suffix", "period"),
    [(3, 0, 200), (6, 1, 400), (7, 0, 800), (1, 0, 1600)],
)
def test_adaptive_period_matches_the_production_closed_carry_action(
    leading: int, suffix: int, period: int
) -> None:
    summary = c1_saturation_summary(leading, suffix)
    assert summary.return_period == period
    source = C1Phase.from_suffix(leading, suffix)
    for steps in (0, 1, 49, 51):
        first = C1Return(source, steps)
        shifted = C1Return(source, steps + period)
        assert first.target == shifted.target
        assert (shifted.count - first.count) % 32 == 0


def test_c1_924_shift_has_q5_q6_exceptions_then_saturates() -> None:
    before = c1_saturation_summary(1, 0)
    cases = (
        (5, 24),
        (6, 16),
        (7, 0),
        (8, 0),
        (50, 0),
        (929, 0),
        (100_000, 0),
        (1_000_000, 0),
    )
    for width, expected_delta in cases:
        first = c1_entry_return_residue(1, 0, width, before)
        shifted = c1_entry_return_residue(1, 0, width + 924, before)
        assert first.target_suffix == shifted.target_suffix
        assert (shifted.carry_mod_32 - first.carry_mod_32) % 32 == expected_delta
        if width < 7:
            continue
        representative = 7 + (width - 7) % 924
        canonical = c1_entry_return_residue(1, 0, representative, before)
        assert (first.target_suffix, first.carry_mod_32) == (
            shifted.target_suffix,
            shifted.carry_mod_32,
        )
        assert (first.target_suffix, first.carry_mod_32) == (
            canonical.target_suffix,
            canonical.carry_mod_32,
        )


@pytest.mark.validation
def test_adaptive_c1_monodromy_periods_cover_all_891_phases() -> None:
    observed_periods: set[int] = set()
    for leading in range(1, 10):
        for suffix in range(99):
            summary = c1_saturation_summary(leading, suffix)
            assert summary.displacement == (
                2 * summary.cycle_length * summary.carry_count_50
            )
            assert summary.return_period == 50 * (32 // gcd(32, summary.carry_count_50))
            return_blocks = summary.return_period // 50
            assert return_blocks * summary.carry_count_50 % 32 == 0
            assert all(
                blocks * summary.carry_count_50 % 32 != 0
                for blocks in range(1, return_blocks)
            )
            observed_periods.add(summary.return_period)
    assert observed_periods == {200, 400, 800, 1600}


@pytest.mark.validation
def test_924_shift_saturation_over_18711_phase_width_pairs() -> None:
    widths = (*range(5, 25), 1_000_000)
    checked = 0
    for leading in range(1, 10):
        for suffix in range(99):
            summary = c1_saturation_summary(leading, suffix)
            for width in widths:
                first = c1_entry_return_residue(leading, suffix, width, summary)
                shifted = c1_entry_return_residue(leading, suffix, width + 924, summary)
                expected_delta = (-pow(10, width - 2, 32)) % 32
                assert first.target_suffix == shifted.target_suffix
                assert (shifted.carry_mod_32 - first.carry_mod_32) % 32 == (
                    expected_delta
                )
                if width >= 7:
                    # The returned step residue is an internal representative;
                    # endpoint and carry residue are the saturated observation.
                    assert first.carry_mod_32 == shifted.carry_mod_32
                checked += 1
    assert checked == 18_711

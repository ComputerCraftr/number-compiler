"""Bounded independent checks of the formal fractional-safety certificates.

Direct real-rational multiplication is independent of the ceiling source
recurrence used to construct the certified interval bounds. Isabelle, not
these samples, supplies the universal statements.
"""

import re
from fractions import Fraction
from pathlib import Path

import pytest

from devtools.paths import isabelle_root

THEORY = (
    isabelle_root(Path(__file__).resolve().parents[3])
    / "mahler_safety/Generated_Mahler_Safety.thy"
)
INTERVALS = {
    int(residue): (Fraction(lower.strip("()")), Fraction(upper.strip("()")))
    for residue, lower, upper in re.findall(
        r'shows "safe_prefix 6 \((\d+)\+t\) \\<longleftrightarrow> '
        r'\((\S+) \\<le> t \\<and> t < (\S+)\)"',
        THEORY.read_text(),
    )
}


def _safe(value: Fraction, steps: int) -> bool:
    for _ in range(steps + 1):
        if value - value.numerator // value.denominator >= Fraction(1, 2):
            return False
        value *= Fraction(3, 2)
    return True


def test_certificate_inventory_and_survivors() -> None:
    assert set(INTERVALS) == set(range(64))
    assert {r for r, (lo, hi) in INTERVALS.items() if lo < hi} == {
        0,
        4,
        6,
        9,
        13,
        14,
        16,
        20,
        21,
        24,
        30,
        32,
        37,
        45,
        46,
        52,
        53,
        56,
    }


@pytest.mark.parametrize("residue", range(64))
def test_interval_endpoints_and_high_fibers(residue: int) -> None:
    lower, upper = INTERVALS[residue]
    epsilon = Fraction(1, 2**20)
    samples = {
        Fraction(0),
        Fraction(1, 2) - epsilon,
        lower - epsilon,
        lower,
        lower + epsilon,
        upper - epsilon,
        upper,
        upper + epsilon,
        (lower + upper) / 2,
    }
    for fraction in samples:
        if 0 <= fraction < Fraction(1, 2):
            for high in (0, 1, 63, 2**80 + 1):
                assert _safe(residue + 64 * high + fraction, 6) == (
                    lower <= fraction < upper
                )


def test_fractional_failure_does_not_mean_ledger_failure() -> None:
    assert not _safe(Fraction(7), 2)
    value, ledger = 8, 0
    observed = [ledger]
    for _ in range(2):
        ledger += 2 if value % 2 == 0 else -1
        value += value // 2
        observed.append(ledger)
    assert observed == [0, 2, 4]

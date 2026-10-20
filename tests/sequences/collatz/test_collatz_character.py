from __future__ import annotations

from typing import Never, cast

import pytest

from number_compiler.api.number_api import NumberCompiler
from number_compiler.arithmetic.automata.program_word import (
    CanonicalWord,
    from_runs,
    from_values,
)
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.sequences.collatz.character import (
    CollatzGrowthCharacter,
    CollatzRadialCharacter,
    collatz_character_period,
    collatz_growth_character_value,
    collatz_growth_character_word,
    collatz_radial_character_value,
    collatz_radial_character_word,
)
from number_compiler.sequences.collatz.raw_field import (
    CollatzSentinelBoundarySummary,
    summarize_collatz_sentinel_boundaries,
)


@pytest.mark.validation  # Exhaustive growth-character check across 5,000 odd sources.
def test_chi4_decides_accelerated_growth_without_valuation_state() -> None:
    for n in range(1, 10000, 2):
        char = collatz_growth_character_value(n)
        k = v2_positive(3 * n + 1)
        target = (3 * n + 1) >> k
        assert char.symbol == (1 if n % 4 == 1 else -1)
        assert char.increases == (k == 1) == (target > n)
        assert char.nonincreasing == (k >= 2)
        assert char.description_bits == 1


@pytest.mark.validation  # Exhaustive 6,000-source power-of-four radix differential.
def test_power4_word_growth_character_uses_only_low_source_residue() -> None:
    for base in (4, 16, 64):
        for n in range(1, 4000, 2):
            word = from_values(digits_lsd(n, base))
            assert collatz_growth_character_word(
                word, base=base
            ) == collatz_growth_character_value(n)


def test_sentinel_growth_projection_does_not_call_full_valuation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError(
            "full valuation was acquired for a one-bit growth observer"
        )

    monkeypatch.setattr(CollatzSentinelBoundarySummary, "power4_valuation", forbidden)
    for n in range(1, 1000, 2):
        summary = summarize_collatz_sentinel_boundaries(digits_lsd(n, 4), base=4)
        expected = n % 4 == 3
        assert summary.accelerated_increases(base=4) == expected
        assert summary.accelerated_nonincreasing(base=4) == (not expected)
        assert summary.accelerated_growth_character(base=4) == (-1 if expected else 1)


@pytest.mark.validation  # Exhaustive 52,500 source/radix/order character checks.
def test_radial_character_projects_only_required_phase_from_compressed_word() -> None:
    for base in (4, 16, 64):
        for n in range(1, 5000, 2):
            word = from_values(digits_lsd(n, base))
            k = v2_positive(3 * n + 1)
            for order in (1, 2, 3, 4, 5, 8, 13):
                char = collatz_radial_character_word(word, order, base=base)
                assert char.shift == k % order
                assert char.lane_exponent() == (-k) % order
                assert char.lane_exponent(3) == (-3 * k) % order
                assert collatz_radial_character_value(n, order) == char


def test_radial_character_skips_huge_sentinel_runs_without_full_k_or_successor() -> (
    None
):
    # In base four, a run of q sentinel digits contributes 2*q to the valuation.
    # The final low-to-high digit 3 has local valuation one.  The observer keeps
    # only the requested residue, even when q itself is enormous.
    q = 10**12 + 123
    word = from_runs(((1, q), (3, 1)))
    for order in (3, 5, 8, 13, 257):
        char = collatz_radial_character_word(word, order, base=4)
        assert char.shift == (2 * q + 1) % order
        assert char.description_bits < 2 * order.bit_length() + 4
        assert collatz_character_period(order, base=4) == order // __import__(
            "math"
        ).gcd(order, 2)


def test_radial_character_composes_as_cyclic_character_not_valuation_history() -> None:
    a = CollatzRadialCharacter(13, 10**30 + 5)
    b = CollatzRadialCharacter(13, 10**40 + 9)
    c = a.then(b)
    assert c.shift == (a.shift + b.shift) % 13
    assert c.canonical_key == ("collatz-radial-character", 13, c.shift)
    with pytest.raises(ValueError):
        a.then(CollatzRadialCharacter(7, 1))


def test_character_types_reject_nonsemantic_inputs() -> None:
    with pytest.raises(ValueError):
        CollatzGrowthCharacter(0)
    with pytest.raises(ValueError):
        collatz_growth_character_value(2)
    with pytest.raises(ValueError):
        CollatzRadialCharacter(0, 0)
    with pytest.raises(ValueError):
        collatz_radial_character_word(from_runs(((1, 1),)), 0)
    with pytest.raises(TypeError):
        CollatzGrowthCharacter(True)
    with pytest.raises(TypeError):
        CollatzRadialCharacter(True, 0)
    with pytest.raises(TypeError):
        CollatzRadialCharacter(4, cast("int", 1.0))


@pytest.mark.validation  # Public API differential across 500 odd sources and orders.
def test_number_api_character_queries_bypass_orbit_and_root_germ() -> None:
    from number_compiler.api import number_api

    # The public nth-state module no longer imports any orbit builder at all.
    assert not hasattr(number_api, "collatz_orbit_formulas")
    compiler = NumberCompiler()
    for n in range(1, 1000, 2):
        growth = compiler.project_collatz_growth(n)
        assert growth.increases == (n % 4 == 3)
        for order in (3, 5, 8):
            phase = compiler.project_collatz_radial_character(n, order)
            assert phase.shift == v2_positive(3 * n + 1) % order


def test_multiple_character_orders_share_one_lcm_projection(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.sequences.collatz.character as module

    word = from_runs(((1, 10**9 + 7), (3, 1)))
    calls = 0
    original = module.collatz_radial_character_word

    def counted(
        word: CanonicalWord, order: int, *, base: int = 4
    ) -> CollatzRadialCharacter:
        nonlocal calls
        calls += 1
        return original(word, order, base=base)

    monkeypatch.setattr(module, "collatz_radial_character_word", counted)
    chars = module.collatz_radial_characters_word(word, (2, 4, 8, 5), base=4)
    assert calls == 1
    full_k = 2 * (10**9 + 7) + 1
    assert [char.shift for char in chars] == [full_k % m for m in (2, 4, 8, 5)]
    master = CollatzRadialCharacter(40, full_k)
    assert master.quotient(8).shift == full_k % 8
    with pytest.raises(ValueError):
        master.quotient(6)

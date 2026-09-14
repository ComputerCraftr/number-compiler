from __future__ import annotations

import random

import pytest

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.sequences.collatz.raw_field import (
    CollatzRawDigitField,
    accelerated_collatz_sentinel_step,
    accelerated_collatz_sentinel_step_digits,
    collatz_sentinel_digit,
    collatz_sentinel_orbit,
    power4_radix_bits,
)


def _v2(n: int) -> int:
    return (n & -n).bit_length() - 1


def _value(digits: tuple[int, ...], base: int) -> int:
    return sum(int(d) * base**i for i, d in enumerate(digits))


def test_power4_sentinel_digits_are_exact_repeated_minus_one_third_residues() -> None:
    for base, bits, sentinel in ((4, 2, 1), (16, 4, 5), (64, 6, 21), (256, 8, 85)):
        assert power4_radix_bits(base) == bits
        assert collatz_sentinel_digit(base) == sentinel
        for width in range(1, 7):
            residue = sum(sentinel * base**i for i in range(width))
            assert 3 * residue + 1 == base**width
    for bad in (2, 8, 10, 32):
        with pytest.raises(ValueError):
            power4_radix_bits(bad)


def test_two_sided_sentinel_summary_subsumes_old_first_hole_summary() -> None:
    from number_compiler.sequences.collatz.raw_field import (
        CollatzSentinelBoundarySummary,
        summarize_collatz_sentinel_boundaries,
    )

    base = 16
    sentinel = collatz_sentinel_digit(base)
    digits = (sentinel, sentinel, 7, sentinel, 3)
    whole = summarize_collatz_sentinel_boundaries(digits, base=base)
    assert whole.low_first_mismatch == 2
    assert whole.low_mismatch_digit == 7
    atoms = [CollatzSentinelBoundarySummary.atom(d, sentinel) for d in digits]
    left = atoms[0].then(atoms[1]).then(atoms[2]).then(atoms[3]).then(atoms[4])
    right = atoms[0].then(atoms[1].then(atoms[2].then(atoms[3].then(atoms[4]))))
    assert left == right == whole


def test_decimal_zero_to_28_raw_field_is_canonical_and_carry_vector_free() -> None:
    field = CollatzRawDigitField.from_odd_value(999_999, base=10)
    assert field.max_component == 28
    assert field.represented_value() == 3 * 999_999 + 1
    assert field.source_value() == 999_999
    normal = field.normalized_digits()
    assert _value(normal, 10) == 3 * 999_999 + 1
    # The retained dataclass has no source-digit, carry-vector, or output-digit fields.
    assert set(field.__dataclass_fields__) == {"base", "coefficients"}


@pytest.mark.validation  # Four-radix by 500-source exact valuation differential.
def test_power4_raw_symbols_synthesize_exact_valuation_without_normalizing() -> None:
    rng = random.Random(0xC011A72)
    for base in (4, 16, 64, 256):
        for _ in range(500):
            n = rng.randrange(1, 1 << 60) | 1
            field = CollatzRawDigitField.from_odd_value(n, base=base)
            assert field.sentinel_valuation() == _v2(3 * n + 1)


@pytest.mark.validation  # Four-radix by 500-source full accelerated-step differential.
def test_sentinel_step_matches_accelerated_collatz_without_carry_vector() -> None:
    rng = random.Random(0x5E471E1)
    for base in (4, 16, 64, 256):
        for _ in range(500):
            n = rng.randrange(1, 1 << 56) | 1
            step = accelerated_collatz_sentinel_step(n, base=base)
            v = _v2(3 * n + 1)
            target = (3 * n + 1) >> v
            assert step.valuation == v
            assert _value(step.target_digits, base) == target
            assert step.increases == (v == 1)
            assert step.nonincreasing == (v >= 2)
            assert step.scalar_carry_peak <= 2


def test_sentinel_step_accepts_digits_directly_and_strips_full_radix_runs() -> None:
    for base in (4, 16, 64):
        D = collatz_sentinel_digit(base)
        # q sentinel digits followed by x != D.
        for q in range(6):
            x = (D + 2) % base
            if x == D:
                x = (x + 1) % base
            digits = (D,) * q + (x, 2, 1)
            # Ensure source is odd. D is odd and q>0; when q=0 choose odd x.
            if q == 0 and not (digits[0] & 1):
                digits = (x ^ 1,) + digits[1:]
                if digits[0] == D:
                    digits = ((digits[0] + 2) % base,) + digits[1:]
            n = _value(digits, base)
            if not (n & 1):
                continue
            step = accelerated_collatz_sentinel_step_digits(digits, base=base)
            assert step.stripped_digits == q
            assert step.valuation == _v2(3 * n + 1)
            assert _value(step.target_digits, base) == (3 * n + 1) >> step.valuation


def test_seed27_sentinel_orbits_are_exact_and_need_tiny_first_hole_projection() -> None:
    for base in (4, 16, 64, 256):
        steps = collatz_sentinel_orbit(27, base=base)
        assert len(steps) == 41
        assert sum(s.valuation for s in steps) == 70
        assert _value(steps[-1].target_digits, base) == 1
        # At radix 16+ seed 27 never needs to inspect more than two full radix
        # symbols to locate each valuation boundary; at radix 64+ one suffices.
        max_inspected = max(s.stripped_digits + 1 for s in steps)
        if base == 16:
            assert max_inspected <= 2
        if base >= 64:
            assert max_inspected == 1


def test_general_sentinel_boundary_summary_synthesizes_decimal_growth_and_radix_factor_run() -> (
    None
):
    from number_compiler.sequences.collatz.raw_field import (
        affine_sentinel_digit,
        summarize_collatz_sentinel_boundaries,
    )

    assert affine_sentinel_digit(10) == 3
    # Exact width threshold: d-digit n grows under 3*n+1 iff n >= 33..3.
    for n in range(10, 100):
        digits = digits_lsd(n, 10)
        summary = summarize_collatz_sentinel_boundaries(digits, base=10)
        assert summary.digit_growth == (3 * n + 1 >= 100)
    # Decimal raw symbols expose trailing factors of 10 as 10,9,9,...
    for n, q in ((7, 0), (13, 1), (33, 2), (1333, 3), (73333, 4)):
        if not (n & 1):
            continue
        field = CollatzRawDigitField.from_odd_value(n, base=10)
        assert field.sentinel_radix_factor_run() == q
        assert (3 * n + 1) % (10**q) == 0
        if q:
            assert (3 * n + 1) // (10**q) == 3 * (n // (10**q)) + 1
        assert field.boundary_summary().digit_growth == field.digit_growth


def test_two_sided_sentinel_summary_is_associative() -> None:
    from number_compiler.sequences.collatz.raw_field import (
        CollatzSentinelBoundarySummary,
        affine_sentinel_digit,
        summarize_collatz_sentinel_boundaries,
    )

    base = 16
    D = affine_sentinel_digit(base)
    digits = (D, D, 2, D, 12, D)
    atoms = [CollatzSentinelBoundarySummary.atom(d, D) for d in digits]
    left = CollatzSentinelBoundarySummary.identity()
    for atom in atoms:
        left = left.then(atom)
    whole = summarize_collatz_sentinel_boundaries(digits, base=base)
    assert left == whole
    assert whole.low_first_mismatch == 2
    # Most significant non-D digit is 12 > 5.
    assert whole.high_relation == 1
    assert whole.digit_growth


def test_sentinel_summary_powers_over_huge_rle_runs_without_digit_expansion() -> None:
    from number_compiler.arithmetic.automata.program_word import from_runs, word_metrics
    from number_compiler.sequences.collatz.raw_field import (
        summarize_collatz_sentinel_word,
    )

    base = 16
    D = collatz_sentinel_digit(base)
    word = from_runs(((D, 1_000_000), (7, 1), (D, 1_000_000)))
    metrics = word_metrics(word)
    summary = summarize_collatz_sentinel_word(word, base=base)
    assert metrics["runs"] == 3
    assert metrics["nodes"] < 16
    assert summary.length == 2_000_001
    assert summary.low_first_mismatch == 1_000_000
    assert summary.low_mismatch_digit == 7
    assert summary.power4_valuation(base=base) == 4_000_001
    assert summary.high_relation == 1  # most-significant non-D run digit is 7 > 5


@pytest.mark.validation  # Four-radix by 500-source two-sided growth differential.
def test_two_sided_summary_replaces_terminal_carry_growth_scan_randomized() -> None:
    import random

    from number_compiler.sequences.collatz.raw_field import (
        summarize_collatz_sentinel_boundaries,
    )

    rng = random.Random(0xB0A7D)
    for base in (4, 10, 16, 64):
        for _ in range(500):
            width = rng.randrange(1, 10)
            lo = base ** (width - 1)
            hi = base**width
            n = rng.randrange(lo, hi) | 1
            if n >= hi:
                n -= 2
            field = CollatzRawDigitField.from_odd_value(n, base=base)
            digits = field.source_digits()
            summary = summarize_collatz_sentinel_boundaries(digits, base=base)
            assert summary.digit_growth == (3 * n + 1 >= base ** len(digits))
            assert summary.digit_growth == field.digit_growth


@pytest.mark.validation  # Eight complete accelerated orbits of up to 128 events.
def test_power4_sentinel_formula_path_is_exact_but_not_required_as_primary_backend() -> (
    None
):
    from number_compiler.arithmetic.fields.digit_formula import DigitSpec, root_to_int
    from number_compiler.sequences.collatz.raw_field import (
        collatz_orbit_formulas_sentinel_power4,
    )

    for seed in (3, 7, 27, 97):
        for base in (4, 16):
            arena, rows = collatz_orbit_formulas_sentinel_power4(
                seed, radix=base, max_odd_steps=128, materialize_values=False
            )
            values = [root_to_int(arena, row.root, DigitSpec(base)) for row in rows]
            reference = [seed]
            n = seed
            while n > 1 and not (n & 1):
                n >>= 1
            reference = [n]
            for _ in range(127):
                if n == 1:
                    break
                m = 3 * n + 1
                v = _v2(m)
                n = m >> v
                reference.append(n)
            assert values == reference


@pytest.mark.validation  # Exhaustive radix-four summary over 2,500 odd sources.
def test_radix4_sentinel_summary_synthesizes_accelerated_growth_phase_from_lsd() -> (
    None
):
    from number_compiler.sequences.collatz.raw_field import (
        summarize_collatz_sentinel_boundaries,
    )

    # Every positive odd base-4 source starts in digit 1 or 3.  Digit 3 gives
    # valuation one (strict growth); digit 1 begins a sentinel run and gives
    # valuation at least two (nonincrease, equality only at the fixed point 1).
    for n in range(1, 5000, 2):
        summary = summarize_collatz_sentinel_boundaries(digits_lsd(n, 4), base=4)
        m = 3 * n + 1
        v = _v2(m)
        assert summary.power4_valuation(base=4) == v
        assert summary.accelerated_increases(base=4) == (v == 1)
        assert summary.accelerated_nonincreasing(base=4) == (v >= 2)
        assert (digits_lsd(n, 4)[0] == 3) == (v == 1)

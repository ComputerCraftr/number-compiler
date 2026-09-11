"""Dead root prefixes preserve angular actions and surviving occurrence words."""

from dataclasses import fields

from number_compiler.arithmetic.automata.program_word import from_values
from number_compiler.arithmetic.carry.collatz_output_quotient import radix64_domain
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.arithmetic.fields.two_adic import v2_nonzero
from number_compiler.sequences.collatz.hensel_occurrence import CollatzHenselAction
from number_compiler.sequences.collatz.root_germs import (
    PadicAngularBoundaryGerm,
    RationalPadicRootGerm,
    RationalPadicRootMismatch,
)


def test_six_root_clocks_settle_in_one_radix64_digit_within_domain() -> None:
    expected = (
        (4, 28, 4, 28),
        (5, 35, 5, 35),
        (7, 49, 7, 49),
        (11, 13, 2, 14),
        (19, 5, 1, 7),
        (35, 53, 8, 56),
    )
    for e, (c, d, settled, next_digit) in enumerate(expected):
        root = RationalPadicRootGerm(2, 3 + (1 << e))
        assert root.constant == c and root.root_residue(6) == d
        after = RationalPadicRootGerm(2, (9 * d + c) // 64)
        assert (after.constant, after.root_residue(6)) == (settled, next_digit)
        assert (9 * next_digit + settled) // 64 == settled
        assert radix64_domain(d) == radix64_domain(next_digit)


def test_h2_angular_unit_phase_is_a_derived_matching_quarter_clock() -> None:
    units = frozenset((1, 2, 4, 5, 7, 8))
    for residual_shift in range(6):
        root = RationalPadicRootGerm(2, 3 + (1 << residual_shift))
        phase = root.constant % 9
        assert phase in units
        matched, advanced, remaining = root.normalize_matching_prefix_word(
            from_values((root.radix4_digit,))
        )
        assert matched == 1 and remaining.length == 0
        assert advanced.constant % 9 == 7 * phase % 9

    # The six-state observer is not exact root identity: different lifts can
    # demand different next radix-four symbols.
    first = RationalPadicRootGerm(2, 1)
    lifted = RationalPadicRootGerm(2, 10)
    assert first.constant % 9 == lifted.constant % 9 == 1
    assert first.radix4_digit != lifted.radix4_digit
    assert first.canonical_key != lifted.canonical_key

    # The unit clock alone is not a general mismatch detector: integer lifts
    # of one phase can expose different next radix-four root digits.
    first, lifted = RationalPadicRootGerm(2, 1), RationalPadicRootGerm(2, 10)
    assert first.constant % 9 == lifted.constant % 9
    assert first.radix4_digit != lifted.radix4_digit


def test_h2_unit_clock_has_exact_three_quarter_radix64_cycle() -> None:
    expected_symbols = {1: 7, 2: 14, 4: 28, 5: 35, 7: 49, 8: 56}
    for constant, expected_symbol in expected_symbols.items():
        current = RationalPadicRootGerm(2, constant)
        digits = []
        for _ in range(3):
            digit = current.radix4_digit
            digits.append(digit)
            matched, current, remaining = current.normalize_matching_prefix_word(
                from_values((digit,))
            )
            assert matched == 1 and remaining.length == 0
        assert current == RationalPadicRootGerm(2, constant)
        assert sum(digit * 4**index for index, digit in enumerate(digits)) == (
            expected_symbol
        )


def test_mismatch_retains_only_independent_event_coordinates() -> None:
    assert tuple(field.name for field in fields(RationalPadicRootMismatch)) == (
        "denominator_power",
        "matched_quarters",
        "source_digit",
        "constant_at_mismatch",
    )
    for h in range(1, 7):
        root = RationalPadicRootGerm(h, 1 + 2 * h)
        digit = (root.radix4_digit + 1) % 4
        mismatch, _suffix = root.first_mismatch_word(from_values((digit,)))
        expected_root = (-mismatch.constant_at_mismatch * pow(3**h, -1, 4)) % 4
        assert mismatch.root_digit == expected_root
        assert mismatch.digit_v2 == v2_nonzero(digit - expected_root)
        assert (
            mismatch.constant_after_root_digit
            == (mismatch.constant_at_mismatch + 3**h * expected_root) // 4
        )


def test_angular_multiplier_is_derived_from_residual_phase() -> None:
    assert tuple(field.name for field in fields(PadicAngularBoundaryGerm)) == (
        "denominator_power",
        "valuation",
        "offset",
    )
    for e in range(6):
        root = RationalPadicRootGerm(2, 3 + (1 << e))
        for digit in range(4):
            if digit == root.radix4_digit:
                continue
            mismatch, _suffix = root.first_mismatch_word(from_values((digit,)))
            angular = PadicAngularBoundaryGerm.from_mismatch(root, mismatch)
            assert angular.residual_phase == angular.valuation % 2
            assert angular.multiplier == 36 >> angular.residual_phase
            same_angular = PadicAngularBoundaryGerm(
                angular.denominator_power,
                angular.valuation + 2,
                angular.offset,
            )
            action = CollatzHenselAction(
                2 - angular.residual_phase,
                angular.denominator_power,
                angular.offset,
            )
            same_action = CollatzHenselAction(
                2 - same_angular.residual_phase,
                same_angular.denominator_power,
                same_angular.offset,
            )
            assert same_action.canonical_key == action.canonical_key
            assert same_angular.canonical_key != angular.canonical_key
    for denominator_power in range(1, 7):
        root = RationalPadicRootGerm(denominator_power, 1 + 2 * denominator_power)
        digit = (root.radix4_digit + 1) % 4
        mismatch, _suffix = root.first_mismatch_word(from_values((digit,)))
        angular = PadicAngularBoundaryGerm.from_mismatch(root, mismatch)
        assert angular.multiplier == (4 * 3**denominator_power) >> mismatch.digit_v2


def test_matching_radix64_prefixes_are_weight_not_live_action_identity() -> None:
    for e in range(6):
        root = RationalPadicRootGerm(2, 3 + (1 << e))
        fixed = RationalPadicRootGerm(
            2, (root.constant + 9 * root.root_residue(6)) // 64
        )
        mismatch_digit = (fixed.radix4_digit + 1) % 4
        tail = mismatch_digit + 4 * 6
        images = []
        for chunks in range(1, 5):
            quarters = 3 * chunks
            source = root.root_residue(6 * chunks) + (tail << (6 * chunks))
            word = from_values(digits_lsd(source, 4))
            dropped, normalized, remaining = root.normalize_matching_prefix_word(word)
            assert dropped == quarters and normalized == fixed
            original_mismatch, original_suffix = root.first_mismatch_word(word)
            mismatch, suffix = normalized.first_mismatch_word(remaining)
            angular = PadicAngularBoundaryGerm.from_mismatch(normalized, mismatch)
            assert (
                original_mismatch.valuation_bits
                == 2 * dropped + mismatch.valuation_bits
            )
            assert original_suffix is suffix
            images.append(
                (
                    normalized,
                    remaining.node_id,
                    angular.multiplier,
                    angular.offset,
                    suffix.node_id,
                )
            )
        assert len(set(images)) == 1

"""Dead root prefixes preserve angular actions and surviving occurrence words."""

from collections.abc import Iterator
from dataclasses import fields, replace

import pytest

import number_compiler.sequences.collatz.root_germs as root_module
from number_compiler.arithmetic.automata import program_word
from number_compiler.arithmetic.automata.program_word import (
    CanonicalWord,
    SourceWord,
    SourceWordSuffix,
    concat,
    drop_source_prefix,
    from_runs,
    from_values,
    iter_runs,
    source_word_key,
    validate_source_word,
)
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
        digits: list[int] = []
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
        _unused_root_binding, digit, mismatch = _nonmatching_digit(h)
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
        root, digit, mismatch = _nonmatching_digit(denominator_power)
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
        images: list[tuple[RationalPadicRootGerm, int, int, int, int]] = []
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


@pytest.mark.parametrize("prefix", (0, 10**12))
@pytest.mark.parametrize("irregular", (False, True))
def test_first_hole_stops_run_iteration_and_preserves_suffix(
    monkeypatch: pytest.MonkeyPatch, prefix: int, irregular: bool
) -> None:
    symbols: list[int] = []
    state, last = 991, 1
    for _ in range(4096):
        state = (1103515245 * state + 12345) & 0x7FFFFFFF
        last = (
            (((state >> 11) % 3) + last + 1) % 4
            if irregular
            else 5 - last
            if last in (2, 3)
            else 2
        )
        symbols.append(last)
    high = from_values(symbols)
    source = concat(from_runs(((1, prefix), (0, 1))), high)
    root = RationalPadicRootGerm(1, 1)
    visits = 0

    def bounded_runs(word: SourceWord) -> Iterator[tuple[int, int]]:
        nonlocal visits
        for item in iter_runs(word):
            visits += 1
            if visits > 1 + bool(prefix):
                raise AssertionError("first-hole search read past its mismatch")
            yield item

    def forbidden_normalization(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("first-hole cursor rebalanced the high suffix")

    monkeypatch.setattr(program_word, "_word_tasks", forbidden_normalization)
    monkeypatch.setattr(root_module, "iter_runs", bounded_runs)
    mismatch, suffix = root.first_mismatch_word(source)
    assert mismatch.matched_quarters == prefix
    assert mismatch.valuation_bits == 2 * prefix
    assert isinstance(suffix, SourceWordSuffix)
    assert suffix.source is source and suffix.start == prefix + 1
    assert len(suffix.parts) <= source.run_count.bit_length()
    assert tuple(iter_runs(suffix)) == tuple(iter_runs(high))
    visits = 0
    dropped, normalized, remaining = root.normalize_matching_prefix_word(source)
    assert dropped == prefix and normalized == root
    assert tuple(iter_runs(remaining)) == ((0, 1), *tuple(iter_runs(high)))


def _irregular_word(count: int) -> CanonicalWord:
    state, last = 991, 1
    symbols: list[int] = []
    for _ in range(count):
        state = (1103515245 * state + 12345) & 0x7FFFFFFF
        last = (((state >> 11) % 3) + last + 1) % 4
        symbols.append(last)
    return from_values(symbols)


@pytest.mark.parametrize("count", (128, 512, 2048))
def test_irregular_first_hole_constructs_only_boundary_cover(
    count: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    source = concat(from_runs(((1, 10**12), (0, 7))), _irregular_word(count))
    checked = 0
    original = program_word.validate_word

    def counted(word: CanonicalWord) -> None:
        nonlocal checked
        checked += 1
        original(word)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("source suffix performed canonical rebalance")

    monkeypatch.setattr(program_word, "validate_word", counted)
    monkeypatch.setattr(program_word, "_word_tasks", forbidden)
    mismatch, suffix = RationalPadicRootGerm(1, 1).first_mismatch_word(source)
    assert mismatch.matched_quarters == 10**12
    assert isinstance(suffix, SourceWordSuffix)
    assert suffix.source is source and suffix.start == 10**12 + 1
    assert checked <= 8 * source.run_count.bit_length()
    assert len(suffix.parts) <= source.run_count.bit_length()
    assert next(iter_runs(suffix)) == (0, 6)


def test_source_suffix_authority_and_memo_reset_are_independent(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = _irregular_word(128)
    suffix = drop_source_prefix(source, 1)
    assert isinstance(suffix, SourceWordSuffix)
    key = source_word_key(suffix)
    forged = replace(suffix, start=2, length=suffix.length - 1)
    with pytest.raises(ValueError, match="foreign or stale"):
        validate_source_word(forged)
    foreign = replace(suffix, source=_irregular_word(129), length=128)
    with pytest.raises(ValueError, match="foreign or stale"):
        validate_source_word(foreign)
    program_word.clear_transient_program_word_caches()
    monkeypatch.setattr(program_word, "SUFFIX_MEMO_LIMIT", 2)
    retained = [drop_source_prefix(source, offset) for offset in range(2, 6)]
    assert [word.length for word in retained] == [
        source.length - offset for offset in range(2, 6)
    ]
    assert len(program_word.program_word_cache_snapshot().suffixes) == 2
    for word in retained:
        validate_source_word(word)
    validate_source_word(suffix)
    program_word.clear_transient_program_word_caches()
    validate_source_word(suffix)
    reissued = drop_source_prefix(source, 1)
    assert reissued is not suffix and source_word_key(reissued) == key
    assert len(program_word.program_word_cache_snapshot().suffixes) <= 2


def test_partial_source_suffix_counts_retained_nodes_and_integer_splits() -> None:
    source = concat(from_runs(((0, 7),)), _irregular_word(128))
    suffix = drop_source_prefix(source, 1)
    assert isinstance(suffix, SourceWordSuffix)
    before = program_word.word_metrics(source)
    retained = program_word.word_metrics(suffix)
    # One issued cursor and its new partial-run node remain live alongside
    # the original source; existing cover subtrees are counted only once.
    assert retained["nodes"] == before["nodes"] + 2
    assert retained["references"] == before["references"] + 1 + len(suffix.parts)
    value = 0
    place = 1
    for digit, length in iter_runs(suffix):
        value += digit * (4**length - 1) // 3 * place
        place *= 4**length
    metrics = program_word.RunTraversalMetrics()
    actual = list(
        program_word.iter_run_blocks_reverse(
            suffix, value, symbol_bits=2, metrics=metrics
        )
    )
    assert [(digit, length) for digit, length, _block in actual] == list(
        reversed(tuple(iter_runs(suffix)))
    )
    assert metrics.visited_nodes >= len(suffix.parts)
    assert metrics.visited_block_bits >= 2 * suffix.length


def test_nine_carry_reentry_is_the_existing_root_pullback() -> None:
    # First non-1 digit of 9*M+c is the first hole of 27*M+3*c+1.
    # The returned suffix remains a source occurrence, not the emitted image.
    for source in range(257):
        word = from_values(digits_lsd(source, 4))
        for carry in range(9):
            mismatch, suffix = RationalPadicRootGerm(
                3, 3 * carry + 1
            ).first_mismatch_word(word)
            output = 9 * source + carry
            prefix = 0
            tail = output
            while tail % 4 == 1:
                prefix += 1
                tail //= 4
            assert mismatch.matched_quarters == prefix
            assert mismatch.valuation_bits == v2_nonzero(3 * output + 1)
            assert mismatch.constant_at_mismatch % 3 == 1
            port = (mismatch.constant_at_mismatch - 1) // 3
            assert 0 <= port < 9
            outgoing, emitted = divmod(9 * mismatch.source_digit + port, 4)
            assert emitted == tail % 4 and emitted != 1
            assert 0 <= outgoing < 9
            high = source >> (2 * (prefix + 1))
            # A finite source may retain a leading zero; numerical semantics,
            # not source-word identity, establishes this affine suffix lift.
            actual_digits = [
                digit for digit, count in iter_runs(suffix) for _ in range(count)
            ]
            assert sum(digit * 4**i for i, digit in enumerate(actual_digits)) == high
            assert 9 * high + outgoing == output >> (2 * (prefix + 1))


def _nonmatching_digit(
    h: int,
) -> tuple[RationalPadicRootGerm, int, RationalPadicRootMismatch]:
    root = RationalPadicRootGerm(h, 1 + 2 * h)
    digit = (root.radix4_digit + 1) % 4
    mismatch, _suffix = root.first_mismatch_word(from_values((digit,)))
    return root, digit, mismatch

"""Independent literal checks for finite MSB-first Pascal word summaries."""

from __future__ import annotations

from math import comb

import pytest

from number_compiler.arithmetic.automata.pascal_word_moments import (
    PascalWordMoments,
    pascal_cyclotomic_repeat_period,
)


def literal_moments(
    word: tuple[int, ...], *, order: int, modulus: int
) -> tuple[tuple[int, ...], tuple[int, ...]]:
    digits = tuple(
        sum(
            (-1 if index & 1 else 1) * comb(index, degree) * value
            for index, value in enumerate(word)
        )
        % modulus
        for degree in range(order + 1)
    )
    markers = tuple(
        sum(
            (-1 if index & 1 else 1) * comb(index, degree) * int(value >= 5)
            for index, value in enumerate(word)
        )
        % modulus
        for degree in range(order + 1)
    )
    return digits, markers


def literal_summary(
    word: tuple[int, ...], *, order: int, modulus: int
) -> PascalWordMoments:
    digits, markers = literal_moments(word, order=order, modulus=modulus)
    return PascalWordMoments(
        len(word),
        modulus,
        digits,
        markers,
        None if not word else int(word[0] >= 5),
        None if not word else int(word[-1] >= 5),
    )


@pytest.mark.parametrize(
    "left,right",
    [
        ((1, 9, 2), (8, 4, 7, 3)),
        ((), (9, 1, 8)),
        ((4, 2, 7), ()),
        ((0, 9, 1, 8, 2), (7, 3)),
    ],
)
@pytest.mark.parametrize("order", (0, 1, 3, 7))
def test_pascal_join_and_reflection_match_nonsymmetric_literal_words(
    left: tuple[int, ...], right: tuple[int, ...], order: int
) -> None:
    modulus = 11
    first = literal_summary(left, order=order, modulus=modulus)
    second = literal_summary(right, order=order, modulus=modulus)
    joined = first.then(second)
    assert joined == literal_summary(left + right, order=order, modulus=modulus)
    assert first.reflected() == literal_summary(
        tuple(reversed(left)), order=order, modulus=modulus
    )


@pytest.mark.parametrize("count", (0, 1, 2, 5, 9))
@pytest.mark.parametrize("order", (0, 1, 4, 8))
def test_pascal_binary_power_matches_literal_repeat_including_high_orders(
    count: int, order: int
) -> None:
    word = (1, 9, 2, 8, 4, 7, 3)
    summary = literal_summary(word, order=order, modulus=11)
    assert summary.power(count) == literal_summary(
        word * count, order=order, modulus=11
    )


def test_pascal_record_rejects_unaligned_or_non_normalized_vectors() -> None:
    with pytest.raises(ValueError, match="aligned"):
        PascalWordMoments(1, 11, (1, 2), (1,), 0, 0)
    with pytest.raises(ValueError, match="normalized"):
        PascalWordMoments(1, 11, (11,), (0,), 0, 0)
    with pytest.raises(ValueError, match="outside the finite word"):
        PascalWordMoments(1, 11, (1, 2), (0, 0), 0, 0)
    with pytest.raises(ValueError, match="one marker"):
        PascalWordMoments(1, 11, (1,), (0,), 0, 1)


def test_marker_is_independent_of_digits_and_composite_moduli_are_exact() -> None:
    digits = (-2, 5, 7)
    markers = (1, 0, 1)
    order, modulus = 4, 12
    result = PascalWordMoments.empty(order, modulus)
    for digit, marker in zip(digits, markers, strict=True):
        result = result.then(
            PascalWordMoments.symbol(digit, marker, order=order, modulus=modulus)
        )
    for values, moments in (
        (digits, result.digit_moments),
        (markers, result.marker_moments),
    ):
        assert moments == tuple(
            sum((-1) ** i * comb(i, r) * value for i, value in enumerate(values))
            % modulus
            for r in range(order + 1)
        )
    assert result.first_marker == result.last_marker == 1
    assert result.reflected().reflected() == result
    with pytest.raises(TypeError, match="exact integers"):
        PascalWordMoments.symbol(True, 0, order=order, modulus=modulus)
    with pytest.raises(ValueError, match="aligned"):
        PascalWordMoments(1, 11, (0,) * 34, (0,) * 34, 0, 0)


@pytest.mark.parametrize(
    "order,period", ((0, 22), (1, 242), (10, 242), (11, 2662), (32, 2662))
)
def test_f11_spatial_repeat_period_retains_exact_width_and_endmarkers(
    order: int, period: int
) -> None:
    word = (1, 9, 2, 8, 4, 7, 3)
    summary = literal_summary(word, order=order, modulus=11)
    assert summary.cyclotomic_repeat_period == period
    assert pascal_cyclotomic_repeat_period(order) == period

    full_cycle = summary.power(period)
    shifted_cycle = summary.power(period + 3)
    short = summary.power(3)
    assert full_cycle.length == len(word) * period
    assert full_cycle.digit_moments == (0,) * (order + 1)
    assert full_cycle.marker_moments == (0,) * (order + 1)
    assert shifted_cycle.length == len(word) * (period + 3)
    assert shifted_cycle.digit_moments == short.digit_moments
    assert shifted_cycle.marker_moments == short.marker_moments
    assert (shifted_cycle.first_marker, shifted_cycle.last_marker) == (0, 0)
    assert full_cycle.first_marker == full_cycle.last_marker == 0

    empty = summary.power(0)
    assert empty.length == 0
    assert empty.first_marker is None and empty.last_marker is None


@pytest.mark.parametrize("word,order", (((8,), 0), ((3, 8), 1), ((3, 8), 11)))
def test_period_reduction_matches_independent_literal_across_wrap(
    word: tuple[int, ...], order: int
) -> None:
    count = pascal_cyclotomic_repeat_period(order) + 3
    summary = literal_summary(word, order=order, modulus=11)

    assert summary.power(count) == literal_summary(
        word * count, order=order, modulus=11
    )


def test_huge_f11_repeat_uses_bounded_lucas_digits_and_period_products(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.arithmetic.automata.pascal_word_moments as module

    order = 18
    length = 11**24 + 1729
    huge_count = 10**80 + 918273645
    digit_moments = tuple((3 * index + 1) % 11 for index in range(order + 1))
    marker_moments = tuple((7 * index + 2) % 11 for index in range(order + 1))
    summary = PascalWordMoments(
        length,
        11,
        digit_moments,
        marker_moments,
        1,
        0,
    )
    sign = -1 if length & 1 else 1
    expected_joined_digits = tuple(
        (
            digit_moments[degree]
            + sign
            * sum(
                comb(length, degree - right_degree) * digit_moments[right_degree]
                for right_degree in range(degree + 1)
            )
        )
        % 11
        for degree in range(order + 1)
    )
    last_index = length - 1
    expected_reflected_digits = tuple(
        (
            (-1 if last_index & 1 else 1)
            * sum(
                (-1 if source_degree & 1 else 1)
                * comb(last_index - source_degree, degree - source_degree)
                * digit_moments[source_degree]
                for source_degree in range(degree + 1)
            )
        )
        % 11
        for degree in range(order + 1)
    )
    assert summary.then(summary).digit_moments == expected_joined_digits
    assert summary.reflected().digit_moments == expected_reflected_digits

    original_comb = comb
    comb_upper_arguments: list[int] = []

    def bounded_comb(n: int, k: int) -> int:
        comb_upper_arguments.append(n)
        if n > 10:
            raise AssertionError("Lucas join used an unbounded binomial upper argument")
        return original_comb(n, k)

    original_then = PascalWordMoments.then
    products = 0
    period = pascal_cyclotomic_repeat_period(order)
    maximum_intermediate_length = length * period

    def bounded_then(
        first: PascalWordMoments, later: PascalWordMoments
    ) -> PascalWordMoments:
        nonlocal products
        products += 1
        if (
            first.length > maximum_intermediate_length
            or later.length > maximum_intermediate_length
        ):
            raise AssertionError("repeat composition expanded the huge requested count")
        return original_then(first, later)

    monkeypatch.setattr(module, "comb", bounded_comb)
    monkeypatch.setattr(PascalWordMoments, "then", bounded_then)
    result = summary.power(huge_count)
    reduced = summary.power(huge_count % period)

    assert result.length == length * huge_count
    assert (result.first_marker, result.last_marker) == (1, 0)
    assert result.digit_moments == reduced.digit_moments
    assert result.marker_moments == reduced.marker_moments
    assert comb_upper_arguments and max(comb_upper_arguments) <= 10
    assert products < 64


def test_composite_modulus_keeps_exact_binary_repeat_path() -> None:
    summary = PascalWordMoments.empty(3, 12)
    for digit, marker in ((4, 0), (9, 1), (2, 0)):
        summary = summary.then(
            PascalWordMoments.symbol(digit, marker, order=3, modulus=12)
        )
    assert summary.cyclotomic_repeat_period is None
    assert summary.power(8) == literal_summary((4, 9, 2) * 8, order=3, modulus=12)

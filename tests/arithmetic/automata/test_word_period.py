"""Finite period searches agree with independent exhaustive definitions."""

from itertools import product
from typing import cast

import pytest

from number_compiler.arithmetic.automata.word_period import (
    finite_suffix_period,
    primitive_period,
)


def test_period_search_matches_all_short_binary_words() -> None:
    for size in range(9):
        for word in product((0, 1), repeat=size):
            expected = next(
                (
                    p
                    for p in range(1, size + 1)
                    if size % p == 0
                    and all(word[i] == word[i % p] for i in range(size))
                ),
                0,
            )
            period, comparisons = primitive_period(word)
            assert period == expected
            assert comparisons <= 2 * size
            for repeats in (2, 3):
                suffix = next(
                    (
                        (start, p)
                        for p in range(1, size // repeats + 1)
                        for start in range(size - repeats * p + 1)
                        if all(
                            word[i] == word[start + (i - start) % p]
                            for i in range(start, size)
                        )
                    ),
                    None,
                )
                found, comparisons = finite_suffix_period(word, min_repeats=repeats)
                assert found == suffix
                assert comparisons <= 2 * size


def test_large_finite_suffix_has_linear_symbol_comparisons() -> None:
    word = tuple(range(32)) + (1, 2, 3) * 4000 + (1, 2)
    found, comparisons = finite_suffix_period(word)
    assert found == (32, 3)
    assert comparisons < 2 * len(word)
    assert primitive_period((1, 2, 3) * 4000)[0] == 3


@pytest.mark.parametrize("repeats", [True, 0, 1, 2.5])
def test_suffix_search_rejects_invalid_repeat_requirement(repeats: object) -> None:
    with pytest.raises(ValueError, match="at least two"):
        finite_suffix_period((1, 2), min_repeats=cast(int, repeats))

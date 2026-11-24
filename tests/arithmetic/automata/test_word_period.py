"""Finite period searches agree with independent exhaustive definitions."""

from itertools import product
from typing import cast

import pytest

from number_compiler.arithmetic.automata.word_period import (
    canonical_primitive_rotation,
    canonical_primitive_text_rotation,
    finite_suffix_period,
    least_rotation_index,
    primitive_period,
)


def test_guarded_primitive_rotation_preserves_complete_phases() -> None:
    for size in range(1, 7):
        for word in product(((0, 1), (0, 2), (1, 1)), repeat=size):
            canonical, phase, _ = canonical_primitive_rotation(
                word, guard_key=lambda port: port
            )
            assert (
                tuple(canonical[(phase + i) % len(canonical)] for i in range(size))
                == word
            )
            assert canonical == min(
                canonical[i:] + canonical[:i] for i in range(len(canonical))
            )
    with pytest.raises(ValueError, match="distinguish"):
        canonical_primitive_rotation(((1, 2), (1, 3)), guard_key=lambda port: port[0])
    with pytest.raises(ValueError, match="empty"):
        canonical_primitive_rotation((), guard_key=lambda port: port)


def test_text_rotation_matches_complete_port_rotation() -> None:
    for size in range(1, 9):
        for chars in product("01", repeat=size):
            word = "".join(chars)
            canonical, phase, comparisons = canonical_primitive_text_rotation(word)
            ports, other_phase, other_comparisons = canonical_primitive_rotation(
                word, guard_key=str
            )
            assert canonical == "".join(ports)
            assert (phase, comparisons) == (other_phase, other_comparisons)


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


def test_least_rotation_matches_all_short_ternary_words() -> None:
    for size in range(1, 8):
        for word in product((0, 1, 2), repeat=size):
            expected = min(
                range(size), key=lambda offset: word[offset:] + word[:offset]
            )
            assert least_rotation_index(word) == expected
    assert least_rotation_index((2, 1) * 8000) == 1
    with pytest.raises(ValueError, match="empty"):
        least_rotation_index(())

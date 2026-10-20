"""Adjacent literal candidates share scale work without skipping a child."""

from collections.abc import Callable
from typing import cast

import pytest

from number_compiler.sequences.comma import forest_verifier

_literal_children = cast(
    Callable[[int], tuple[int, ...]],
    object.__getattribute__(forest_verifier, "_literal_children"),
)
_leading_digit_scale = cast(
    Callable[[int], tuple[int, int]],
    object.__getattribute__(forest_verifier, "_leading_digit_scale"),
)


@pytest.mark.parametrize("exponent", (1, 2, 10, 100, 1000))
def test_literal_candidates_preserve_decimal_seams(exponent: int) -> None:
    scale = 10**exponent
    for leading in range(1, 11):
        for offset in (-100, -99, -10, -9, -2, -1, 0, 1, 9, 99):
            parent = leading * scale + offset
            if parent <= 0:
                continue
            expected: tuple[int, ...] = tuple(
                candidate
                for digit in range(1, 10)
                if int(str(candidate := parent + 10 * (parent % 10) + digit)[0])
                == digit
            )
            assert _literal_children(parent) == expected


def test_literal_candidates_find_the_scale_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = _leading_digit_scale
    visits = 0

    def counted(value: int) -> tuple[int, int]:
        nonlocal visits
        visits += 1
        return original(value)

    monkeypatch.setattr(forest_verifier, "_leading_digit_scale", counted)
    assert _literal_children(19_999_999_918) == (
        19_999_999_999,
        20_000_000_000,
    )
    assert visits == 1

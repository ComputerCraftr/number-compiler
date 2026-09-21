"""Quotient-only consumers must not rediscover an unused remainder."""

from typing import Never

import pytest

from number_compiler.arithmetic.fields.digit_formula import (
    DigitSpec,
    digit_root_from_int,
    root_to_int,
)
from number_compiler.arithmetic.formula.formula import FormulaArena
from number_compiler.sequences.collatz import radix


@pytest.mark.parametrize("base", (2, 4, 6, 10, 16))
def test_floor_half_does_not_request_remainder(
    base: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("quotient-only construction requested the remainder")

    monkeypatch.setattr(radix, "closed_digit_at", forbidden)
    spec = DigitSpec(base)
    for value in range(65):
        arena = FormulaArena()
        root = digit_root_from_int(value, arena, spec)
        half = radix.local_half_even_radix(arena, root, spec)
        assert root_to_int(arena, half, spec) == value // 2


@pytest.mark.parametrize("base", (2, 4, 6, 10, 16))
def test_divide_still_returns_the_actual_remainder(base: int) -> None:
    spec = DigitSpec(base)
    for value in (0, 1, base - 1, base, base + 1, base * base - 1):
        arena = FormulaArena()
        root = digit_root_from_int(value, arena, spec)
        quotient, remainder = radix.local_divide2_even_radix(arena, root, spec)
        assert (root_to_int(arena, quotient, spec), remainder) == divmod(value, 2)


def test_floor_half_preserves_even_radix_and_plane_count_checks() -> None:
    arena = FormulaArena()
    root = digit_root_from_int(7, arena, DigitSpec(4))
    with pytest.raises(ValueError, match="even radix"):
        radix.local_half_even_radix(arena, root, DigitSpec(3))
    with pytest.raises(ValueError):
        radix.local_half_even_radix(arena, root, DigitSpec(16))


@pytest.mark.parametrize("base", (4, 16, 64, 256))
def test_first_hole_valuation_justifies_every_quotient_only_division(base: int) -> None:
    sentinel = (base - 1) // 3
    bits = base.bit_length() - 1
    for first in range(base):
        if first == sentinel:
            continue
        small = 3 * first + 1
        local = (small & -small).bit_length() - 1
        assert local < bits
        for high in (0, 1, base + 1):
            suffix = first + base * high
            value = 3 * suffix + 1
            for _ in range(local):
                assert value % 2 == 0
                value //= 2
            assert value % 2 == 1
            # Appending sentinel digits changes only the full-radix part of
            # the valuation; the quotient comes from this same suffix.
            for count in (0, 1, 5):
                low = sentinel * (base**count - 1) // (base - 1)
                source = low + base**count * suffix
                assert 3 * source + 1 == value << (bits * count + local)

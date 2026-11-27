"""Differential and fail-closed tests for algebraic forcing-slab contraction."""

from collections.abc import Sequence
from math import comb
from random import Random
from typing import Never, cast

import pytest

from number_compiler.arithmetic.carry import event_memory as memory
from number_compiler.arithmetic.carry.carry_itinerary import (
    cyclic_transport_kernel,
    negacyclic_transport_kernel,
)


def _literal_fold(rows: Sequence[Sequence[int]], base: int) -> tuple[int, ...]:
    modulus = 1 << memory.pair_plane_bits(base)
    image = [0] * len(rows[0])
    for row in rows:
        if len(row) == len(image):
            image = [2 * a + b for a, b in zip(image, row, strict=True)]
        else:
            image = [
                a + b + e for a, b, e in zip(image + [0], [0] + image, row, strict=True)
            ]
        image = [v % modulus for v in image]
    return tuple(image)


def _assert_fold_matches_literal(rows: Sequence[Sequence[int]], base: int) -> None:
    expected = _literal_fold(rows, base)
    assert memory.fold_forcing_events(rows, base=base) == expected
    assert memory.fold_forcing_events(iter(rows), base=base) == expected


@pytest.mark.parametrize("base", (3, 10, 1000))
def test_signed_forcing_fold_and_stream(base: int) -> None:
    rng = Random(base)
    for _ in range(80):
        width = rng.randrange(1, 14)
        rows: list[tuple[int, ...]] = []
        for _ in range(rng.randrange(1, 35)):
            width += rng.randrange(2)
            rows.append(
                tuple(rng.randint(-2 * base, 2 * base) for _ in range(width))
                if rng.randrange(3)
                else (0,) * width
            )
        _assert_fold_matches_literal(rows, base)


@pytest.mark.parametrize("base", (10, 1000, 2**23))
def test_quiet_multiplier_never_spills_coefficient_lanes(base: int) -> None:
    bits = memory.pair_plane_bits(base)
    row = ((1 << bits) - 1, 3, 7)
    rows = [row] + [(0, 0, 0)] * (bits - 1)
    _assert_fold_matches_literal(rows, base)


def test_extinct_event_prefix_is_not_folded() -> None:
    rows = [(17, -9, 8)] * 100 + [(0, 0, 0)] * 5
    calls: list[int] = []
    assert memory.fold_forcing_events(rows, record_updates=calls.append) == (0,) * 3
    assert calls == [15]
    with pytest.raises(ValueError):
        memory.fold_forcing_events([(0,) * 4, *rows])
    with pytest.raises(ValueError):
        memory.fold_forcing_events([cast(tuple[int, ...], ("invalid", 0, 0)), *rows])


def test_zero_carry_suffix_needs_no_event_construction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    carry = [(0, 1, 0)] + [(0, 0, 0)] * 5

    def forbidden(*args: object, **kwargs: object) -> Never:
        pytest.fail("opened an extinct or identically zero forcing row")

    monkeypatch.setattr(memory, "forcing_event_from_carry", forbidden)
    assert memory.forcing_image_from_certified_carry_suffix(carry, source_width=2) == (
        0,
        0,
    )
    assert memory.forcing_image_from_certified_carry_suffix(
        iter(carry[1:]), source_width=2
    ) == (0, 0)
    with pytest.raises(ValueError, match="annihilated"):
        memory.forcing_image_from_certified_carry_suffix(carry[1:5], source_width=2)
    with pytest.raises(ValueError, match="geometry"):
        memory.forcing_image_from_certified_carry_suffix(
            [(0, 2, 0)] + carry[1:], source_width=2
        )


def test_carry_suffix_matches_physical_pair_recurrence() -> None:
    rng = Random(196)
    for _ in range(100):
        digits = tuple(rng.randrange(10) for _ in range(rng.randrange(1, 25)))
        source = tuple(a + b for a, b in zip(digits, reversed(digits), strict=True))
        width = len(source)
        carries: list[tuple[int, ...]] = []
        for _ in range(20):
            source, _, row = memory.pair_step_with_carry(source, 10)
            carries.append(row)
        assert (
            memory.forcing_image_from_certified_carry_suffix(
                carries, source_width=width
            )
            == source
        )
        assert (
            memory.forcing_image_from_certified_carry_suffix(
                iter(carries), source_width=width
            )
            == source
        )


@pytest.mark.parametrize("negative", (False, True))
def test_transport_power_matches_binomial(negative: bool) -> None:
    kernel = negacyclic_transport_kernel if negative else cyclic_transport_kernel
    for p in (1, 2, 3, 4, 7, 8):
        for q in range(6):
            for g in (0, 1, 2, 6, 17, 33):
                for modulus in (3, 16, 25, 32):
                    expected = [0] * p
                    for j in range(g + 1):
                        k, i = divmod(j, p)
                        expected[i] += (
                            (-1 if negative and k % 2 else 1) * comb(g, j) * 2**q
                        )
                    assert kernel(p, q, g, modulus=modulus) == tuple(
                        v % modulus for v in expected
                    )
    for p in (1, 2, 4, 8, 16):
        assert kernel(p, 0, 2**4096, modulus=32) == (0,) * p

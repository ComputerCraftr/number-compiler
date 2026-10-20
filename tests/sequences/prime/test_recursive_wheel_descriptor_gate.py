"""The eleven-stage wheel owns rank/select without a parent gap carrier."""

from __future__ import annotations

from collections.abc import Callable
from math import gcd
from typing import Never, cast

import pytest

from number_compiler.sequences.prime import wheel_cyclotomic as wheels


def _forbid_parent_gap_construction(monkeypatch: pytest.MonkeyPatch) -> None:
    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("recursive wheel query entered parent gap construction")

    monkeypatch.setattr(wheels, "extend_prime_wheel_gaps", forbidden)
    monkeypatch.setattr(wheels, "index_prime_wheel_extension", forbidden)
    monkeypatch.setattr(wheels.PrimeWheelExtensionIndex, "build", forbidden)
    monkeypatch.setattr(wheels.PrimeWheelExtensionIndex, "materialize_gaps", forbidden)
    monkeypatch.setattr(wheels.PrimeWheelExtensionMorphism, "from_gaps", forbidden)


def _index_for_primes(primes: tuple[int, ...]) -> wheels.PrimeRecursiveWheelIndex:
    index = wheels.PrimeRecursiveWheelIndex.from_primes((2,))
    for prime in primes:
        index = index.with_prime(prime)
    return index


def _checked_prefix(index: wheels.PrimeRecursiveWheelIndex, stop: int) -> list[int]:
    prefix: list[int] = []
    assert index.rank_before(1) == 0
    for value in range(1, stop):
        if gcd(value, index.modulus) == 1:
            prefix.append(value)
        assert index.rank_before(value + 1) == len(prefix)
    return prefix


def test_eleven_stage_rank_select_uses_only_the_prime_descriptor(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _forbid_parent_gap_construction(monkeypatch)
    cast(
        Callable[[], None],
        object.__getattribute__(
            object.__getattribute__(wheels, "_wheel_count_leq"), "cache_clear"
        ),
    )()
    try:
        index = _index_for_primes((3, 5, 7, 11, 13, 17, 19, 23, 29, 31))
        assert index.modulus == 200_560_490_130
        assert index.length == 30_656_102_400
        # The unit check covers a bounded prefix and retains the far-select,
        # parent-gap poison, and periodic-boundary work at the full index size.
        prefix = _checked_prefix(index, 101)
        assert len(prefix) == 15
        for rank in (0, 1, 7, len(prefix) // 2, len(prefix) - 1):
            assert index.residue_at(rank) == prefix[rank]
            assert index.rank_before(prefix[rank]) == rank
        rank_100_residue = index.residue_at(100)
        assert gcd(rank_100_residue, index.modulus) == 1
        assert index.rank_before(rank_100_residue) == 100
        assert index.rank_before(rank_100_residue + 1) == 101
        # Far selects use the same rank owner, without any gap output.
        for rank in (index.length // 2, index.length - 1):
            residue = index.residue_at(rank)
            assert gcd(residue, index.modulus) == 1
            assert index.rank_before(residue) == rank
            assert index.rank_before(residue + 1) == rank + 1
        assert index.count_positive_below(1_000_001) == 152_840
        # Periodic rank retains the strict-boundary convention beyond one wheel.
        assert index.count_positive_below(index.modulus + 1_000_001) == (
            index.length + 152_840
        )
    finally:
        cast(
            Callable[[], None],
            object.__getattribute__(
                object.__getattribute__(wheels, "_wheel_count_leq"), "cache_clear"
            ),
        )()


@pytest.mark.validation  # Exhaustive 10,000-coordinate differential on the full wheel.
def test_eleven_stage_rank_matches_the_exhaustive_prefix(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _forbid_parent_gap_construction(monkeypatch)
    cast(
        Callable[[], None],
        object.__getattribute__(
            object.__getattribute__(wheels, "_wheel_count_leq"), "cache_clear"
        ),
    )()
    try:
        index = _index_for_primes((3, 5, 7, 11, 13, 17, 19, 23, 29, 31))
        prefix = _checked_prefix(index, 10_001)
        assert len(prefix) == 1517
        for rank in (0, 1, 7, 100, len(prefix) // 2, len(prefix) - 1):
            assert index.residue_at(rank) == prefix[rank]
            assert index.rank_before(prefix[rank]) == rank
    finally:
        cast(
            Callable[[], None],
            object.__getattribute__(
                object.__getattribute__(wheels, "_wheel_count_leq"), "cache_clear"
            ),
        )()

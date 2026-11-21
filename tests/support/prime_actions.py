"""Typed internal observations for prime authority and cleanup regressions."""

from __future__ import annotations

from math import isqrt
from typing import cast

from number_compiler.resources.owned_memo import OwnedMemo
from number_compiler.resources.stores import LedgerList
from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG
from number_compiler.sequences.prime.partial_successor_image import (
    PrimePartialSuccessorQuery,
)
from number_compiler.sequences.prime.successor_action import PrimeSuccessorActionArena


def primes_through(limit: int) -> tuple[int, ...]:
    """Independent bounded sieve for prime successor and rank comparisons."""
    flags = bytearray(b"\x01") * (limit + 1)
    if limit >= 0:
        flags[0] = 0
    if limit >= 1:
        flags[1] = 0
    for candidate in range(2, isqrt(limit) + 1):
        if flags[candidate]:
            flags[candidate * candidate : limit + 1 : candidate] = b"\x00" * (
                (limit - candidate * candidate) // candidate + 1
            )
    return tuple(value for value in range(2, limit + 1) if flags[value])


def prime_factor_store(rank: CoprimeRankDAG) -> LedgerList[int]:
    """Read the exact issued store for append-only authority tests."""
    return cast(LedgerList[int], object.__getattribute__(rank, "_primes"))


def corrupt_prime_factor(rank: CoprimeRankDAG, index: int, value: int) -> None:
    """Bypass the store gate deliberately to test stale source detection."""
    values = cast(list[int], object.__getattribute__(prime_factor_store(rank), "_data"))
    values[index] = value


def prime_inverse_workspace(rank: CoprimeRankDAG) -> OwnedMemo[int, int]:
    return cast(
        OwnedMemo[int, int], object.__getattribute__(rank, "_progression_inverses")
    )


def partial_prime_arena(
    query: PrimePartialSuccessorQuery,
) -> PrimeSuccessorActionArena | None:
    return cast(
        PrimeSuccessorActionArena | None, object.__getattribute__(query, "_arena")
    )

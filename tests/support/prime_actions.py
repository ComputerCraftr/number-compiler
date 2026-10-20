"""Typed internal observations for prime authority and cleanup regressions."""

from __future__ import annotations

from typing import cast

from number_compiler.resources.owned_memo import OwnedMemo
from number_compiler.resources.stores import LedgerList
from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG
from number_compiler.sequences.prime.partial_successor_image import (
    PrimePartialSuccessorQuery,
)
from number_compiler.sequences.prime.successor_action import PrimeSuccessorActionArena


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

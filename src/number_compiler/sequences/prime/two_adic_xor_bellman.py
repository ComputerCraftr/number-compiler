"""Source-certified 2-adic first-prime selection over a bounded interval."""

from __future__ import annotations

from dataclasses import dataclass
from math import isqrt
from typing import TYPE_CHECKING, Literal

if TYPE_CHECKING:
    from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG

PrimeBellmanMode = Literal["rank", "leaf"]


@dataclass(frozen=True, slots=True)
class PrimeXorBellmanWitness:
    """The selected survivor and its first primorial XOR change."""

    candidate: int
    cancellation_depth: int
    first_changed_bit: int
    first_flip_direction: Literal["ON", "OFF"]
    modulus: int
    residue: int
    source_depth: int
    classes: int
    candidate_probes: int
    rank_queries: int
    source_low_bits: int


def _first_in_class(lower: int, modulus: int, residue: int) -> int:
    return residue + ((lower - residue + modulus - 1) // modulus) * modulus


def _candidate_is_wheel_survivor(
    rank: CoprimeRankDAG, candidate: int, depth: int
) -> bool:
    identity = rank.factor_source_identity()
    for index in range(depth):
        factor = rank.factor_at(index, identity)
        if factor * factor > candidate:
            break
        rank.charge(candidate.bit_length() + factor.bit_length())
        if candidate % factor == 0:
            return False
    return True


def first_survivor_xor_bellman(
    rank: CoprimeRankDAG,
    lower: int,
    upper: int,
    *,
    depth: int | None = None,
    mode: PrimeBellmanMode = "rank",
) -> PrimeXorBellmanWitness | None:
    """Select the least survivor in [lower, upper) from a certified prime source.

    Odd candidates partition by v2(candidate - 1). The rank branch minimizes
    their exact class ranks. The leaf branch visits the bounded odd interval
    in order and checks the same factor source.
    """
    from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG

    if type(rank) is not CoprimeRankDAG:
        raise TypeError("XOR Bellman needs the canonical prime rank owner")
    if (
        type(lower) is not int
        or type(upper) is not int
        or type(depth) not in (int, type(None))
        or lower < 3
        or upper <= lower
        or mode not in ("rank", "leaf")
    ):
        raise ValueError("invalid 2-adic Bellman interval or mode")
    if depth is None:
        depth = rank.factor_count
    rank.validate_consecutive_prefix(depth)
    identity = rank.factor_source_identity()
    if lower <= rank.factor_at(depth - 1, identity):
        raise ValueError("2-adic prime birth must follow the admitted prefix")
    if rank.count(isqrt(upper - 1), depth) != 1:
        raise ValueError("2-adic Bellman requires a complete prime-root certificate")

    possible_classes = (upper - 2).bit_length()
    winner: int | None = None
    winning_depth = 0
    classes = probes = queries = 0
    if mode == "leaf":
        candidate = lower | 1
        while candidate < upper:
            rank.charge(candidate.bit_length())
            probes += 1
            if _candidate_is_wheel_survivor(rank, candidate, depth):
                winner = candidate
                winning_depth = ((candidate - 1) & -(candidate - 1)).bit_length() - 1
                break
            candidate += 2
    for phase in range(1, possible_classes + 1):
        rank.charge(phase + 2 + lower.bit_length())
        modulus = 1 << (phase + 1)
        residue = (1 << phase) + 1
        first = _first_in_class(lower, modulus, residue)
        if first >= upper:
            continue
        classes += 1
        if mode == "leaf" or (winner is not None and first >= winner):
            continue
        high = min(upper - 1, winner - 1 if winner is not None else upper - 1)
        baseline = rank.count_progression(lower - 1, modulus, residue, depth)
        total = rank.count_progression(high, modulus, residue, depth)
        queries += 2
        if total == baseline:
            continue
        left, right = 0, (high - first) // modulus
        while left < right:
            middle = (left + right) // 2
            present = rank.count_progression(
                first + middle * modulus, modulus, residue, depth
            )
            queries += 1
            if present > baseline:
                right = middle
            else:
                left = middle + 1
        winner, winning_depth = first + left * modulus, phase
        probes += 1

    if winner is None:
        return None
    if not rank.is_current_factor_source(identity):
        raise RuntimeError("XOR Bellman lost its certified prime source")
    first_changed_bit = winning_depth + 1
    mask = (1 << (first_changed_bit + 1)) - 1
    source = 1
    for index in range(depth):
        factor = rank.factor_at(index, identity)
        rank.charge(factor.bit_length() + mask.bit_length())
        source = (source * factor) & mask
    return PrimeXorBellmanWitness(
        candidate=winner,
        cancellation_depth=winning_depth,
        first_changed_bit=first_changed_bit,
        first_flip_direction="OFF" if source & (1 << first_changed_bit) else "ON",
        modulus=1 << (winning_depth + 1),
        residue=1 + (1 << winning_depth),
        source_depth=depth,
        classes=classes,
        candidate_probes=probes,
        rank_queries=queries,
        source_low_bits=source,
    )

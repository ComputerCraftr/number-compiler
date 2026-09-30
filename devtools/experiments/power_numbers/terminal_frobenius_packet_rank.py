"""Rank obstruction for linear terminal Frobenius coefficient packets.

The production chunk quotient asks only for one folded coefficient, but a
natural next attempt is to propagate a fixed-dimensional linear
invariant/anti-invariant packet for powers of ``1+X``.  This module records why
that cannot be the missing asymptotic extractor.

For power-of-two ``M``, put ``A=Q[X]/(X^M+1)`` and let ``L`` be multiplication
by ``1+X``.  Since ``X^M+1=Phi_(2M)(X)`` is irreducible, ``1+X`` has minimal
polynomial ``(Y-1)^M+1`` of degree M.  The source 1 is cyclic under L (the
vectors ``(1+X)^j``, 0<=j<M, are triangular in the monomial basis), and the
coefficient-of-X functional has nonzero weight on every eigenvalue
``1+omega``.  Consequently that scalar sequence has exact linear recurrence /
Hankel rank M over characteristic zero.

Thus a linear packet for this coefficient necessarily grows with the
cyclotomic degree.  At the square-root prime-decision threshold M is already
roughly sqrt(N), so the final extractor must use genuinely nonlinear arithmetic
(nonunits/gcds, a special reciprocity descent, etc.), not a fixed linear/Fitting
packet.
"""

from __future__ import annotations

from dataclasses import dataclass
from devtools.verification.fraction_linear_algebra import fraction_matrix_rank

from number_compiler.sequences.power_numbers.terminal_threshold import (
    terminal_threshold_spec,
)


@dataclass(frozen=True, slots=True)
class FrobeniusLinearPacketRankAudit:
    family: str
    parameter: int
    decision_required_local_v2: int
    folded_degree_log2: int
    exact_linear_rank: int
    rank_description_bits: int
    bounded_dimension_possible: bool
    proof: str


def terminal_linear_packet_rank_audit(
    family: str, parameter: int
) -> FrobeniusLinearPacketRankAudit:
    spec = terminal_threshold_spec(str(family), int(parameter))
    v = spec.prime_decision_required_local_v2
    if v < 1:
        raise ValueError(v)
    # The r-level fold lives in X^M+1 with M=2^(v-1).  Keep the large rank as
    # an integer descriptor; no M-dimensional matrix/polynomial is built.
    degree_log2 = v - 1
    rank = 1 << degree_log2
    return FrobeniusLinearPacketRankAudit(
        spec.family,
        spec.parameter,
        v,
        degree_log2,
        rank,
        max(1, rank.bit_length()),
        False,
        (
            "X^M+1=Phi_(2M) is irreducible; multiplication by 1+X has minimal "
            "polynomial (Y-1)^M+1; source 1 is cyclic and [X] is observable, "
            "so the scalar coefficient sequence has exact Hankel rank M"
        ),
    )


def _fold_negacyclic(values: list[int], M: int) -> tuple[int, ...]:
    out = [0] * M
    for degree, value in enumerate(values):
        block, index = divmod(degree, M)
        out[index] += -value if block & 1 else value
    return tuple(out)


def folded_x_sequence(M: int, terms: int) -> tuple[int, ...]:
    """Small exact integer differential for [X](1+X)^e mod X^M+1."""
    M, terms = int(M), int(terms)
    if M < 2 or M & (M - 1) or terms < 1:
        raise ValueError((M, terms))
    state = (1,) + (0,) * (M - 1)
    out: list[int] = []
    for _ in range(terms):
        out.append(state[1])
        raw = [0] * (M + 1)
        for j, value in enumerate(state):
            raw[j] += value
            raw[j + 1] += value
        state = _fold_negacyclic(raw, M)
    return tuple(out)


def _matrix_rank_fraction(matrix: list[list[int]]) -> int:
    return fraction_matrix_rank(matrix)


def small_hankel_rank_differential(M: int) -> int:
    """Materialize only tiny M controls and verify the structural rank theorem."""
    M = int(M)
    seq = folded_x_sequence(M, 2 * M + 1)
    hankel = [[seq[i + j] for j in range(M)] for i in range(M)]
    return _matrix_rank_fraction(hankel)


__all__ = [name for name in globals() if not name.startswith("_")]

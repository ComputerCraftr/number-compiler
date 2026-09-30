"""Small exact rational linear algebra helpers shared by bounded audits."""

from __future__ import annotations

from collections.abc import Sequence
from fractions import Fraction


def fraction_matrix_rank(matrix: Sequence[Sequence[int]]) -> int:
    """Return the exact row rank of an integer matrix over the rationals."""
    if not matrix:
        return 0
    rows = [[Fraction(value) for value in row] for row in matrix]
    row_count, column_count = len(rows), len(rows[0])
    rank = column = 0
    while rank < row_count and column < column_count:
        pivot = next(
            (index for index in range(rank, row_count) if rows[index][column]), None
        )
        if pivot is None:
            column += 1
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        divisor = rows[rank][column]
        rows[rank] = [value / divisor for value in rows[rank]]
        for index in range(row_count):
            if index == rank or not rows[index][column]:
                continue
            factor = rows[index][column]
            rows[index] = [
                value - factor * pivot_value
                for value, pivot_value in zip(rows[index], rows[rank], strict=True)
            ]
        rank += 1
        column += 1
    return rank

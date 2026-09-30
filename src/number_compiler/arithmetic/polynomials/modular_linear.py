"""Canonical iterative Gaussian elimination over a prime coefficient field."""

from __future__ import annotations

from collections.abc import Sequence


def row_reduce_mod_prime(
    matrix: Sequence[Sequence[int]], prime: int
) -> tuple[list[list[int]], tuple[int, ...]]:
    """Return reduced rows and pivot columns, preserving deterministic first pivots."""
    p = int(prime)
    rows = [[int(value) % p for value in row] for row in matrix]
    width = len(rows[0]) if rows else 0
    if any(len(row) != width for row in rows):
        raise ValueError("ragged matrix")
    pivots: list[int] = []
    rank = 0
    for column in range(width):
        pivot = next(
            (index for index in range(rank, len(rows)) if rows[index][column]), None
        )
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        inverse = pow(rows[rank][column], -1, p)
        rows[rank] = [(value * inverse) % p for value in rows[rank]]
        for index, row in enumerate(rows):
            if index == rank or not row[column]:
                continue
            factor = row[column]
            rows[index] = [
                (left - factor * right) % p
                for left, right in zip(row, rows[rank], strict=True)
            ]
        pivots.append(column)
        rank += 1
        if rank == len(rows):
            break
    return rows, tuple(pivots)

"""Small exact min-plus/tropical normalization utilities for powered residuals.

Tropical signatures are compiler prefilters only: an exact residual/function
identity must still justify every merge.  The purpose of this module is to push
additive potentials out of state-local observations before Myhill--Nerode
refinement so equivalent weighted behavior is not distinguished by placement of
a common offset.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass

from number_compiler.arithmetic.automata.guard import record_tropical_op
from number_compiler.arithmetic.fields.morphism_core import binary_power

INF: int | None = None


def normalize_vector(values: Sequence[int | None]) -> tuple[int | None, ...]:
    """Projective min-plus normalization by the minimum finite potential."""
    vals = tuple(None if x is None else int(x) for x in values)
    finite = [x for x in vals if x is not None]
    if not finite:
        return vals
    m = min(finite)
    record_tropical_op(len(vals))
    return tuple(None if x is None else x - m for x in vals)


@dataclass(frozen=True, slots=True)
class TropicalMatrix:
    rows: tuple[tuple[int | None, ...], ...]

    def __post_init__(self) -> None:
        rows = tuple(
            tuple(None if x is None else int(x) for x in row) for row in self.rows
        )
        if not rows or not rows[0] or any(len(row) != len(rows[0]) for row in rows):
            raise ValueError("nonempty rectangular tropical matrix required")
        object.__setattr__(self, "rows", rows)

    @property
    def shape(self) -> tuple[int, int]:
        return len(self.rows), len(self.rows[0])

    @classmethod
    def identity(cls, n: int) -> TropicalMatrix:
        n = int(n)
        if n <= 0:
            raise ValueError(n)
        return cls(
            tuple(tuple(0 if i == j else None for j in range(n)) for i in range(n))
        )

    def compose(self, other: TropicalMatrix) -> TropicalMatrix:
        """Min-plus product ``self * other``."""
        m, k = self.shape
        k2, n = other.shape
        if k != k2:
            raise ValueError((self.shape, other.shape))
        out: list[tuple[int | None, ...]] = []
        for i in range(m):
            row: list[int | None] = []
            for j in range(n):
                best = None
                for h in range(k):
                    a, b = self.rows[i][h], other.rows[h][j]
                    if a is None or b is None:
                        continue
                    z = a + b
                    record_tropical_op()
                    if best is None or z < best:
                        best = z
                row.append(best)
            out.append(tuple(row))
        return TropicalMatrix(tuple(out))

    def power(self, exponent: int) -> TropicalMatrix:
        exponent = int(exponent)
        n, m = self.shape
        if n != m or exponent < 0:
            raise ValueError((self.shape, exponent))
        return binary_power(
            self,
            exponent,
            identity=TropicalMatrix.identity(n),
            compose=TropicalMatrix.compose,
        ).value

    def projective_signature(self) -> tuple[tuple[int | None, ...], ...]:
        """Normalize every row by its minimum finite entry."""
        return tuple(normalize_vector(row) for row in self.rows)

    def upper_triangular_signature(self) -> tuple[object, ...]:
        """Exact normalized signature for an upper-triangular matrix.

        The caller may use this as a fast identity prefilter.  Non-upper entries
        are checked rather than silently dropped.
        """
        n, m = self.shape
        if n != m:
            raise ValueError(self.shape)
        for i in range(n):
            for j in range(i):
                if self.rows[i][j] is not None:
                    raise ValueError("matrix is not upper triangular")
        return self.projective_signature()


__all__ = ["INF", "TropicalMatrix", "normalize_vector"]

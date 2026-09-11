"""Port-valued primary-jet responses with an external spatial clock.

An endpoint carry function is a projection of these rows, never a second
stored domain ID. Equality is extensional for this emission consumer; it is
not equality of spatial occurrences or a nonlinear temporal successor law.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.polynomials.primary_jet import _poly_add, _poly_mul


@dataclass(frozen=True, slots=True)
class JetPortRow:
    outgoing: int
    jet: tuple[int, ...]

    def __post_init__(self) -> None:
        if type(self.outgoing) is not int or self.outgoing < 0:
            raise ValueError("jet response needs a nonnegative exact port")
        if (
            type(self.jet) is not tuple
            or not self.jet
            or any(type(v) is not int or v < 0 for v in self.jet)
        ):
            raise ValueError("jet response needs canonical immutable coefficients")


@dataclass(frozen=True, slots=True)
class JetPortCylinder:
    """A phase-neutral function ``c -> (exit(c), emission(c))``."""

    modulus: int
    rows: tuple[JetPortRow, ...]

    def __post_init__(self) -> None:
        if type(self.modulus) is not int or self.modulus <= 1:
            raise ValueError("jet cylinder modulus must exceed one")
        if (
            type(self.rows) is not tuple
            or not self.rows
            or any(type(row) is not JetPortRow for row in self.rows)
        ):
            raise ValueError("jet cylinder requires immutable port rows")
        degree = len(self.rows[0].jet)
        if any(
            row.outgoing >= len(self.rows)
            or len(row.jet) != degree
            or any(v >= self.modulus for v in row.jet)
            for row in self.rows
        ):
            raise ValueError("jet cylinder escapes its port or coefficient algebra")

    @property
    def outputs(self) -> tuple[int, ...]:
        return tuple(row.outgoing for row in self.rows)

    @property
    def degree(self) -> int:
        return len(self.rows[0].jet)

    @classmethod
    def identity(
        cls, ports: int, *, degree: int = 5, modulus: int = 32
    ) -> JetPortCylinder:
        if (
            type(ports) is not int
            or ports <= 0
            or type(degree) is not int
            or degree <= 0
        ):
            raise ValueError("jet cylinder needs positive exact dimensions")
        return cls(modulus, tuple(JetPortRow(c, (0,) * degree) for c in range(ports)))

    def then(self, after: JetPortCylinder, shift: tuple[int, ...]) -> JetPortCylinder:
        """Substitute ports, translate the right emission, then reduce.

        ``shift`` is supplied by the left occurrence's clock. No predecessor
        word, carry tape, width or clock provenance enters cylinder identity.
        """
        if type(after) is not JetPortCylinder or (
            self.modulus,
            self.degree,
            len(self.rows),
        ) != (after.modulus, after.degree, len(after.rows)):
            raise ValueError("jet cylinder composition requires the same algebra")
        if (
            type(shift) is not tuple
            or len(shift) != self.degree
            or any(type(v) is not int or not 0 <= v < self.modulus for v in shift)
        ):
            raise ValueError("jet cylinder shift belongs to another algebra")
        rows = []
        for first in self.rows:
            second = after.rows[first.outgoing]
            rows.append(
                JetPortRow(
                    second.outgoing,
                    _poly_add(
                        first.jet,
                        _poly_mul(shift, second.jet, self.modulus),
                        self.modulus,
                    ),
                )
            )
        return JetPortCylinder(self.modulus, tuple(rows))

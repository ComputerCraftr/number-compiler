"""Exact upper-triangular temporal moment algebra.

The law composes duration ``D`` and innovations ``U,V`` as
``(D1,U1,V1) then (D2,U2,V2) =
 (D1+D2,U1+U2,V1+V2+D2*U1)``. It is an arithmetic identity only; it does
not certify that a physical process follows either interval.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.fields.morphism_core import binary_power


def _require_int(value: int, description: str, minimum: int = 0) -> None:
    if type(value) is not int or value < minimum:
        raise ValueError(f"{description} must be an integer >= {minimum}")


@dataclass(frozen=True, slots=True)
class SkewMoment:
    """Formal matrix ``[[1,D,V],[0,1,U],[0,0,1]]``.

    Coefficients may be reduced modulo ``modulus``. This algebra is a formal
    composition rule and does not authenticate any process or source interval.
    """

    duration: int
    U: int
    V: int
    modulus: int | None = None

    def __post_init__(self) -> None:
        _require_int(self.duration, "temporal duration")
        if type(self.U) is not int or type(self.V) is not int:
            raise TypeError("skew moments must be exact integer coefficients")
        if self.modulus is not None:
            _require_int(self.modulus, "moment modulus", 1)
            if not 0 <= self.U < self.modulus or not 0 <= self.V < self.modulus:
                raise ValueError("modular moments must be canonical residues")
        if self.duration == 0 and (self.U or self.V):
            raise ValueError("empty temporal moment must be identity")

    @property
    def matrix(self) -> tuple[tuple[int, int, int], ...]:
        duration = self.duration
        if self.modulus is not None:
            duration %= self.modulus
        return ((1, duration, self.V), (0, 1, self.U), (0, 0, 1))

    def then(self, after: SkewMoment) -> SkewMoment:
        """Join adjacent chronological intervals; ``after`` acts second."""
        if type(after) is not SkewMoment or self.modulus != after.modulus:
            raise ValueError("skew actions require a matching coefficient ring")
        modulus = self.modulus
        u = self.U + after.U
        v = self.V + after.V + after.duration * self.U
        if modulus is not None:
            u %= modulus
            v %= modulus
        return SkewMoment(self.duration + after.duration, u, v, modulus)

    def square_formal(self) -> SkewMoment:
        """Square the matrix, not a physical return certificate."""
        return self.then(self)

    def power_formal(self, exponent: int) -> SkewMoment:
        """Exponentiate in logarithmically many matrix products."""
        _require_int(exponent, "formal exponent")
        return binary_power(
            self,
            exponent,
            identity=SkewMoment(0, 0, 0, self.modulus),
            compose=lambda first, second: first.then(second),
        ).value

    def apply(self, source: int, source_reverse: int) -> tuple[int, int]:
        """Evaluate the formal matrix on supplied initial coordinates."""
        if type(source) is not int or type(source_reverse) is not int:
            raise TypeError("numeric matrix arguments must be exact integers")
        endpoint = source + self.duration * source_reverse + self.V
        reverse_endpoint = source_reverse + self.U
        if self.modulus is None:
            return endpoint, reverse_endpoint
        return endpoint % self.modulus, reverse_endpoint % self.modulus


__all__ = ["SkewMoment"]

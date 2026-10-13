"""Source-qualified arithmetic for the demanded Collatz innovation observer.

The observer records the initial second innovation as either an ordered
subtraction borrow or a magnitude-addition carry, with its sign kept apart.
Its source residue does not authenticate any future branch or ActionID.
"""

from __future__ import annotations

from dataclasses import dataclass


def _positive_int(value: int, name: str, minimum: int) -> None:
    if type(value) is not int or value < minimum:
        raise ValueError(f"{name} must be integer >= {minimum}")


@dataclass(frozen=True, slots=True)
class CollatzInnovationCocycle:
    """Initial second-innovation operand residues for one authenticated source.

    A query at pivot ``m`` is admitted only when the source residue retains
    all four parity classes modulo ``4*m``. This coordinate is an observer
    input; it does not certify a temporal successor.
    """

    source_residue: int
    source_modulus: int

    def __post_init__(self) -> None:
        _positive_int(self.source_modulus, "source_modulus", 4)
        if self.source_modulus % 4:
            raise ValueError("source_modulus must preserve mod-4 parity cylinder")
        if (
            type(self.source_residue) is not int
            or not 0 <= self.source_residue < self.source_modulus
        ):
            raise ValueError("invalid source_residue")

    @property
    def source_branch4(self) -> int:
        return self.source_residue % 4

    def _operands(self, pivot: int) -> tuple[int, int, str]:
        _positive_int(pivot, "pivot", 2)
        if self.source_modulus % (4 * pivot):
            raise ValueError("source residue does not authenticate 4m")
        n = self.source_residue % (4 * pivot)
        # Preserve the subtraction orientation and the separate sign of the
        # magnitude difference; no future source is inferred from this row.
        if n % 4 == 0:
            return n // 2, n // 4, "sub"
        if n % 4 == 1:
            return (n + 1) // 2, (3 * n + 1) // 4, "add"
        if n % 4 == 2:
            return n // 2, (n + 2) // 4, "add"
        return (3 * n + 3) // 4, (n + 1) // 2, "sub"

    def kappa(self, pivot: int) -> int:
        a, b, operation = self._operands(pivot)
        if operation == "add":
            return int((a % pivot) + (b % pivot) >= pivot)
        return int((a % pivot) < (b % pivot))

    def operation(self) -> tuple[str, int]:
        if self.source_branch4 == 1:
            return "add", -1
        if self.source_branch4 == 2:
            return "add", 1
        return "sub", 1


__all__ = ["CollatzInnovationCocycle"]

"""Fermat/Mersenne digit observers after idempotent specialization."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.fields.idempotent_output import IdempotentModElement
from number_compiler.arithmetic.polynomials.digit_convolution import (
    cyclic_binary_square_add_projection,
    negacyclic_binary_square_projection,
)
from number_compiler.sequences.power_numbers.numbers import (
    FermatNumberSpec,
    MersenneNumberSpec,
)


@dataclass(frozen=True, slots=True)
class IdempotentSpecialDigitBlock:
    """Exact digit/length/carry observer for a formal special-number residue.

    Integer observers are evaluated after specialization, where radix carries
    are meaningful for the selected Fermat or Mersenne source.
    """

    family: str
    parameter: int
    value: IdempotentModElement

    def __post_init__(self) -> None:
        if self.family not in ("fermat", "mersenne"):
            raise ValueError(self.family)
        parameter = int(self.parameter)
        if parameter < 0 or (self.family == "mersenne" and parameter <= 0):
            raise ValueError(parameter)
        expected = (
            FermatNumberSpec(parameter).materialize()
            if self.family == "fermat"
            else MersenneNumberSpec(parameter).materialize()
        )
        if self.value.modulus != expected:
            raise ValueError((self.value.modulus, expected))
        object.__setattr__(self, "parameter", parameter)

    @property
    def modulus(self) -> int:
        return self.value.modulus

    @property
    def width(self) -> int:
        return (1 << self.parameter) if self.family == "fermat" else self.parameter

    @property
    def default_square_constant(self) -> int:
        return 0 if self.family == "fermat" else -2

    def specialize_idempotent(self, idempotent: int) -> int:
        return self.value.specialize_idempotent(idempotent)

    def digit_at_idempotent(self, index: int, idempotent: int) -> int:
        index = int(index)
        if index < 0:
            raise ValueError(index)
        return (self.specialize_idempotent(idempotent) >> index) & 1

    def length_at_idempotent(self, idempotent: int) -> int:
        return max(1, self.specialize_idempotent(idempotent).bit_length())

    def endpoint_digit_pair(self, index: int) -> tuple[int, int]:
        return (
            self.digit_at_idempotent(index, 0),
            self.digit_at_idempotent(index, 1),
        )

    def endpoint_length_pair(self) -> tuple[int, int]:
        return (self.length_at_idempotent(0), self.length_at_idempotent(1))

    def square_boundary_carry_at_idempotent(
        self,
        idempotent: int,
        *,
        constant: int | None = None,
    ) -> int:
        value = self.specialize_idempotent(idempotent)
        constant = self.default_square_constant if constant is None else int(constant)
        if self.family == "fermat":
            if constant != 0:
                raise ValueError(
                    "Fermat negacyclic square observer currently has constant 0"
                )
            projection = negacyclic_binary_square_projection(value, self.width)
        else:
            projection = cyclic_binary_square_add_projection(
                value, self.width, constant
            )
        return projection.normalization.boundary_in

    def endpoint_square_boundary_carries(
        self,
        *,
        constant: int | None = None,
    ) -> tuple[int, int]:
        return (
            self.square_boundary_carry_at_idempotent(0, constant=constant),
            self.square_boundary_carry_at_idempotent(1, constant=constant),
        )


__all__ = ["IdempotentSpecialDigitBlock"]

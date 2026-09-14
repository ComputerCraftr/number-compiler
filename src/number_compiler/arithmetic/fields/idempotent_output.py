"""Exact idempotent-sheet algebra for special-number digit projections.

``IdempotentModElement`` implements the rank-two algebra
``(Z/NZ)[E]/(E**2-E)`` and remains valid for nontrivial CRT idempotents.  The
cyclotomic lift reuses the canonical source-digit block componentwise.  Digit,
length, and carry observers are deliberately evaluated only after
specialization because these nonlinear integer views do not commute with an
arbitrary ring idempotent.

The lightweight Boolean source guard and output-relative partition machinery
live in :mod:`number_compiler.projection.output_quotient` and are re-exported here for the
combined research surface.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.polynomials.digit_convolution import (
    cyclic_binary_square_add_projection,
    negacyclic_binary_square_projection,
)
from number_compiler.arithmetic.polynomials.digit_cyclotomic import CyclotomicDigitBlock
from number_compiler.projection.output_quotient import (
    BinaryOutputCoordinate,
    BinarySourceFactorAudit,
    OutputFiberQuotient,
    ProjectionMachineQuotient,
    SpecialBranchMask,
    SpecialOutputMode,
    SpecialSourceGuard,
    SpecialSourceShape,
    audit_binary_source_factor,
    minimize_projection_machine,
    output_fiber_quotient,
)
from number_compiler.sequences.power_numbers.numbers import (
    FermatNumberSpec,
    MersenneNumberSpec,
)


@dataclass(frozen=True, slots=True)
class IdempotentModElement:
    """Element ``A + B*E`` of ``(Z/NZ)[E]/(E**2-E)``.

    ``E`` is formal.  Evaluating at ``0`` and ``1`` gives the product-ring
    sheets ``(A, A+B)``.  Evaluating at any independently known idempotent
    ``e`` with ``e**2=e (mod N)`` is also exact.
    """

    modulus: int
    constant: int
    coefficient: int = 0

    def __post_init__(self) -> None:
        modulus = int(self.modulus)
        if modulus <= 1:
            raise ValueError(modulus)
        object.__setattr__(self, "modulus", modulus)
        object.__setattr__(self, "constant", int(self.constant) % modulus)
        object.__setattr__(self, "coefficient", int(self.coefficient) % modulus)

    @classmethod
    def scalar(cls, modulus: int, value: int) -> IdempotentModElement:
        return cls(int(modulus), int(value), 0)

    @classmethod
    def generator(cls, modulus: int) -> IdempotentModElement:
        return cls(int(modulus), 0, 1)

    @classmethod
    def from_sheets(
        cls,
        modulus: int,
        zero_sheet: int,
        one_sheet: int,
    ) -> IdempotentModElement:
        modulus = int(modulus)
        zero = int(zero_sheet) % modulus
        one = int(one_sheet) % modulus
        return cls(modulus, zero, one - zero)

    @property
    def zero_sheet(self) -> int:
        return self.constant

    @property
    def one_sheet(self) -> int:
        return (self.constant + self.coefficient) % self.modulus

    @property
    def sheets(self) -> tuple[int, int]:
        return (self.zero_sheet, self.one_sheet)

    @property
    def formally_independent(self) -> bool:
        """Whether the *ring element itself* has no ``E`` coefficient."""
        return self.coefficient == 0

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "idempotent-mod-element",
            self.modulus,
            self.constant,
            self.coefficient,
        )

    def _coerce(self, other: IdempotentModElement | int) -> IdempotentModElement:
        if isinstance(other, IdempotentModElement):
            if other.modulus != self.modulus:
                raise ValueError((self.modulus, other.modulus))
            return other
        return IdempotentModElement.scalar(self.modulus, int(other))

    def add(self, other: IdempotentModElement | int) -> IdempotentModElement:
        right = self._coerce(other)
        return IdempotentModElement(
            self.modulus,
            self.constant + right.constant,
            self.coefficient + right.coefficient,
        )

    def subtract(self, other: IdempotentModElement | int) -> IdempotentModElement:
        right = self._coerce(other)
        return IdempotentModElement(
            self.modulus,
            self.constant - right.constant,
            self.coefficient - right.coefficient,
        )

    def negate(self) -> IdempotentModElement:
        return IdempotentModElement(
            self.modulus,
            -self.constant,
            -self.coefficient,
        )

    def multiply(self, other: IdempotentModElement | int) -> IdempotentModElement:
        """Closed product ``AC + (AD+BC+BD)E``."""
        right = self._coerce(other)
        a, b = self.constant, self.coefficient
        c, d = right.constant, right.coefficient
        return IdempotentModElement(
            self.modulus,
            a * c,
            a * d + b * c + b * d,
        )

    def square(self) -> IdempotentModElement:
        """Closed square ``A**2 + (2AB+B**2)E``."""
        a, b = self.constant, self.coefficient
        return IdempotentModElement(
            self.modulus,
            a * a,
            2 * a * b + b * b,
        )

    def evaluate_boolean(self, source_bit: bool | int) -> int:
        bit = int(source_bit)
        if bit not in (0, 1):
            raise ValueError(bit)
        return self.zero_sheet if bit == 0 else self.one_sheet

    def specialize_idempotent(self, idempotent: int) -> int:
        """Evaluate at an exact CRT idempotent after verifying ``e**2=e``."""
        e = int(idempotent) % self.modulus
        if (e * e - e) % self.modulus:
            raise ValueError(("not-idempotent", e, self.modulus))
        return (self.constant + self.coefficient * e) % self.modulus


@dataclass(frozen=True, slots=True)
class IdempotentCyclotomicDigitBlock:
    """Product-ring lift of the canonical source-digit/cyclotomic block.

    The two sheets reuse :class:`CyclotomicDigitBlock`; no second polynomial or
    cyclotomic implementation is introduced.  Algebraic operations are simply
    componentwise under ``R[E]/(E**2-E) ~= R x R``.
    """

    zero_sheet: CyclotomicDigitBlock
    one_sheet: CyclotomicDigitBlock

    def __post_init__(self) -> None:
        if not isinstance(self.zero_sheet, CyclotomicDigitBlock) or not isinstance(
            self.one_sheet, CyclotomicDigitBlock
        ):
            raise TypeError((type(self.zero_sheet), type(self.one_sheet)))
        if self.zero_sheet.module_key != self.one_sheet.module_key:
            raise ValueError((self.zero_sheet.module_key, self.one_sheet.module_key))

    @property
    def module_key(self) -> tuple[object, ...]:
        return self.zero_sheet.module_key

    @property
    def endpoint_residues_equal(self) -> bool:
        return self.zero_sheet.residue == self.one_sheet.residue

    @property
    def endpoint_blocks_equal(self) -> bool:
        return (
            self.zero_sheet.length == self.one_sheet.length
            and self.endpoint_residues_equal
        )

    def _check(self, other: IdempotentCyclotomicDigitBlock) -> None:
        if not isinstance(other, IdempotentCyclotomicDigitBlock):
            raise TypeError(type(other))
        if self.module_key != other.module_key:
            raise ValueError((self.module_key, other.module_key))

    def add(
        self, other: IdempotentCyclotomicDigitBlock
    ) -> IdempotentCyclotomicDigitBlock:
        self._check(other)
        return IdempotentCyclotomicDigitBlock(
            self.zero_sheet.add(other.zero_sheet),
            self.one_sheet.add(other.one_sheet),
        )

    def subtract(
        self, other: IdempotentCyclotomicDigitBlock
    ) -> IdempotentCyclotomicDigitBlock:
        self._check(other)
        return IdempotentCyclotomicDigitBlock(
            self.zero_sheet.subtract(other.zero_sheet),
            self.one_sheet.subtract(other.one_sheet),
        )

    def multiply(
        self, other: IdempotentCyclotomicDigitBlock
    ) -> IdempotentCyclotomicDigitBlock:
        self._check(other)
        return IdempotentCyclotomicDigitBlock(
            self.zero_sheet.multiply(other.zero_sheet),
            self.one_sheet.multiply(other.one_sheet),
        )

    def square(self) -> IdempotentCyclotomicDigitBlock:
        return IdempotentCyclotomicDigitBlock(
            self.zero_sheet.square(),
            self.one_sheet.square(),
        )

    def add_constant(self, value: int) -> IdempotentCyclotomicDigitBlock:
        return IdempotentCyclotomicDigitBlock(
            self.zero_sheet.add_constant(value),
            self.one_sheet.add_constant(value),
        )

    def then(
        self, other: IdempotentCyclotomicDigitBlock
    ) -> IdempotentCyclotomicDigitBlock:
        self._check(other)
        return IdempotentCyclotomicDigitBlock(
            self.zero_sheet.then(other.zero_sheet),
            self.one_sheet.then(other.one_sheet),
        )

    def shift_positions(
        self,
        offset: int,
        *,
        result_length: int | None = None,
    ) -> IdempotentCyclotomicDigitBlock:
        return IdempotentCyclotomicDigitBlock(
            self.zero_sheet.shift_positions(offset, result_length=result_length),
            self.one_sheet.shift_positions(offset, result_length=result_length),
        )

    def reverse(self, *, width: int | None = None) -> IdempotentCyclotomicDigitBlock:
        return IdempotentCyclotomicDigitBlock(
            self.zero_sheet.reverse(width=width),
            self.one_sheet.reverse(width=width),
        )

    def specialize_idempotent(self, idempotent: int) -> CyclotomicDigitBlock:
        """Interpolate the algebraic residue at a verified coefficient idempotent.

        The returned length is the maximum sheet width because spatial length is
        metadata rather than a ring coordinate.  Concrete digit/length observers
        must still be evaluated *after* specialization.
        """
        modulus = self.zero_sheet.modulus
        e = int(idempotent) % modulus
        if (e * e - e) % modulus:
            raise ValueError(("not-idempotent", e, modulus))
        delta = self.one_sheet.subtract(self.zero_sheet)
        out = self.zero_sheet.add(delta.scale_coefficients(e))
        return out.with_length(
            max(self.zero_sheet.length, self.one_sheet.length, out.length)
        )


@dataclass(frozen=True, slots=True)
class IdempotentSpecialDigitBlock:
    """Exact digit/length/carry observer for a formal special-number residue.

    The formal arithmetic is rank two, but integer observers are deliberately
    applied only after specialization.  This prevents the unsound transformation
    ``digit(A+B*E) -> digit(A) + ...*E`` in the presence of radix carries.
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
        value = self.specialize_idempotent(idempotent)
        return (value >> index) & 1

    def length_at_idempotent(self, idempotent: int) -> int:
        value = self.specialize_idempotent(idempotent)
        return max(1, value.bit_length())

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


__all__ = [
    "BinaryOutputCoordinate",
    "BinarySourceFactorAudit",
    "IdempotentCyclotomicDigitBlock",
    "IdempotentModElement",
    "IdempotentSpecialDigitBlock",
    "OutputFiberQuotient",
    "ProjectionMachineQuotient",
    "SpecialBranchMask",
    "SpecialOutputMode",
    "SpecialSourceGuard",
    "SpecialSourceShape",
    "audit_binary_source_factor",
    "minimize_projection_machine",
    "output_fiber_quotient",
]

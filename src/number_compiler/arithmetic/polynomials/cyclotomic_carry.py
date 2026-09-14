"""Carry-transfer transducer with cyclotomic emission.

The source digit ring lives in :mod:`digit_cyclotomic`; this module owns only
the carry action/output wreath.  Separating them prevents carry normalization
from becoming part of the canonical cyclotomic ring state.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass

from number_compiler.arithmetic.carry.carry_normalization import (
    RadixCarryAction,
    RadixCarryBlock,
    linear_normalization_fields,
)
from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.arithmetic.fields.radix import bit_width
from number_compiler.arithmetic.polynomials.digit_cyclotomic import CyclotomicDigitBlock


@dataclass(frozen=True, slots=True)
class CarryCyclotomicTransducer:
    """Exact carry-transfer action with one cyclotomic carry emission.

    For each admissible incoming carry ``c`` the transducer stores only

    * the outgoing carry after this spatial coefficient block, and
    * ``Q_c(z) = sum_i c_(i+1) z**i`` in one selected cyclotomic module.

    The raw coefficients and the internal carry vector are discarded.  The
    object nevertheless composes exactly: appending a more-significant block
    feeds the first block's outgoing carry into the second block and appends
    the second cyclotomic emission at the correct spatial shift.  This is the
    multi-valued analogue of the three-function reverse-add carry automaton,
    with the carry polynomial acting as the wreath/transducer output channel.

    The finite incoming interval is explicit.  Research callers choose a
    theorem-safe reachable interval; production must never infer correctness
    outside that declared domain.
    """

    action: RadixCarryAction
    order: int
    modulus: int
    power: int
    factor: tuple[int, ...] | None
    emissions: tuple[tuple[int, ...], ...]
    compositions: int = 0

    def __post_init__(self) -> None:
        if (
            self.order <= 0
            or self.modulus <= 1
            or self.power <= 0
            or self.compositions < 0
        ):
            raise ValueError(self)
        if len(self.emissions) != len(self.action.outgoing):
            raise ValueError((len(self.emissions), len(self.action.outgoing)))
        probe = CyclotomicDigitBlock.identity(
            self.order,
            self.modulus,
            power=self.power,
            factor=self.factor,
        )
        degree = probe.degree
        if any(len(row) != degree for row in self.emissions):
            raise ValueError((degree, self.emissions))
        object.__setattr__(
            self, "factor", None if self.factor is None else tuple(self.factor)
        )
        object.__setattr__(
            self,
            "emissions",
            tuple(
                tuple(int(value) % self.modulus for value in row)
                for row in self.emissions
            ),
        )

    @classmethod
    def from_coefficients(
        cls,
        coefficients: Sequence[int],
        *,
        base: int,
        incoming_min: int,
        incoming_max: int,
        order: int,
        modulus: int,
        power: int = 1,
        factor: Sequence[int] | None = None,
    ) -> CarryCyclotomicTransducer:
        coeffs = tuple(map(int, coefficients))
        block = RadixCarryBlock.from_coefficients(coeffs, base=int(base))
        action = RadixCarryAction.from_block(
            block,
            incoming_min=int(incoming_min),
            incoming_max=int(incoming_max),
        )
        f = None if factor is None else tuple(map(int, factor))
        emissions: list[tuple[int, ...]] = []
        for incoming in range(action.incoming_min, action.incoming_max + 1):
            _digits, carries = linear_normalization_fields(
                coeffs,
                base=action.base,
                boundary_in=incoming,
            )
            emission = CyclotomicDigitBlock.from_coefficients(
                carries[1:],
                order=int(order),
                modulus=int(modulus),
                power=int(power),
                length=len(coeffs),
                factor=f,
            )
            emissions.append(emission.residue)
        return cls(
            action,
            int(order),
            int(modulus),
            int(power),
            f,
            tuple(emissions),
            action.compositions,
        )

    @property
    def incoming_min(self) -> int:
        return self.action.incoming_min

    @property
    def incoming_max(self) -> int:
        return self.action.incoming_max

    @property
    def module_key(self) -> tuple[object, ...]:
        return CyclotomicDigitBlock.identity(
            self.order,
            self.modulus,
            power=self.power,
            factor=self.factor,
        ).module_key

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "carry-cyclotomic-transducer",
            self.action.canonical_key,
            self.module_key,
            self.emissions,
        )

    @property
    def description_bits(self) -> int:
        coefficient_bits = bit_width(self.modulus - 1)
        return (
            self.action.description_bits
            + bit_width(self.order)
            + bit_width(self.modulus)
            + bit_width(self.power)
            + sum(len(row) * coefficient_bits for row in self.emissions)
        )

    def emission(self, incoming: int) -> CyclotomicDigitBlock:
        incoming = int(incoming)
        if not self.incoming_min <= incoming <= self.incoming_max:
            raise ValueError((incoming, self.incoming_min, self.incoming_max))
        residue = self.emissions[incoming - self.incoming_min]
        return CyclotomicDigitBlock(
            self.order,
            self.modulus,
            self.action.length,
            residue,
            0,
            self.power,
            self.factor,
        )

    def then(self, other: CarryCyclotomicTransducer) -> CarryCyclotomicTransducer:
        if self.module_key != other.module_key:
            raise ValueError((self.module_key, other.module_key))
        action = self.action.then(other.action)
        emissions: list[tuple[int, ...]] = []
        for incoming in range(self.incoming_min, self.incoming_max + 1):
            middle = self.action.apply(incoming)
            combined = self.emission(incoming).then(other.emission(middle))
            emissions.append(combined.residue)
        return CarryCyclotomicTransducer(
            action,
            self.order,
            self.modulus,
            self.power,
            self.factor,
            tuple(emissions),
            self.compositions + other.compositions + 1,
        )

    def power_block(self, exponent: int) -> CarryCyclotomicTransducer:
        identity_action = RadixCarryAction(
            self.action.base,
            0,
            self.incoming_min,
            tuple(range(self.incoming_min, self.incoming_max + 1)),
            0,
        )
        zero = CyclotomicDigitBlock.identity(
            self.order,
            self.modulus,
            power=self.power,
            factor=self.factor,
        ).residue
        identity = CarryCyclotomicTransducer(
            identity_action,
            self.order,
            self.modulus,
            self.power,
            self.factor,
            tuple(zero for _ in identity_action.outgoing),
            0,
        )
        base = CarryCyclotomicTransducer(
            self.action,
            self.order,
            self.modulus,
            self.power,
            self.factor,
            self.emissions,
            0,
        )
        powered = binary_power(
            base, exponent, identity=identity, compose=CarryCyclotomicTransducer.then
        )
        result = powered.value
        return CarryCyclotomicTransducer(
            result.action,
            result.order,
            result.modulus,
            result.power,
            result.factor,
            result.emissions,
            powered.compositions,
        )


__all__ = ["CarryCyclotomicTransducer"]

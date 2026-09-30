"""Unified cyclotomic algebra on *source digit polynomials*.

This module is the canonical bridge below projection/carry instrumentation.
A radix word ``d_0,d_1,...`` is the polynomial ``D(z)=sum d_i z**i`` and is
reduced in one cyclotomic (or finite-field cyclotomic-factor) quotient.  The
same object supports the operations that recur across the sequence families:

* reversal ``z**(L-1) D(z**-1)`` and symmetric pair addition;
* radix multiplication/addition, including binary Collatz ``(1+z)D+1``;
* spatial shifts and the reverse-add growth multiplier ``1+z``;
* polynomial products/squares before cyclic or negacyclic normalization;
* the boundary-aware normalization defect ``(base-z)Q``;
* finite-field irreducible factors of ``Phi_m`` without a parallel digit state.

The blocks here are theorem/quotient coordinates.  They never become a second
semantic sequence state merely by being computed; a caller must still prove
that a requested target or successor is recoverable from a chosen component.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from math import comb, gcd
from typing import TYPE_CHECKING

from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.arithmetic.fields.radix import bit_width, digits_lsd
from number_compiler.arithmetic.polynomials.cyclotomic_factor import (
    cyclotomic_factors_mod_prime,
    cyclotomic_primary_components,
    polynomial_crt_mod_prime,
    polynomial_crt_mod_prime_power,
)
from number_compiler.arithmetic.polynomials.cyclotomic_ring import CyclotomicRing
from number_compiler.arithmetic.polynomials.polynomial import (
    trim_polynomial,
    evaluate_polynomial,
    polynomial_divide_exact,
)

if TYPE_CHECKING:
    from number_compiler.arithmetic.polynomials.cyclotomic_affine import (
        CyclotomicAffineMorphism,
    )


def _trim(values: Sequence[int]) -> tuple[int, ...]:
    return trim_polynomial(values)


def _affine_morphism() -> type[CyclotomicAffineMorphism]:
    # Lazy import breaks the intentional block<->affine type dependency without
    # duplicating either implementation.
    from number_compiler.arithmetic.polynomials.cyclotomic_affine import (
        CyclotomicAffineMorphism,
    )

    return CyclotomicAffineMorphism


@dataclass(frozen=True, slots=True)
class CyclotomicDigitBlock:
    """One fixed-width digit polynomial in a canonical cyclotomic quotient.

    ``factor`` is normally ``None``, selecting ``Phi_order(z)**power``.  For a
    finite-field primary component it is one monic irreducible factor of
    ``Phi_order`` modulo the prime coefficient modulus.  This keeps full
    cyclotomic jets and their deeper finite-field factors in *one* block type.
    """

    order: int
    modulus: int
    length: int
    residue: tuple[int, ...]
    compositions: int = 0
    power: int = 1
    factor: tuple[int, ...] | None = None

    def __post_init__(self) -> None:
        order = int(self.order)
        modulus = int(self.modulus)
        power = int(self.power)
        length = int(self.length)
        compositions = int(self.compositions)
        if order <= 0 or modulus <= 1 or power <= 0 or length < 0 or compositions < 0:
            raise ValueError(self)
        ring = CyclotomicRing(order, modulus, power, self.factor)
        factor = ring.factor
        degree = ring.degree
        if len(self.residue) != degree:
            raise ValueError((len(self.residue), degree, self))
        object.__setattr__(self, "order", order)
        object.__setattr__(self, "modulus", modulus)
        object.__setattr__(self, "power", power)
        object.__setattr__(self, "length", length)
        object.__setattr__(self, "compositions", compositions)
        object.__setattr__(self, "factor", factor)
        object.__setattr__(
            self, "residue", tuple(int(v) % modulus for v in self.residue)
        )

    @property
    def ring(self) -> CyclotomicRing:
        return CyclotomicRing(self.order, self.modulus, self.power, self.factor)

    @property
    def divisor(self) -> tuple[int, ...]:
        return self.ring.divisor

    @property
    def degree(self) -> int:
        return self.ring.degree

    @property
    def finite_factor(self) -> bool:
        return self.factor is not None

    @property
    def module_key(self) -> tuple[object, ...]:
        return self.ring.module_key

    @classmethod
    def identity(
        cls,
        order: int = 2,
        modulus: int = 32,
        *,
        power: int = 1,
        factor: Sequence[int] | None = None,
    ) -> CyclotomicDigitBlock:
        ring = CyclotomicRing(
            int(order),
            int(modulus),
            int(power),
            None if factor is None else tuple(factor),
        )
        return cls(ring.order, ring.modulus, 0, ring.zero, 0, ring.power, ring.factor)

    @classmethod
    def digit(
        cls,
        value: int,
        *,
        order: int = 2,
        modulus: int = 32,
        power: int = 1,
        factor: Sequence[int] | None = None,
    ) -> CyclotomicDigitBlock:
        ring = CyclotomicRing(
            int(order),
            int(modulus),
            int(power),
            None if factor is None else tuple(factor),
        )
        return cls(
            ring.order,
            ring.modulus,
            1,
            (int(value) % ring.modulus,) + (0,) * (ring.degree - 1),
            0,
            ring.power,
            ring.factor,
        )

    @classmethod
    def from_coefficients(
        cls,
        coefficients: Sequence[int],
        *,
        order: int,
        modulus: int,
        power: int = 1,
        length: int | None = None,
        factor: Sequence[int] | None = None,
    ) -> CyclotomicDigitBlock:
        coeffs = tuple(map(int, coefficients))
        if length is None:
            length = len(coeffs)
        length = int(length)
        if length < len(coeffs):
            raise ValueError((length, len(coeffs)))
        ring = CyclotomicRing(
            int(order),
            int(modulus),
            int(power),
            None if factor is None else tuple(factor),
        )
        residue = ring.reduce(coeffs)
        return cls(
            ring.order,
            ring.modulus,
            length,
            residue,
            0,
            ring.power,
            ring.factor,
        )

    @classmethod
    def from_radix_value(
        cls,
        value: int,
        *,
        base: int,
        order: int,
        modulus: int,
        width: int | None = None,
        power: int = 1,
        factor: Sequence[int] | None = None,
    ) -> CyclotomicDigitBlock:
        digits = digits_lsd(int(value), int(base), width)
        return cls.from_coefficients(
            digits,
            order=order,
            modulus=modulus,
            power=power,
            length=len(digits),
            factor=factor,
        )

    @classmethod
    def finite_field_factor(
        cls,
        coefficients: Sequence[int],
        *,
        order: int,
        prime: int,
        factor_index: int,
        length: int | None = None,
    ) -> CyclotomicDigitBlock:
        factors = cyclotomic_factors_mod_prime(int(order), int(prime))
        index = int(factor_index)
        if not 0 <= index < len(factors):
            raise ValueError((index, len(factors)))
        return cls.from_coefficients(
            coefficients,
            order=int(order),
            modulus=int(prime),
            power=1,
            length=length,
            factor=factors[index],
        )

    def finite_field_components(self) -> tuple[CyclotomicDigitBlock, ...]:
        """Split a whole ``Phi_order mod p`` component into irreducible factors.

        All components together are lossless by polynomial CRT; callers may
        retain a strict subset only after proving that subset is an observer.
        """
        if self.factor is not None or self.power != 1:
            raise ValueError(
                "finite-field splitting requires one whole power-1 cyclotomic block"
            )
        factors = cyclotomic_factors_mod_prime(self.order, self.modulus)
        return tuple(
            CyclotomicDigitBlock.from_coefficients(
                self.residue,
                order=self.order,
                modulus=self.modulus,
                length=self.length,
                factor=factor,
            )
            for factor in factors
        )

    @classmethod
    def from_finite_field_components(
        cls,
        components: Sequence[CyclotomicDigitBlock],
    ) -> CyclotomicDigitBlock:
        """CRT-reconstruct the whole cyclotomic block from all primary factors."""
        parts = tuple(components)
        if not parts:
            raise ValueError("no finite-field components")
        first = parts[0]
        if first.factor is None or first.power != 1:
            raise ValueError(first)
        if any(
            part.order != first.order
            or part.modulus != first.modulus
            or part.length != first.length
            or part.factor is None
            or part.power != 1
            for part in parts
        ):
            raise ValueError("incompatible finite-field components")
        expected = cyclotomic_factors_mod_prime(first.order, first.modulus)
        supplied = tuple(part.factor for part in parts if part.factor is not None)
        if tuple(sorted(supplied)) != expected:
            raise ValueError(("incomplete-or-duplicate-components", supplied, expected))
        ordered = {part.factor: part for part in parts}
        residue = polynomial_crt_mod_prime(
            tuple(ordered[factor].residue for factor in expected),
            expected,
            first.modulus,
        )
        return cls(
            first.order,
            first.modulus,
            first.length,
            residue,
            sum(part.compositions for part in parts) + max(0, len(parts) - 1),
            1,
            None,
        )

    def prime_power_components(
        self,
        *,
        prime: int,
        precision: int,
    ) -> tuple[CyclotomicDigitBlock, ...]:
        """Split one whole cyclotomic block into canonical ``p**k`` primaries.

        Ramified channels intentionally return ``(self,)``: repeated-root
        factors are not independent CRT coordinates.
        """
        p, k = int(prime), int(precision)
        if self.factor is not None or self.power != 1 or self.modulus != p**k:
            raise ValueError((self.module_key, p, k))
        factors = cyclotomic_primary_components(self.order, p, k)
        if (
            len(factors) == 1
            and tuple(int(c) % self.modulus for c in self.divisor) == factors[0]
        ):
            return (self,)
        return tuple(
            CyclotomicDigitBlock.from_coefficients(
                self.residue,
                order=self.order,
                modulus=self.modulus,
                length=self.length,
                factor=factor,
            )
            for factor in factors
        )

    @classmethod
    def from_prime_power_components(
        cls,
        components: Sequence[CyclotomicDigitBlock],
        *,
        prime: int,
        precision: int,
    ) -> CyclotomicDigitBlock:
        """CRT-reconstruct a whole cyclotomic block from all unramified primaries."""
        parts = tuple(components)
        p, k = int(prime), int(precision)
        q = p**k
        if not parts:
            raise ValueError("no prime-power components")
        if len(parts) == 1 and parts[0].factor is None:
            if parts[0].modulus != q:
                raise ValueError((parts[0].modulus, q))
            return parts[0]
        first = parts[0]
        if any(
            part.order != first.order
            or part.modulus != q
            or part.length != first.length
            or part.factor is None
            or part.power != 1
            for part in parts
        ):
            raise ValueError("incompatible prime-power components")
        expected = cyclotomic_primary_components(first.order, p, k)
        supplied = tuple(part.factor for part in parts if part.factor is not None)
        if tuple(sorted(supplied)) != tuple(sorted(expected)):
            raise ValueError(
                ("incomplete-or-duplicate-primary-components", supplied, expected)
            )
        by_factor = {part.factor: part for part in parts}
        residue = polynomial_crt_mod_prime_power(
            tuple(by_factor[factor].residue for factor in expected),
            expected,
            p,
            k,
        )
        return cls(
            first.order,
            q,
            first.length,
            residue,
            sum(part.compositions for part in parts) + max(0, len(parts) - 1),
            1,
            None,
        )

    def _check_module(self, other: CyclotomicDigitBlock) -> None:
        if self.module_key != other.module_key:
            raise ValueError((self.module_key, other.module_key))

    def with_length(self, length: int) -> CyclotomicDigitBlock:
        length = int(length)
        if length < self.length:
            raise ValueError((self.length, length))
        return CyclotomicDigitBlock(
            self.order,
            self.modulus,
            length,
            self.residue,
            self.compositions,
            self.power,
            self.factor,
        )

    def then(self, other: CyclotomicDigitBlock) -> CyclotomicDigitBlock:
        """Append ``other`` as a more-significant coefficient block."""
        self._check_module(other)
        shift = self.z_power_residue(self.length)
        moved = self.ring.multiply(shift, other.residue)
        residue = self.ring.add(self.residue, moved)
        return CyclotomicDigitBlock(
            self.order,
            self.modulus,
            self.length + other.length,
            residue,
            self.compositions + other.compositions + 1,
            self.power,
            self.factor,
        )

    def power_block(self, exponent: int) -> CyclotomicDigitBlock:
        """Repeat this *spatial block* through the shared monoid power kernel."""
        identity = CyclotomicDigitBlock.identity(
            self.order,
            self.modulus,
            power=self.power,
            factor=self.factor,
        )
        powered = binary_power(
            self, exponent, identity=identity, compose=CyclotomicDigitBlock.then
        )
        result = powered.value
        return CyclotomicDigitBlock(
            result.order,
            result.modulus,
            result.length,
            result.residue,
            powered.compositions,
            result.power,
            result.factor,
        )

    def equivalent(self, other: CyclotomicDigitBlock) -> bool:
        self._check_module(other)
        return self.residue == other.residue

    def add(self, other: CyclotomicDigitBlock) -> CyclotomicDigitBlock:
        self._check_module(other)
        return CyclotomicDigitBlock(
            self.order,
            self.modulus,
            max(self.length, other.length),
            self.ring.add(self.residue, other.residue),
            self.compositions + other.compositions + 1,
            self.power,
            self.factor,
        )

    def subtract(self, other: CyclotomicDigitBlock) -> CyclotomicDigitBlock:
        self._check_module(other)
        return CyclotomicDigitBlock(
            self.order,
            self.modulus,
            max(self.length, other.length),
            self.ring.subtract(self.residue, other.residue),
            self.compositions + other.compositions + 1,
            self.power,
            self.factor,
        )

    def scale_coefficients(self, scalar: int) -> CyclotomicDigitBlock:
        residue = self.ring.scale(self.residue, scalar)
        return CyclotomicDigitBlock(
            self.order,
            self.modulus,
            self.length,
            residue,
            self.compositions + 1,
            self.power,
            self.factor,
        )

    def add_constant(self, value: int) -> CyclotomicDigitBlock:
        residue = list(self.residue)
        residue[0] = (residue[0] + int(value)) % self.modulus
        return CyclotomicDigitBlock(
            self.order,
            self.modulus,
            max(1, self.length),
            tuple(residue),
            self.compositions + 1,
            self.power,
            self.factor,
        )

    def multiply(self, other: CyclotomicDigitBlock) -> CyclotomicDigitBlock:
        self._check_module(other)
        residue = self.ring.multiply(self.residue, other.residue)
        length = (
            0 if not self.length or not other.length else self.length + other.length - 1
        )
        return CyclotomicDigitBlock(
            self.order,
            self.modulus,
            length,
            residue,
            self.compositions + other.compositions + 1,
            self.power,
            self.factor,
        )

    def square(self) -> CyclotomicDigitBlock:
        return self.multiply(self)

    def z_power_residue(self, exponent: int) -> tuple[int, ...]:
        exponent = int(exponent)
        degree = self.degree
        one = (1,) + (0,) * (degree - 1)
        if exponent == 0:
            return one
        if exponent < 0:
            minus_z_inverse = self.linear_factor_inverse_residue(0)
            base = tuple((-value) % self.modulus for value in minus_z_inverse)
            exponent = -exponent
        else:
            base = self.ring.reduce((0, 1))
        return tuple(self.ring.power_residue(base, exponent).value)

    def shift_positions(
        self, offset: int, *, result_length: int | None = None
    ) -> CyclotomicDigitBlock:
        offset = int(offset)
        if result_length is None:
            result_length = self.length + offset
        result_length = int(result_length)
        if result_length < 0:
            raise ValueError((self.length, offset, result_length))
        morphism = _affine_morphism().from_residues(
            self,
            self.z_power_residue(offset),
            (0,) * self.degree,
        )
        return morphism.apply(self, result_length=result_length)

    def reverse(self, *, width: int | None = None) -> CyclotomicDigitBlock:
        """Apply ``D(z) -> z**(L-1) D(z**-1)`` at fixed padded width."""
        width = self.length if width is None else int(width)
        if width < self.length or width <= 0:
            raise ValueError((self.length, width))
        inverse_z = self.z_power_residue(-1)
        power = (1,) + (0,) * (self.degree - 1)
        reflected = [0] * self.degree
        for coefficient in self.residue:
            for index, value in enumerate(power):
                reflected[index] = (
                    reflected[index] + coefficient * value
                ) % self.modulus
            power = self.ring.multiply(power, inverse_z)
        shift = self.z_power_residue(width - 1)
        residue = self.ring.multiply(shift, reflected)
        return CyclotomicDigitBlock(
            self.order,
            self.modulus,
            width,
            residue,
            self.compositions + 1,
            self.power,
            self.factor,
        )

    def symmetric_pair(self) -> CyclotomicDigitBlock:
        return self.add(self.reverse())

    def multiply_one_plus_z(self) -> CyclotomicDigitBlock:
        factor = CyclotomicDigitBlock.from_coefficients(
            (1, 1),
            order=self.order,
            modulus=self.modulus,
            power=self.power,
            factor=self.factor,
        )
        return self.multiply(factor)

    def multiply_polynomial_power(
        self,
        coefficients: Sequence[int],
        exponent: int,
        *,
        length_growth: int = 0,
    ) -> CyclotomicDigitBlock:
        """Apply one polynomial multiplier to a temporal power in ``O(log exponent)`` compositions."""
        exponent = int(exponent)
        length_growth = int(length_growth)
        if exponent < 0 or length_growth < 0:
            raise ValueError((exponent, length_growth))
        factor = CyclotomicDigitBlock.from_coefficients(
            coefficients,
            order=self.order,
            modulus=self.modulus,
            power=self.power,
            factor=self.factor,
        )
        # This is algebraic multiplication, not spatial block repetition.
        powered = self.ring.power_residue(factor.residue, exponent)
        result_residue = powered.value
        ops = powered.compositions
        residue = self.ring.multiply(self.residue, result_residue)
        return CyclotomicDigitBlock(
            self.order,
            self.modulus,
            self.length + exponent * length_growth,
            residue,
            self.compositions + ops + int(bool(exponent)),
            self.power,
            self.factor,
        )

    def reverse_add_linear_transport(
        self,
        *,
        no_growth: int = 0,
        growth: int = 0,
    ) -> CyclotomicDigitBlock:
        """Apply the exact reverse-add pair *linear* transport ``2^q(1+z)^r``.

        Carry-domain affine corrections remain separate.  The powered linear
        part is compiled through :class:`CyclotomicAffineMorphism`, the same
        executable IR used by Collatz and normalization maps.
        """
        q, r = int(no_growth), int(growth)
        if q < 0 or r < 0:
            raise ValueError((q, r))
        morphism = _affine_morphism().scale(self, pow(2, q, self.modulus))
        if r:
            growth_map = _affine_morphism().from_polynomials(self, (1, 1), (0,))
            morphism = morphism.then(growth_map.power_map(r))
        return morphism.apply(self, result_length=self.length + r)

    def radix_affine(
        self, *, multiplier: int, addend: int, base: int
    ) -> CyclotomicDigitBlock:
        """Apply the raw radix polynomial for ``multiplier*x + addend``.

        The multiplier is represented by its radix digits, so binary ``3*x+1``
        becomes ``(1+z)D+1`` while ternary ``3*x+1`` becomes ``zD+1``.
        No normalization/carry vector is materialized here.
        """
        multiplier, addend, base = int(multiplier), int(addend), int(base)
        if multiplier < 0 or base < 2:
            raise ValueError((multiplier, addend, base))
        factor_digits = digits_lsd(multiplier, base)
        morphism = _affine_morphism().from_polynomials(
            self,
            factor_digits,
            (addend,),
        )
        raw_length = (
            0
            if not self.length or not factor_digits
            else self.length + len(factor_digits) - 1
        )
        return morphism.apply(self, result_length=max(1, raw_length))

    def linear_factor_is_unit(self, base: int) -> bool:
        """Whether multiplication by ``base-z`` is invertible in this quotient."""
        value = evaluate_polynomial(self.divisor, int(base))
        return gcd(value, self.modulus) == 1

    def linear_factor_inverse_residue(self, base: int) -> tuple[int, ...]:
        """Return ``(base-z)^-1`` when it exists, without generic polynomial EEA.

        For monic ``F``, write ``F(z)-F(base)=(z-base)H(z)``.  Then
        ``(base-z)H(z)=F(base)-F(z)=F(base) mod F``.  Thus one integer modular
        inverse of ``F(base)`` gives the whole polynomial inverse.
        """
        base = int(base)
        value = evaluate_polynomial(self.divisor, base)
        if gcd(value, self.modulus) != 1:
            raise ValueError(
                ("nonunit-linear-normalization", base, value, self.modulus)
            )
        numerator = list(map(int, self.divisor))
        numerator[0] -= value
        quotient = polynomial_divide_exact(tuple(numerator), (-base, 1))
        if quotient is None:
            raise AssertionError((self.divisor, base, value))
        inverse_value = pow(value % self.modulus, -1, self.modulus)
        return self.ring.reduce(
            tuple(inverse_value * coefficient for coefficient in quotient)
        )

    def apply_linear_factor(self, base: int) -> CyclotomicDigitBlock:
        return (
            _affine_morphism()
            .from_polynomials(
                self,
                (int(base), -1),
                (0,),
            )
            .apply(self, result_length=self.length + 1)
        )

    def divide_linear_factor(
        self, base: int, *, result_length: int | None = None
    ) -> CyclotomicDigitBlock:
        inverse = self.linear_factor_inverse_residue(int(base))
        return (
            _affine_morphism()
            .from_residues(
                self,
                inverse,
                (0,) * self.degree,
            )
            .apply(
                self,
                result_length=self.length
                if result_length is None
                else int(result_length),
            )
        )

    @property
    def local_linear_coefficients(self) -> tuple[int, ...]:
        if self.factor is not None or self.order not in (1, 2):
            raise ValueError(
                "linear local coordinates require an unfactored Phi_1/Phi_2 jet"
            )
        center = 1 if self.order == 1 else -1
        degree = len(self.residue)
        return tuple(
            sum(
                self.residue[i] * comb(i, j) * (center ** (i - j))
                for i in range(j, degree)
            )
            % self.modulus
            for j in range(degree)
        )

    @property
    def canonical_key(self) -> tuple[object, ...]:
        if self.factor is not None:
            return (
                "digit-cyclotomic-factor",
                self.order,
                self.modulus,
                self.factor,
                self.length,
                self.residue,
            )
        # Preserve the former projection keys so existing caches/readers do not
        # fork merely because the implementation moved below the projection layer.
        if self.power == 1:
            return (
                "projection-cyclotomic",
                self.order,
                self.modulus,
                self.length,
                self.residue,
            )
        return (
            "projection-cyclotomic-jet",
            self.order,
            self.power,
            self.modulus,
            self.length,
            self.residue,
        )

    @property
    def description_bits(self) -> int:
        coefficient_bits = bit_width(self.modulus - 1)
        bits = (
            bit_width(self.order)
            + bit_width(self.modulus)
            + bit_width(self.length)
            + len(self.residue) * coefficient_bits
        )
        if self.power != 1:
            bits += bit_width(self.power)
        if self.factor is not None:
            bits += len(self.factor) * coefficient_bits
        return bits


__all__ = ["CyclotomicDigitBlock"]

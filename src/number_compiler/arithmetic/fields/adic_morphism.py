"""Shared p-adic affine and tropical sensitivity morphisms.

The cross-family primary/cyclotomic interfaces all track the same semantic fact:
how strongly a powered action still depends on its old source.  If ``v`` is the
valuation of an input perturbation, many exact theorem channels act as

    v -> min(precision, scale*v + increment).

This is a closed tropical affine monoid.  It is deliberately a *derived theorem
interface*, never a replacement for the canonical sequence state.

Examples:

* Collatz normalized parity slab, p=3: each odd symbol adds one valuation;
* Mersenne successor ``x -> 2*x+1``, p=2: each step adds one valuation;
* Fermat shifted squaring ``x -> x**2`` on even x: valuation doubles;
* prime candidate translation ``x -> x+2``: source sensitivity is unchanged;
* reverse-add power-of-two cyclotomic channel: increment is
  ``q + floor(r/classes)``.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.fields.morphism_core import AffineCocycle, binary_power
from number_compiler.arithmetic.fields.radix import bit_width

_MAX_PADIC_LIMB = (1 << 64) - 1


def _bounded_prime_power(prime: int, exponent: int) -> int:
    """Return a one-limb prime power without ever allocating a wide integer."""
    if type(prime) is not int or type(exponent) is not int:
        raise TypeError("p-adic modulus metadata requires exact integers")
    if prime < 2 or exponent < 0:
        raise ValueError("invalid p-adic prime power")
    value = 1
    for _ in range(exponent):
        if value > _MAX_PADIC_LIMB // prime:
            raise ValueError("p-adic modulus exceeds the 64-bit runtime limb")
        value *= prime
    return value


def _vp(value: int, prime: int, cap: int) -> int:
    if any(type(item) is not int for item in (value, prime, cap)):
        raise TypeError("p-adic valuation requires exact integers")
    if value == 0:
        return cap
    out = 0
    while out < cap and value % prime == 0:
        value //= prime
        out += 1
    return out


@dataclass(frozen=True, slots=True)
class PadicAffineMorphism:
    """Exact affine map modulo ``prime**precision``."""

    prime: int
    precision: int
    multiplier: int
    offset: int
    steps: int = 0
    compositions: int = 0

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (
                self.prime,
                self.precision,
                self.multiplier,
                self.offset,
                self.steps,
                self.compositions,
            )
        ):
            raise TypeError("p-adic affine morphisms require exact integers")
        if (
            self.prime < 2
            or self.precision <= 0
            or self.steps < 0
            or self.compositions < 0
        ):
            raise ValueError(self)
        modulus = _bounded_prime_power(self.prime, self.precision)
        object.__setattr__(self, "multiplier", self.multiplier % modulus)
        object.__setattr__(self, "offset", self.offset % modulus)

    @property
    def modulus(self) -> int:
        return _bounded_prime_power(self.prime, self.precision)

    @classmethod
    def identity(cls, prime: int, precision: int) -> PadicAffineMorphism:
        return cls(prime, precision, 1, 0, 0, 0)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "padic-affine",
            self.prime,
            self.precision,
            self.multiplier,
            self.offset,
        )

    @property
    def source_valuation(self) -> int:
        return _vp(self.multiplier, self.prime, self.precision)

    @property
    def source_annihilated(self) -> bool:
        return self.source_valuation >= self.precision

    @property
    def description_bits(self) -> int:
        return sum(
            bit_width(v)
            for v in (
                self.prime,
                self.precision,
                self.multiplier,
                self.offset,
                self.steps,
            )
        )

    def apply(self, value: int) -> int:
        if type(value) is not int:
            raise TypeError("p-adic affine input must be an exact integer")
        modulus = self.modulus
        return self.cocycle.apply(
            value,
            multiply=lambda a, b: (a * b) % modulus,
            add=lambda a, b: (a + b) % modulus,
        )

    @property
    def cocycle(self) -> AffineCocycle[int]:
        return AffineCocycle(self.multiplier, self.offset)

    def _then_raw(self, other: PadicAffineMorphism) -> PadicAffineMorphism:
        if (self.prime, self.precision) != (other.prime, other.precision):
            raise ValueError("incompatible p-adic affine morphisms")
        m = self.modulus
        c = self.cocycle.then(
            other.cocycle,
            multiply=lambda a, b: (a * b) % m,
            add=lambda a, b: (a + b) % m,
        )
        return PadicAffineMorphism(
            self.prime,
            self.precision,
            c.multiplier,
            c.addend,
            self.steps + other.steps,
            0,
        )

    def then(self, other: PadicAffineMorphism) -> PadicAffineMorphism:
        out = self._then_raw(other)
        return PadicAffineMorphism(
            out.prime,
            out.precision,
            out.multiplier,
            out.offset,
            out.steps,
            self.compositions + other.compositions + 1,
        )

    def power(self, exponent: int) -> PadicAffineMorphism:
        base = PadicAffineMorphism(
            self.prime, self.precision, self.multiplier, self.offset, self.steps, 0
        )
        powered = binary_power(
            base,
            exponent,
            identity=PadicAffineMorphism.identity(self.prime, self.precision),
            compose=PadicAffineMorphism._then_raw,
        )
        result = powered.value
        return PadicAffineMorphism(
            result.prime,
            result.precision,
            result.multiplier,
            result.offset,
            result.steps,
            powered.compositions,
        )

    @property
    def radial_quotient(self) -> PadicRadialQuotient:
        """Factor the predictable p-adic scale from the affine source term.

        ``multiplier = p**valuation * unit`` at the surviving precision.  The
        affine innovation/offset is retained separately.  When the valuation
        reaches ``precision`` the old source is annihilated and no unit phase
        remains.  This is an exact view of the same morphism, not additional
        sequence state.
        """
        valuation = self.source_valuation
        if valuation >= self.precision:
            unit = None
        else:
            live_modulus = _bounded_prime_power(
                self.prime,
                self.precision - valuation,
            )
            unit = (
                self.multiplier // _bounded_prime_power(self.prime, valuation)
            ) % live_modulus
            if unit % self.prime == 0:
                raise AssertionError((self, valuation, unit))
        return PadicRadialQuotient(
            self.prime,
            self.precision,
            valuation,
            unit,
            self.offset,
            self.steps,
        )


@dataclass(frozen=True, slots=True)
class PadicRadialQuotient:
    """Exact scale/unit/innovation split of one p-adic affine morphism."""

    prime: int
    precision: int
    source_valuation: int
    source_unit: int | None
    innovation: int
    steps: int = 0

    def __post_init__(self) -> None:
        values = (
            self.prime,
            self.precision,
            self.source_valuation,
            self.innovation,
            self.steps,
        )
        if any(type(value) is not int for value in values) or (
            self.source_unit is not None and type(self.source_unit) is not int
        ):
            raise TypeError("p-adic radial quotients require exact integers")
        p, precision = self.prime, self.precision
        valuation = self.source_valuation
        if p < 2 or precision <= 0 or not 0 <= valuation <= precision or self.steps < 0:
            raise ValueError(self)
        modulus = _bounded_prime_power(p, precision)
        object.__setattr__(self, "innovation", self.innovation % modulus)
        if valuation >= precision:
            if self.source_unit is not None:
                raise ValueError("annihilated radial quotient has no source unit")
        else:
            live_modulus = _bounded_prime_power(p, precision - valuation)
            unit = (
                self.source_unit % live_modulus
                if self.source_unit is not None
                else None
            )
            if unit is None or unit % p == 0:
                raise ValueError("live radial quotient requires a p-adic unit")
            object.__setattr__(self, "source_unit", unit)

    @property
    def modulus(self) -> int:
        return _bounded_prime_power(self.prime, self.precision)

    @property
    def source_annihilated(self) -> bool:
        return self.source_valuation >= self.precision

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "padic-radial",
            self.prime,
            self.precision,
            self.source_valuation,
            self.source_unit,
            self.innovation,
        )

    def multiplier(self) -> int:
        if self.source_annihilated:
            return 0
        if self.source_unit is None:
            raise AssertionError(self)
        return (
            _bounded_prime_power(self.prime, self.source_valuation) * self.source_unit
        ) % self.modulus

    def as_affine(self) -> PadicAffineMorphism:
        return PadicAffineMorphism(
            self.prime,
            self.precision,
            self.multiplier(),
            self.innovation,
            self.steps,
            0,
        )


@dataclass(frozen=True, slots=True)
class ValuationSensitivityMorphism:
    """Tropical affine action ``v -> min(W, scale*v + increment)``."""

    prime: int
    precision: int
    scale: int = 1
    increment: int = 0
    logical_steps: int = 0
    compositions: int = 0

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (
                self.prime,
                self.precision,
                self.scale,
                self.increment,
                self.logical_steps,
                self.compositions,
            )
        ):
            raise TypeError("valuation morphisms require exact integers")
        if (
            self.prime < 2
            or self.precision <= 0
            or self.scale < 0
            or self.increment < 0
            or self.logical_steps < 0
            or self.compositions < 0
        ):
            raise ValueError(self)
        object.__setattr__(self, "increment", min(self.precision, self.increment))

    @classmethod
    def identity(cls, prime: int, precision: int) -> ValuationSensitivityMorphism:
        return cls(prime, precision, 1, 0, 0, 0)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "valuation-sensitivity",
            self.prime,
            self.precision,
            self.scale,
            self.increment,
        )

    @property
    def description_bits(self) -> int:
        return sum(
            bit_width(v)
            for v in (
                self.prime,
                self.precision,
                self.scale,
                self.increment,
                self.logical_steps,
            )
        )

    def apply(self, valuation: int) -> int:
        if type(valuation) is not int:
            raise TypeError("valuation input must be an exact integer")
        if not 0 <= valuation <= self.precision:
            raise ValueError((valuation, self.precision))
        return min(self.precision, self.scale * valuation + self.increment)

    def then(self, other: ValuationSensitivityMorphism) -> ValuationSensitivityMorphism:
        if (self.prime, self.precision) != (other.prime, other.precision):
            raise ValueError("incompatible valuation theorem channels")
        return ValuationSensitivityMorphism(
            self.prime,
            self.precision,
            other.scale * self.scale,
            min(self.precision, other.scale * self.increment + other.increment),
            self.logical_steps + other.logical_steps,
            self.compositions + other.compositions + 1,
        )

    def _then_raw(
        self, other: ValuationSensitivityMorphism
    ) -> ValuationSensitivityMorphism:
        if (self.prime, self.precision) != (other.prime, other.precision):
            raise ValueError("incompatible valuation theorem channels")
        return ValuationSensitivityMorphism(
            self.prime,
            self.precision,
            other.scale * self.scale,
            min(self.precision, other.scale * self.increment + other.increment),
            self.logical_steps + other.logical_steps,
            0,
        )

    def power(self, exponent: int) -> ValuationSensitivityMorphism:
        base = ValuationSensitivityMorphism(
            self.prime,
            self.precision,
            self.scale,
            self.increment,
            self.logical_steps,
            0,
        )
        powered = binary_power(
            base,
            exponent,
            identity=ValuationSensitivityMorphism.identity(self.prime, self.precision),
            compose=ValuationSensitivityMorphism._then_raw,
        )
        result = powered.value
        return ValuationSensitivityMorphism(
            result.prime,
            result.precision,
            result.scale,
            result.increment,
            result.logical_steps,
            powered.compositions,
        )

    @property
    def annihilates_unit_difference(self) -> bool:
        return self.apply(0) >= self.precision


def mersenne_successor_padic2(precision: int = 8) -> PadicAffineMorphism:
    return PadicAffineMorphism(2, precision, 2, 1, 1, 0)


def mersenne_successor_2adic_sensitivity(
    precision: int = 8,
) -> ValuationSensitivityMorphism:
    return ValuationSensitivityMorphism(2, precision, 1, 1, 1, 0)


def fermat_shifted_square_sensitivity(
    precision: int = 8,
) -> ValuationSensitivityMorphism:
    """Sensitivity of ``x -> x**2`` on the even shifted coordinate ``F-1``."""
    return ValuationSensitivityMorphism(2, precision, 2, 0, 1, 0)


def prime_translation_sensitivity(
    prime: int = 2, precision: int = 8
) -> ValuationSensitivityMorphism:
    """Translation preserves source differences: the non-nilpotent control case."""
    return ValuationSensitivityMorphism(prime, precision, 1, 0, 1, 0)


__all__ = [
    "PadicAffineMorphism",
    "PadicRadialQuotient",
    "ValuationSensitivityMorphism",
    "fermat_shifted_square_sensitivity",
    "mersenne_successor_2adic_sensitivity",
    "mersenne_successor_padic2",
    "prime_translation_sensitivity",
]

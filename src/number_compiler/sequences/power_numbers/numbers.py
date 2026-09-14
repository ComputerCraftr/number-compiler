"""Canonical Fermat / Mersenne carriers and exact bounded projectors.

These families share the same cyclotomic, radix-word, factor-set, and powered
operator machinery used by reverse-add, Collatz, and the prime projector:

* ``F_n = 2**(2**n)+1 = Phi_(2**(n+1))(2)`` is a pure 2-power cyclotomic /
  negacyclic channel.  Subtracting one conjugates generation to squaring.
* ``M_p = 2**p-1 = Phi_p(2)`` when ``p`` is prime is an odd cyclotomic /
  cyclic channel.  The trace-square map ``x -> x*x-2`` conjugates to exponent
  doubling in the norm-one quadratic unit ``2+sqrt(3)``.

These generator identities do not construct the candidate's primality bit.
Production classification requires a separately proved candidate-derived
observation; missing recovery remains unresolved.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd

from number_compiler.arithmetic.fields.symbolic_extent import DyadicExtent
from number_compiler.sequences.prime.set import is_prime_u64, smallest_factor


@dataclass(frozen=True, slots=True)
class FermatNumberSpec:
    index: int

    def __post_init__(self) -> None:
        if self.index < 0:
            raise ValueError(self.index)

    @property
    def exponent_extent(self) -> DyadicExtent:
        return DyadicExtent(self.index)

    @property
    def bit_length_extent(self) -> DyadicExtent:
        return DyadicExtent(self.index, 1)

    @property
    def cyclotomic_order_extent(self) -> DyadicExtent:
        return DyadicExtent(self.index + 1)

    @property
    def exponent(self) -> int:
        # Compatibility/materialization view.  Production source compilation
        # uses exponent_extent and never calls this property.
        return self.exponent_extent.materialize(max_power=self.index)

    @property
    def cyclotomic_order(self) -> int:
        return self.cyclotomic_order_extent.materialize(max_power=self.index + 1)

    @property
    def bit_length(self) -> int:
        return self.bit_length_extent.materialize(max_power=self.index)

    @property
    def description_bits(self) -> int:
        return max(1, self.index.bit_length())

    def materialize(self, *, max_bits: int = 1_000_000) -> int:
        max_bits = int(max_bits)
        if max_bits <= 0 or self.bit_length_extent > max_bits:
            raise ValueError((self.bit_length_extent, max_bits))
        # The guard above proves the exponent is small enough for the requested
        # materialization budget before any dyadic boundary is lowered.
        exponent = self.exponent_extent.materialize(max_power=max_bits.bit_length())
        return (1 << exponent) + 1


@dataclass(frozen=True, slots=True)
class MersenneNumberSpec:
    exponent: int

    def __post_init__(self) -> None:
        if self.exponent <= 0:
            raise ValueError(self.exponent)

    @property
    def bit_length(self) -> int:
        return self.exponent

    @property
    def description_bits(self) -> int:
        return max(1, self.exponent.bit_length())

    def materialize(self, *, max_bits: int = 1_000_000) -> int:
        max_bits = int(max_bits)
        if max_bits <= 0 or self.bit_length > max_bits:
            raise ValueError((self.bit_length, max_bits))
        return (1 << self.exponent) - 1


@dataclass(frozen=True, slots=True)
class CyclotomicRadixWordSpec:
    """Symbolic reinterpretation of a sparse binary special-number word.

    ``family='fermat'`` means the digit word ``1 0^(2^n-1) 1`` evaluated in
    ``radix``; ``family='mersenne'`` means ``1^p`` evaluated in ``radix``.
    These are respectively ``Phi_(2^(n+1))(radix)`` and, for prime ``p``,
    ``Phi_p(radix)``.  The digit program stays compact even when the evaluated
    integer is enormous.
    """

    family: str
    parameter: int
    radix: int

    def __post_init__(self) -> None:
        if (
            self.family not in ("fermat", "mersenne")
            or self.parameter < 0
            or self.radix < 2
        ):
            raise ValueError(self)
        if self.family == "mersenne" and self.parameter <= 0:
            raise ValueError(self)

    @property
    def cyclotomic_order_extent(self) -> DyadicExtent | int:
        return (
            DyadicExtent(self.parameter + 1)
            if self.family == "fermat"
            else self.parameter
        )

    @property
    def digit_length_extent(self) -> DyadicExtent | int:
        return (
            DyadicExtent(self.parameter, 1)
            if self.family == "fermat"
            else self.parameter
        )

    @property
    def cyclotomic_order(self) -> int:
        value = self.cyclotomic_order_extent
        return (
            value.materialize(max_power=value.power)
            if isinstance(value, DyadicExtent)
            else int(value)
        )

    @property
    def digit_length(self) -> int:
        value = self.digit_length_extent
        return (
            value.materialize(max_power=value.power)
            if isinstance(value, DyadicExtent)
            else int(value)
        )

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "cyclotomic-radix-word",
            self.family,
            int(self.parameter),
            int(self.radix),
        )

    @property
    def description_bits(self) -> int:
        return max(1, self.parameter.bit_length()) + max(1, self.radix.bit_length()) + 1

    def materialize(self, *, max_digits: int = 100_000) -> int:
        max_digits = int(max_digits)
        extent = self.digit_length_extent
        if (
            (extent > max_digits)
            if isinstance(extent, DyadicExtent)
            else (int(extent) > max_digits)
        ):
            raise ValueError((extent, max_digits))
        if self.family == "fermat":
            exponent = DyadicExtent(self.parameter).materialize(
                max_power=max_digits.bit_length()
            )
            return int(pow(self.radix, exponent)) + 1
        return (int(pow(self.radix, self.parameter)) - 1) // (self.radix - 1)


def fermat_radix_reinterpretation(index: int, radix: int) -> CyclotomicRadixWordSpec:
    return CyclotomicRadixWordSpec("fermat", int(index), int(radix))


def mersenne_radix_reinterpretation(
    exponent: int, radix: int
) -> CyclotomicRadixWordSpec:
    return CyclotomicRadixWordSpec("mersenne", int(exponent), int(radix))


def fermat_number(index: int) -> int:
    return FermatNumberSpec(int(index)).materialize()


def mersenne_number(exponent: int) -> int:
    return MersenneNumberSpec(int(exponent)).materialize()


def fermat_successor(value: int) -> int:
    """Polynomial generation recurrence ``F_(n+1)=(F_n-1)^2+1``."""
    value = int(value)
    if value < 3:
        raise ValueError(value)
    return (value - 1) * (value - 1) + 1


def mersenne_successor(value: int) -> int:
    """Exponent-by-one recurrence ``M_(n+1)=2*M_n+1``."""
    value = int(value)
    if value < 1:
        raise ValueError(value)
    return 2 * value + 1


def fermat_previous_product(index: int) -> int:
    """Return ``prod(F_0..F_(n-1)) = F_n-2`` for bounded materialized ``n``."""
    index = int(index)
    if index < 0:
        raise ValueError(index)
    return FermatNumberSpec(index).materialize() - 2


def mersenne_gcd_spec(first_exponent: int, second_exponent: int) -> MersenneNumberSpec:
    """Symbolic form of ``gcd(M_a,M_b)=M_gcd(a,b)``."""
    a, b = int(first_exponent), int(second_exponent)
    if a <= 0 or b <= 0:
        raise ValueError((a, b))
    return MersenneNumberSpec(gcd(a, b))


def special_modulus_matches(family: str, parameter: int, modulus: int) -> bool:
    """Validate a concrete Fermat/Mersenne modulus without duplicate huge powers."""
    family, parameter, modulus = str(family), int(parameter), int(modulus)
    if family == "fermat":
        m = modulus - 1
        exponent = m.bit_length() - 1 if m > 0 else -1
        return (
            parameter >= 0
            and m > 0
            and not (m & (m - 1))
            and exponent > 0
            and not (exponent & (exponent - 1))
            and exponent.bit_length() - 1 == parameter
        )
    if family == "mersenne":
        m = modulus + 1
        return (
            parameter >= 2
            and m > 0
            and not (m & (m - 1))
            and m.bit_length() - 1 == parameter
        )
    raise ValueError(family)


def mersenne_exponent_is_prime(exponent: int) -> bool:
    """Decide the exponent gate without producing an unnecessary factor.

    Mersenne primality only reaches the number-level theorem when the exponent
    itself is prime.  For machine-word exponents the repository already has an
    exact deterministic Miller--Rabin predicate, so do not trial-divide all the
    way to sqrt(p) merely to learn the same Boolean.  Larger Python integers
    retain the exact historical factor-producing fallback.
    """
    n = int(exponent)
    if n < 2:
        return False
    if n < (1 << 64):
        return is_prime_u64(n)
    return smallest_factor(n) is None


def mersenne_composite_exponent_factor(
    exponent: int, *, max_divisor: int | None = None
) -> MersenneNumberSpec | None:
    """Return a symbolic proper Mersenne divisor when the exponent is composite."""
    n = int(exponent)
    if n <= 1:
        raise ValueError(n)
    factor = smallest_factor(n, max_divisor=max_divisor)
    return None if factor is None else MersenneNumberSpec(factor)


def fermat_factor_stride(index: int) -> int:
    """Stride forced on prime divisors of ``F_n`` for ``n>=2``."""
    index = int(index)
    if index < 2:
        raise ValueError(index)
    return 1 << (index + 2)


def mersenne_factor_stride(exponent: int) -> int:
    """Every prime divisor of ``2**p-1`` for prime ``p`` is ``1 mod 2p``."""
    exponent = int(exponent)
    if exponent < 2:
        raise ValueError(exponent)
    return 2 * exponent


__all__ = [
    "CyclotomicRadixWordSpec",
    "FermatNumberSpec",
    "MersenneNumberSpec",
    "fermat_factor_stride",
    "fermat_number",
    "fermat_previous_product",
    "fermat_radix_reinterpretation",
    "fermat_successor",
    "mersenne_composite_exponent_factor",
    "mersenne_exponent_is_prime",
    "mersenne_factor_stride",
    "mersenne_gcd_spec",
    "mersenne_number",
    "mersenne_radix_reinterpretation",
    "mersenne_successor",
    "special_modulus_matches",
]

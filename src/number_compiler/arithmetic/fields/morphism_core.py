"""Shared composition kernels for all powered sequence families.

The repository has several domain-specific state spaces, but their temporal
algebra is much smaller than those state spaces:

* binary powering is one monoid algorithm;
* affine forcing is one cocycle law ``(A,b);(C,d)=(CA,Cb+d)``;
* Collatz branch/slab maps use the same law with a dyadic denominator; and
* Fermat squaring, Lucas--Lehmer traces, and the real 2-power cyclotomic tower
  are coordinate views of the degree-two endomorphism ``y -> y**2``.

This module owns those generic laws.  Domain modules retain only validation,
observers, and their concrete ring operations.  Nothing here materializes an
orbit or claims that a branch observer is closed.
"""

from __future__ import annotations

from collections.abc import Callable, Hashable
from dataclasses import dataclass
from typing import Generic, TypeVar

T = TypeVar("T")
K = TypeVar("K", bound=Hashable)
V = TypeVar("V")
E = TypeVar("E")


@dataclass(frozen=True, slots=True)
class InternedEffectNode(Generic[E]):
    """Shared node wrapper for hash-consed extensional effect arenas.

    The numeric id is arena-local construction identity; ``effect`` is the
    canonical semantic payload.  Domain arenas should not define parallel
    two-field node classes for the same invariant.
    """

    node_id: int
    effect: E

    def __post_init__(self) -> None:
        if int(self.node_id) <= 0:
            raise ValueError(self.node_id)
        object.__setattr__(self, "node_id", int(self.node_id))


class LazyLoweringCache(Generic[K, V]):
    """Tiny shared cache separating morphism descriptors from heavy lowering.

    The cache has no domain semantics: callers provide a canonical key and a
    lowering closure.  It exists so polynomial coefficients, affine offsets,
    matrices, or other large carriers are created only at explicit observer
    boundaries rather than during morphism composition.
    """

    __slots__ = ("_values", "hits", "misses")

    def __init__(self) -> None:
        self._values: dict[K, V] = {}
        self.hits = 0
        self.misses = 0

    @property
    def size(self) -> int:
        return len(self._values)

    def get_or_lower(self, key: K, lower: Callable[[], V]) -> V:
        try:
            value = self._values[key]
        except KeyError:
            value = lower()
            self._values[key] = value
            self.misses += 1
            return value
        self.hits += 1
        return value

    def peek(self, key: K) -> V | None:
        return self._values.get(key)


@dataclass(frozen=True, slots=True)
class BinaryPowerResult(Generic[T]):
    """Result of exponentiation by squaring with the charged compose count."""

    value: T
    compositions: int


def binary_power(
    base: T,
    exponent: int,
    *,
    identity: T,
    compose: Callable[[T, T], T],
) -> BinaryPowerResult[T]:
    """Return ``base`` repeated ``exponent`` times by shared binary composition.

    ``compose(first, second)`` must mean "apply/concatenate ``first`` and then
    ``second``".  The returned composition count charges only newly executed
    semantic compositions; construction history inside an operand is not
    recursively re-charged.
    """
    if type(exponent) is not int:
        raise TypeError("binary power exponent must be an exact integer")
    n = exponent
    if n < 0:
        raise ValueError(n)
    result = identity
    power = base
    operations = 0
    while n:
        if n & 1:
            result = compose(result, power)
            operations += 1
        n >>= 1
        if n:
            power = compose(power, power)
            operations += 1
    return BinaryPowerResult(result, operations)


def binary_power_composition_count(exponent: int) -> int:
    """Number of compose calls made by :func:`binary_power`."""
    if type(exponent) is not int:
        raise TypeError("binary power exponent must be an exact integer")
    n = exponent
    if n < 0:
        raise ValueError(n)
    return 0 if n == 0 else n.bit_count() + n.bit_length() - 1


def modular_power(base: int, exponent: int, modulus: int) -> BinaryPowerResult[int]:
    """Shared multiplicative-monoid power with an exact composition count."""
    if any(type(value) is not int for value in (base, exponent, modulus)):
        raise TypeError("modular power requires exact integers")
    if modulus <= 1:
        raise ValueError(modulus)
    return binary_power(
        base % modulus,
        exponent,
        identity=1 % modulus,
        compose=lambda first, second: (first * second) % modulus,
    )


@dataclass(frozen=True, slots=True)
class AffineCocycle(Generic[T]):
    """Ring-agnostic affine payload ``x -> multiplier*x + addend``.

    Ring arithmetic is deliberately supplied by the caller.  This keeps one
    semantic representation shared by integer, modular, polynomial and
    cyclotomic carriers without putting domain-specific arithmetic in this
    module.
    """

    multiplier: T
    addend: T

    def then(
        self,
        other: AffineCocycle[T],
        *,
        multiply: Callable[[T, T], T],
        add: Callable[[T, T], T],
    ) -> AffineCocycle[T]:
        # self first, then other: (B,d)o(A,c)=(BA,Bc+d).
        return AffineCocycle(
            multiply(other.multiplier, self.multiplier),
            add(multiply(other.multiplier, self.addend), other.addend),
        )

    def apply(
        self,
        value: T,
        *,
        multiply: Callable[[T, T], T],
        add: Callable[[T, T], T],
    ) -> T:
        return add(multiply(self.multiplier, value), self.addend)


@dataclass(frozen=True, slots=True)
class DyadicAffineCocycle:
    """Exact integer affine map ``x -> (a*x+b)/2**shift``.

    This is the shared linear/translation representation used by known Collatz
    branch words and parity slabs.  Domain admissibility remains outside this
    object because it is an observer property, not part of affine algebra.
    """

    multiplier: int
    addend: int
    shift: int

    def __post_init__(self) -> None:
        if int(self.multiplier) <= 0 or int(self.addend) < 0 or int(self.shift) < 0:
            raise ValueError(self)
        object.__setattr__(self, "multiplier", int(self.multiplier))
        object.__setattr__(self, "addend", int(self.addend))
        object.__setattr__(self, "shift", int(self.shift))

    @classmethod
    def identity(cls) -> DyadicAffineCocycle:
        return cls(1, 0, 0)

    def then(self, other: DyadicAffineCocycle) -> DyadicAffineCocycle:
        # other((a*x+b)/2^s) = (c*a*x + c*b + d*2^s)/2^(s+t)
        return DyadicAffineCocycle(
            other.multiplier * self.multiplier,
            other.multiplier * self.addend + (other.addend << self.shift),
            self.shift + other.shift,
        )

    def square(self) -> DyadicAffineCocycle:
        """Self-compose using the closed affine square law."""
        return DyadicAffineCocycle(
            self.multiplier * self.multiplier,
            self.addend * (self.multiplier + (1 << self.shift)),
            self.shift * 2,
        )

    def power(self, exponent: int) -> BinaryPowerResult[DyadicAffineCocycle]:
        return binary_power(
            self,
            exponent,
            identity=DyadicAffineCocycle.identity(),
            compose=DyadicAffineCocycle.then,
        )

    def numerator(self, value: int) -> int:
        return self.multiplier * int(value) + self.addend

    def apply_exact(self, value: int) -> int:
        numerator = self.numerator(value)
        divisor = 1 << self.shift
        if numerator % divisor:
            raise ValueError("dyadic affine map is not integral on this input")
        return numerator // divisor


@dataclass(frozen=True, slots=True)
class QuadraticPower:
    """Power of the universal degree-two endomorphism ``y -> y**2``.

    ``depth`` represents ``y -> y**(2**depth)``.  Fermat uses the multiplicative
    coordinate directly.  Mersenne and the real 2-power cyclotomic tower use the
    inversion quotient ``u=y+y^-1``, whose one-step map is ``u -> u**2-2``.
    """

    depth: int = 0

    def __post_init__(self) -> None:
        if int(self.depth) < 0:
            raise ValueError(self.depth)
        object.__setattr__(self, "depth", int(self.depth))

    @classmethod
    def identity(cls) -> QuadraticPower:
        return cls(0)

    @classmethod
    def atom(cls) -> QuadraticPower:
        return cls(1)

    def then(self, other: QuadraticPower) -> QuadraticPower:
        return QuadraticPower(self.depth + other.depth)

    def power(self, exponent: int) -> BinaryPowerResult[QuadraticPower]:
        return binary_power(
            self,
            exponent,
            identity=QuadraticPower.identity(),
            compose=QuadraticPower.then,
        )

    def apply_iterated(self, value: T, *, step: Callable[[T], T]) -> T:
        """Apply the represented degree-two depth in any coordinate.

        This is the shared bridge used by non-scalar coordinate lifts such as
        the reverse-add real-cyclotomic polynomial tower.  The family supplies
        only its one-step coordinate map; temporal depth remains this object.
        """
        out = value
        for _ in range(self.depth):
            out = step(out)
        return out

    def apply_multiplicative(self, value: int, modulus: int) -> int:
        modulus = int(modulus)
        if modulus <= 1:
            raise ValueError(modulus)
        # pow's exponent has only depth+1 bits even though its value is 2**depth.
        return pow(int(value) % modulus, 1 << self.depth, modulus)

    def apply_trace(self, value: int, modulus: int) -> int:
        modulus = int(modulus)
        if modulus <= 1:
            raise ValueError(modulus)
        return self.apply_iterated(
            int(value) % modulus,
            step=lambda item: trace_square(item, modulus),
        )


def multiplicative_square(value: int, modulus: int | None = None) -> int:
    out = int(value) * int(value)
    return out if modulus is None else out % int(modulus)


def trace_square(value: int, modulus: int | None = None) -> int:
    """The inversion-quotient square map ``u -> u**2 - 2``."""
    out = int(value) * int(value) - 2
    return out if modulus is None else out % int(modulus)


__all__ = [
    "AffineCocycle",
    "BinaryPowerResult",
    "DyadicAffineCocycle",
    "InternedEffectNode",
    "LazyLoweringCache",
    "QuadraticPower",
    "binary_power",
    "binary_power_composition_count",
    "modular_power",
    "multiplicative_square",
    "trace_square",
]

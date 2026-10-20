"""Canonical integer congruence intersection and affine preimages."""

from __future__ import annotations

from math import gcd

Congruence = tuple[int, int]


def exact_modular_power(base: int, exponent: int, modulus: int) -> int:
    """Return the built-in signed modular power as an exact integer.

    The object boundary narrows the standard-library overload without
    changing Python's errors for zero moduli or noninvertible negative powers.
    """
    result: object = pow(base, exponent, modulus)
    if type(result) is not int:
        raise TypeError("modular integer power returned another sort")
    return result


def _require_congruence(value: Congruence) -> None:
    residue, modulus = value
    if type(residue) is not int or type(modulus) is not int:
        raise TypeError("congruence coordinates must be exact integers")
    if modulus < 1 or not 0 <= residue < modulus:
        raise ValueError("congruence coordinates must be canonical")


def join_congruences(left: Congruence, right: Congruence) -> Congruence | None:
    """Intersect two residue classes, including noncoprime moduli."""
    _require_congruence(left)
    _require_congruence(right)
    r, m = left
    s, n = right
    divisor = gcd(m, n)
    if (s - r) % divisor:
        return None
    other = n // divisor
    coefficient = (
        0 if other == 1 else ((s - r) // divisor * pow(m // divisor, -1, other)) % other
    )
    modulus = m * other
    return (r + m * coefficient) % modulus, modulus


def affine_preimage(
    target: Congruence, *, gain: int, offset: int, denominator: int
) -> Congruence | None:
    """Sources whose integral (gain*x+offset)/denominator is in target."""
    _require_congruence(target)
    if any(type(value) is not int for value in (gain, offset, denominator)):
        raise TypeError("affine coordinates must be exact integers")
    if denominator < 1:
        raise ValueError("affine denominator must be positive")
    residue, modulus = target
    lifted = denominator * modulus
    rhs = denominator * residue - offset
    divisor = gcd(gain, lifted)
    if rhs % divisor:
        return None
    reduced = lifted // divisor
    if reduced == 1:
        return 0, 1
    return (rhs // divisor * pow(gain // divisor, -1, reduced)) % reduced, reduced

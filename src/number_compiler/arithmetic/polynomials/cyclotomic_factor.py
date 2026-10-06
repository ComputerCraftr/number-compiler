"""Finite-field and prime-power factorization/CRT for cyclotomic rings.

Factoring and CRT are construction-time algebra, not temporal sequence state.
Keeping them separate prevents the core cyclotomic transport module from also
becoming a second polynomial-arithmetic/factorization implementation.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from functools import cache
from math import gcd

from number_compiler.arithmetic.number_theory import smallest_factor
from number_compiler.arithmetic.polynomials.cyclotomic import (
    cyclotomic_coefficients,
    cyclotomic_power_coefficients,
)
from number_compiler.arithmetic.polynomials.modular_linear import row_reduce_mod_prime
from number_compiler.arithmetic.polynomials.polynomial import (
    MonicPolynomialRing,
    evaluate_polynomial,
    polynomial_divide_exact,
    polynomial_multiply,
    polynomial_remainder_monic,
    trim_polynomial,
)


def multiplicative_order_mod(value: int, modulus: int) -> int:
    """Return the multiplicative order of ``value`` modulo ``modulus``.

    The arguments must be coprime.  This small exact helper is used to predict
    the degree of irreducible finite-field factors of ``Phi_m``: when
    ``gcd(prime, m)=1``, every factor of ``Phi_m`` over ``F_prime`` has degree
    ``ord_m(prime)``.
    """

    value, modulus = int(value), int(modulus)
    if modulus <= 1 or gcd(value, modulus) != 1:
        raise ValueError((value, modulus))
    value %= modulus
    power = value
    order = 1
    while power != 1:
        power = (power * value) % modulus
        order += 1
        if order > modulus:
            raise AssertionError((value, modulus))
    return order


def _poly_trim_mod(coefficients: Sequence[int], prime: int) -> tuple[int, ...]:
    p = int(prime)
    out = [int(value) % p for value in coefficients] or [0]
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return tuple(out)


def _poly_divmod_prime(
    numerator: Sequence[int],
    denominator: Sequence[int],
    prime: int,
) -> tuple[tuple[int, ...], tuple[int, ...]]:
    p = int(prime)
    if p <= 1:
        raise ValueError(p)
    a = list(_poly_trim_mod(numerator, p))
    b = _poly_trim_mod(denominator, p)
    if b == (0,):
        raise ZeroDivisionError
    if len(a) < len(b):
        return (0,), tuple(a)
    inverse = pow(b[-1], -1, p)
    q = [0] * (len(a) - len(b) + 1)
    while len(a) >= len(b) and any(a):
        coefficient = a[-1] * inverse % p
        shift = len(a) - len(b)
        q[shift] = coefficient
        for index, value in enumerate(b):
            a[shift + index] = (a[shift + index] - coefficient * value) % p
        while len(a) > 1 and a[-1] == 0:
            a.pop()
    return _poly_trim_mod(q, p), _poly_trim_mod(a, p)


def _poly_monic_prime(coefficients: Sequence[int], prime: int) -> tuple[int, ...]:
    p = int(prime)
    poly = _poly_trim_mod(coefficients, p)
    if poly == (0,):
        return poly
    inverse = pow(poly[-1], -1, p)
    return tuple(value * inverse % p for value in poly)


def _poly_gcd_prime(
    first: Sequence[int],
    second: Sequence[int],
    prime: int,
) -> tuple[int, ...]:
    p = int(prime)
    a = _poly_trim_mod(first, p)
    b = _poly_trim_mod(second, p)
    while b != (0,):
        _q, r = _poly_divmod_prime(a, b, p)
        a, b = b, r
    return _poly_monic_prime(a, p)


def _poly_power_mod_prime(
    coefficients: Sequence[int],
    exponent: int,
    divisor: Sequence[int],
    prime: int,
) -> tuple[int, ...]:
    exponent = int(exponent)
    if exponent < 0:
        raise ValueError(exponent)
    ring = MonicPolynomialRing(tuple(divisor), int(prime))
    return tuple(ring.power(coefficients, exponent).value)


def _nullspace_mod_prime(
    matrix: Sequence[Sequence[int]], prime: int
) -> tuple[tuple[int, ...], ...]:
    """Return a deterministic row-vector basis for a matrix nullspace over ``F_p``."""
    p = int(prime)
    rows, pivot_cols = row_reduce_mod_prime(matrix, p)
    if not rows:
        return ()
    ncols = len(rows[0])
    free_cols = [c for c in range(ncols) if c not in set(pivot_cols)]
    basis: list[tuple[int, ...]] = []
    for free in free_cols:
        vector = [0] * ncols
        vector[free] = 1
        for row_index, pivot_col in reversed(tuple(enumerate(pivot_cols))):
            vector[pivot_col] = (-rows[row_index][free]) % p
        basis.append(tuple(vector))
    return tuple(basis)


def _berlekamp_basis(poly: Sequence[int], prime: int) -> tuple[tuple[int, ...], ...]:
    p = int(prime)
    f = _poly_monic_prime(poly, p)
    degree = len(f) - 1
    if degree <= 0:
        return ()
    columns = []
    for j in range(degree):
        columns.append(_poly_power_mod_prime((0, 1), p * j, f, p))
    matrix = []
    for i in range(degree):
        row = []
        for j in range(degree):
            value = columns[j][i] if i < len(columns[j]) else 0
            row.append((value - int(i == j)) % p)
        matrix.append(row)
    return _nullspace_mod_prime(matrix, p)


def _factor_squarefree_prime(
    poly: Sequence[int], prime: int
) -> tuple[tuple[int, ...], ...]:
    """Deterministic Berlekamp factorization for one monic squarefree polynomial."""
    from itertools import product

    p = int(prime)
    pending = [_poly_monic_prime(poly, p)]
    factors: list[tuple[int, ...]] = []
    while pending:
        f = pending.pop()
        degree = len(f) - 1
        if degree <= 1:
            factors.append(f)
            continue
        basis = _berlekamp_basis(f, p)
        if len(basis) <= 1:
            factors.append(f)
            continue
        # A squarefree polynomial with r irreducible factors has an
        # r-dimensional Berlekamp nullspace.  Enumerating its small finite span
        # is deterministic and avoids probabilistic splitting.
        combinations = p ** len(basis)
        if combinations > 4096:
            raise ValueError(("berlekamp-span-too-large", degree, p, len(basis)))
        split: tuple[tuple[int, ...], tuple[int, ...]] | None = None
        for coefficients in product(range(p), repeat=len(basis)):
            if not any(coefficients):
                continue
            candidate = [0] * degree
            for scalar, vector in zip(coefficients, basis, strict=True):
                if not scalar:
                    continue
                for index, value in enumerate(vector):
                    candidate[index] = (candidate[index] + scalar * value) % p
            for constant in range(p):
                shifted = list(candidate)
                shifted[0] = (shifted[0] - constant) % p
                divisor = _poly_gcd_prime(f, shifted, p)
                if 1 < len(divisor) < len(f):
                    quotient, remainder = _poly_divmod_prime(f, divisor, p)
                    if remainder != (0,):
                        raise AssertionError((f, divisor, remainder))
                    split = (divisor, quotient)
                    break
            if split is not None:
                break
        if split is None:
            raise AssertionError(("berlekamp-failed", f, p, basis))
        # Stack order is irrelevant because the final factor tuple is sorted.
        pending.extend(split)
    return tuple(sorted(factors))


def polynomial_inverse_mod_prime(
    coefficients: Sequence[int],
    divisor: Sequence[int],
    prime: int,
) -> tuple[int, ...]:
    """Invert one nonzero polynomial modulo a monic irreducible over ``F_p``."""
    p = int(prime)
    mod = _poly_monic_prime(divisor, p)
    degree = len(mod) - 1
    value = polynomial_remainder_monic(coefficients, mod, modulus=p)
    if not any(value):
        raise ValueError("zero polynomial is not invertible")
    # In the degree-d finite field every nonzero element has order dividing
    # p**d-1.  Exponentiation avoids a second polynomial-Euclid primitive.
    inverse = _poly_power_mod_prime(value, p**degree - 2, mod, p)
    product = polynomial_remainder_monic(
        polynomial_multiply(value, inverse),
        mod,
        modulus=p,
    )
    if product != (1,) + (0,) * (degree - 1):
        raise ValueError(("polynomial-not-unit", value, mod, p))
    return inverse


def polynomial_crt_mod_prime(
    residues: Sequence[Sequence[int]],
    moduli: Sequence[Sequence[int]],
    prime: int,
) -> tuple[int, ...]:
    """Reconstruct one polynomial residue from pairwise-coprime factors over ``F_p``."""
    p = int(prime)
    mods = tuple(_poly_monic_prime(modulus, p) for modulus in moduli)
    rs = tuple(tuple(int(v) % p for v in residue) for residue in residues)
    if not mods or len(mods) != len(rs):
        raise ValueError((len(rs), len(mods)))
    total: tuple[int, ...] = (1,)
    for modulus in mods:
        total = _poly_monic_prime(polynomial_multiply(total, modulus), p)
    degree = len(total) - 1
    out = (0,) * degree
    for i, (residue, modulus) in enumerate(zip(rs, mods, strict=True)):
        for j in range(i):
            if _poly_gcd_prime(modulus, mods[j], p) != (1,):
                raise ValueError(("non-coprime-crt-moduli", modulus, mods[j]))
        cofactor, remainder = _poly_divmod_prime(total, modulus, p)
        if remainder != (0,):
            raise AssertionError((total, modulus, remainder))
        inverse = polynomial_inverse_mod_prime(cofactor, modulus, p)
        term = polynomial_multiply(polynomial_multiply(residue, cofactor), inverse)
        term = polynomial_remainder_monic(term, total, modulus=p)
        out = tuple((a + b) % p for a, b in zip(out, term, strict=True))
    return polynomial_remainder_monic(out, total, modulus=p)


@cache
def cyclotomic_factors_mod_prime(order: int, prime: int) -> tuple[tuple[int, ...], ...]:
    """Factor ``Phi_order`` into monic irreducibles over ``F_prime``.

    The coefficient modulus must be prime and coprime to ``order``.  Under this
    condition the cyclotomic polynomial is separable, every returned factor has
    degree ``ord_order(prime)``, and their product is exactly ``Phi_order``
    modulo ``prime``.  This exposes the finite-field primary components hidden
    inside a whole cyclotomic channel without introducing a second digit state.
    """

    n, p = int(order), int(prime)
    if n <= 0 or p <= 1 or smallest_factor(p) is not None or gcd(n, p) != 1:
        raise ValueError((n, p))
    source = _poly_monic_prime(cyclotomic_coefficients(n), p)
    derivative = tuple((i * source[i]) % p for i in range(1, len(source))) or (0,)
    if _poly_gcd_prime(source, derivative, p) != (1,):
        raise ValueError(("inseparable-cyclotomic", n, p))
    factors = tuple(sorted(_factor_squarefree_prime(source, p)))
    expected_degree = multiplicative_order_mod(p, n) if n > 1 else 1
    if any(len(factor) - 1 != expected_degree for factor in factors):
        raise AssertionError((n, p, expected_degree, factors))
    product_poly: tuple[int, ...] = (1,)
    for factor in factors:
        product_poly = tuple(
            value % p for value in polynomial_multiply(product_poly, factor)
        )
    if _poly_monic_prime(product_poly, p) != source:
        raise AssertionError((n, p, source, factors, product_poly))
    return factors


@dataclass(frozen=True, slots=True)
class CyclotomicLinearFactorProfile:
    """Exact finite-module profile of multiplication by ``base-z``.

    For monic ``F`` the integer cokernel of multiplication by ``base-z`` on
    ``Z[z]/F`` is cyclic of order ``abs(F(base))``.  After reducing coefficients
    modulo ``q`` this immediately gives the kernel/cokernel size
    ``gcd(q,F(base))`` without constructing a dense matrix or enumerating states.
    """

    order: int
    power: int
    base: int
    modulus: int
    degree: int
    evaluation: int
    kernel_size: int
    image_size: int
    cokernel_size: int

    @property
    def unit(self) -> bool:
        return self.kernel_size == 1


def cyclotomic_linear_factor_profile(
    order: int,
    base: int,
    modulus: int,
    *,
    power: int = 1,
) -> CyclotomicLinearFactorProfile:
    order, base, modulus, power = map(int, (order, base, modulus, power))
    if order <= 0 or modulus <= 1 or power <= 0:
        raise ValueError((order, base, modulus, power))
    divisor = cyclotomic_power_coefficients(order, power)
    degree = len(divisor) - 1
    value = evaluate_polynomial(divisor, base)
    kernel = gcd(abs(value), modulus)
    states = modulus**degree
    return CyclotomicLinearFactorProfile(
        order,
        power,
        base,
        modulus,
        degree,
        value,
        kernel,
        states // kernel,
        kernel,
    )


def _pad_polynomial(values: Sequence[int], length: int) -> list[int]:
    out = list(map(int, values))
    if len(out) > int(length):
        raise ValueError((len(out), length))
    out += [0] * (int(length) - len(out))
    return out


@cache
def cyclotomic_factors_mod_prime_power(
    order: int,
    prime: int,
    precision: int,
) -> tuple[tuple[int, ...], ...]:
    """Hensel-lift separable ``Phi_order`` factors to ``Z/p**precision``.

    ``gcd(order,p)=1`` is required.  Ramified/repeated-root channels must stay
    as one primary component; :func:`cyclotomic_primary_components` provides
    that fail-honest wrapper.
    """
    n, p, k = int(order), int(prime), int(precision)
    if n <= 0 or p <= 1 or k <= 0 or smallest_factor(p) is not None or gcd(n, p) != 1:
        raise ValueError((n, p, k))
    base_factors = cyclotomic_factors_mod_prime(n, p)
    if k == 1:
        return base_factors
    source = cyclotomic_coefficients(n)
    lifted = [tuple(int(c) % p for c in factor) for factor in base_factors]
    # Lift one p-adic digit per round.  Cross-products of corrections are
    # divisible by p**(e+1) once e>=1.
    modulus = p
    for _e in range(1, k):
        product_poly: tuple[int, ...] = (1,)
        for factor in lifted:
            product_poly = polynomial_multiply(product_poly, factor)
        length = max(len(source), len(product_poly))
        src = _pad_polynomial(source, length)
        prod = _pad_polynomial(product_poly, length)
        error = []
        for a, b in zip(src, prod, strict=True):
            delta = a - b
            if delta % modulus:
                raise AssertionError((n, p, k, modulus, delta))
            error.append((delta // modulus) % p)
        error_poly = tuple(trim_polynomial(error))
        new_modulus = modulus * p
        next_factors: list[tuple[int, ...]] = []
        # Mod p, the lifted factors are still the original pairwise-coprime
        # irreducibles, so the multifactor Hensel correction splits by CRT.
        for i, (factor, base_factor) in enumerate(
            zip(lifted, base_factors, strict=True)
        ):
            cofactor: tuple[int, ...] = (1,)
            for j, other in enumerate(base_factors):
                if i != j:
                    cofactor = polynomial_multiply(cofactor, other)
            inverse = polynomial_inverse_mod_prime(cofactor, base_factor, p)
            e_i = polynomial_remainder_monic(error_poly, base_factor, modulus=p)
            correction = polynomial_remainder_monic(
                polynomial_multiply(e_i, inverse),
                base_factor,
                modulus=p,
            )
            coeffs = _pad_polynomial(factor, len(base_factor))
            for index in range(len(base_factor) - 1):
                coeffs[index] = (
                    coeffs[index] + modulus * correction[index]
                ) % new_modulus
            coeffs[-1] = 1
            next_factors.append(tuple(coeffs))
        lifted = next_factors
        modulus = new_modulus
    q = p**k
    product_poly = (1,)
    for factor in lifted:
        product_poly = polynomial_multiply(product_poly, factor)
    source_mod = tuple(int(c) % q for c in source)
    prod_mod = tuple(int(c) % q for c in product_poly)
    length = max(len(source_mod), len(prod_mod))
    if tuple(_pad_polynomial(source_mod, length)) != tuple(
        _pad_polynomial(prod_mod, length)
    ):
        raise AssertionError((n, p, k, source_mod, prod_mod))
    return tuple(lifted)


def cyclotomic_primary_components(
    order: int,
    prime: int,
    precision: int,
) -> tuple[tuple[int, ...], ...]:
    """Return canonical ``p**k`` primary components, preserving ramification.

    Separable channels are Hensel-lifted factor-by-factor.  If ``p`` divides the
    cyclotomic order, reduction has repeated roots and no coprime CRT split is
    sound; the whole cyclotomic polynomial is therefore returned as one primary
    component modulo ``p**k``.
    """
    n, p, k = int(order), int(prime), int(precision)
    if n <= 0 or p <= 1 or k <= 0 or smallest_factor(p) is not None:
        raise ValueError((n, p, k))
    q = p**k
    if gcd(n, p) != 1:
        source = cyclotomic_coefficients(n)
        return (tuple(int(c) % q for c in source),)
    return cyclotomic_factors_mod_prime_power(n, p, k)


def _prime_power_modulus(prime: int, precision: int) -> tuple[int, int, int]:
    p, k = int(prime), int(precision)
    if p <= 1 or k <= 0 or smallest_factor(p) is not None:
        raise ValueError((p, k))
    return p, k, p**k


def polynomial_inverse_mod_prime_power(
    coefficients: Sequence[int],
    divisor: Sequence[int],
    prime: int,
    precision: int,
) -> tuple[int, ...]:
    """Invert a polynomial modulo one unramified ``p**k`` primary factor.

    An inverse modulo ``p`` is lifted by Newton iteration ``y <- y*(2-a*y)``;
    each round doubles p-adic precision.  A nonunit fails closed at the base
    finite-field inverse rather than fabricating a partial inverse.
    """
    p, k, q = _prime_power_modulus(prime, precision)
    div = tuple(int(c) % q for c in trim_polynomial(divisor))
    if not div or div[-1] % q != 1:
        raise ValueError("divisor must be monic")
    base_div = tuple(int(c) % p for c in div)
    inverse = polynomial_inverse_mod_prime(coefficients, base_div, p)
    exponent = 1
    while exponent < k:
        next_exponent = min(2 * exponent, k)
        modulus = p**next_exponent
        ay = polynomial_remainder_monic(
            polynomial_multiply(coefficients, inverse),
            div,
            modulus=modulus,
        )
        correction = [(-v) % modulus for v in ay]
        correction[0] = (correction[0] + 2) % modulus
        inverse = polynomial_remainder_monic(
            polynomial_multiply(inverse, correction),
            div,
            modulus=modulus,
        )
        exponent = next_exponent
    degree = len(div) - 1
    product = polynomial_remainder_monic(
        polynomial_multiply(coefficients, inverse),
        div,
        modulus=q,
    )
    if product != (1,) + (0,) * (degree - 1):
        raise ValueError(
            ("polynomial-not-unit-mod-prime-power", coefficients, div, p, k)
        )
    return inverse


def polynomial_crt_mod_prime_power(
    residues: Sequence[Sequence[int]],
    moduli: Sequence[Sequence[int]],
    prime: int,
    precision: int,
) -> tuple[int, ...]:
    """CRT-reconstruct pairwise-coprime Hensel components modulo ``p**k``."""
    p, k, q = _prime_power_modulus(prime, precision)
    mods = tuple(tuple(int(c) % q for c in trim_polynomial(m)) for m in moduli)
    rs = tuple(tuple(int(c) % q for c in residue) for residue in residues)
    if not mods or len(mods) != len(rs) or any(m[-1] % q != 1 for m in mods):
        raise ValueError((len(rs), len(mods)))
    total: tuple[int, ...] = (1,)
    for modulus_poly in mods:
        total = polynomial_multiply(total, modulus_poly)
    total = tuple(int(c) % q for c in total)
    degree = len(total) - 1
    out = (0,) * degree
    for i, (residue, modulus_poly) in enumerate(zip(rs, mods, strict=True)):
        cofactor = polynomial_divide_exact(total, modulus_poly)
        if cofactor is None:
            # Exact integer division can fail because coefficients are canonical
            # residues modulo q.  Rebuild the cofactor from the other factors.
            cofactor = (1,)
            for j, other in enumerate(mods):
                if i != j:
                    cofactor = polynomial_multiply(cofactor, other)
        inverse = polynomial_inverse_mod_prime_power(cofactor, modulus_poly, p, k)
        term = polynomial_remainder_monic(
            polynomial_multiply(polynomial_multiply(residue, cofactor), inverse),
            total,
            modulus=q,
        )
        out = tuple((a + b) % q for a, b in zip(out, term, strict=True))
    return polynomial_remainder_monic(out, total, modulus=q)


__all__ = [
    "CyclotomicLinearFactorProfile",
    "cyclotomic_factors_mod_prime",
    "cyclotomic_factors_mod_prime_power",
    "cyclotomic_linear_factor_profile",
    "cyclotomic_primary_components",
    "multiplicative_order_mod",
    "polynomial_crt_mod_prime",
    "polynomial_crt_mod_prime_power",
    "polynomial_inverse_mod_prime",
    "polynomial_inverse_mod_prime_power",
]

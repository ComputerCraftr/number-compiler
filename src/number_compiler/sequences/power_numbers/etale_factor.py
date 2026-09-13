"""Candidate-derived quadratic etale defects and optional factor output.

A nonzero Frobenius additivity defect proves compositeness under the stated
special-family premises. A zero defect is NOT a primality certificate.
The binary power performs linear-in-candidate-bit-length ring work; gcd output
adds no factor search but is not a constant-time or universal factorization.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.sequences.power_numbers.numbers import (
    fermat_number,
    mersenne_number,
)


@dataclass(frozen=True, slots=True)
class MersenneAdditiveEtaleFrobeniusProbe:
    """Specific Frobenius-additivity probe in the LL quadratic algebra.

    Work in ``R[s]/(s^2-3)`` and test the additive element ``3+s``.  On a
    prime Mersenne field, ``s^N=-s`` and characteristic-N Frobenius gives
    ``(3+s)^N=3-s``.  A nonzero defect is an exact composite witness.  A zero
    defect is not promoted to primality, and the exponentiation still has the
    same linear-in-p chain depth as the classical LL proof.
    """

    exponent: int
    candidate_modulus: int
    powered_value: tuple[int, int]
    expected_value: tuple[int, int]
    defect: tuple[int, int]
    nontrivial_gcds: tuple[int, ...]
    ring_multiplications: int
    composite_witness: bool
    prime_certificate: bool
    scalable: bool
    candidate_derived: bool = True
    factor_enumeration: int = 0


@dataclass(frozen=True, slots=True)
class FermatAdditiveEtaleFrobeniusProbe:
    """Candidate-only Frobenius additivity probe in the first missing layer.

    ``y`` alone is formally blind because ``y^N=y``.  The additive probe tests

        (1+y)^N == 1+y

    in ``R[y]/(y^2-r1)``.  A prime Fermat candidate must pass because the
    algebra is split over the field and characteristic-N Frobenius is the
    identity.  A nonzero defect is therefore an exact composite witness for
    n>=3.  A zero defect is *not* promoted to prime: quadratic/Frobenius
    pseudoprimes are not excluded by the present theorem.

    The implementation intentionally counts the raw candidate-ring products;
    this is a research probe, not a scalable terminal selector.
    """

    parameter: int
    candidate_modulus: int
    radicand: int
    powered_value: tuple[int, int]
    defect: tuple[int, int]
    nontrivial_gcds: tuple[int, ...]
    ring_multiplications: int
    composite_witness: bool
    prime_certificate: bool
    scalable: bool
    candidate_derived: bool = True
    factor_enumeration: int = 0


def _quadratic_mul_pair(
    left: tuple[int, int],
    right: tuple[int, int],
    radicand: int,
    modulus: int,
) -> tuple[int, int]:
    a, b = left
    c, d = right
    return (
        (a * c + b * d * radicand) % modulus,
        (a * d + b * c) % modulus,
    )


def _quadratic_power_pair(
    base: tuple[int, int],
    exponent: int,
    radicand: int,
    modulus: int,
) -> tuple[tuple[int, int], int]:
    result = (1, 0)
    current = (base[0] % modulus, base[1] % modulus)
    e = int(exponent)
    products = 0
    while e:
        if e & 1:
            result = _quadratic_mul_pair(result, current, radicand, modulus)
            products += 1
        e >>= 1
        if e:
            current = _quadratic_mul_pair(current, current, radicand, modulus)
            products += 1
    return result, products


def mersenne_additive_etale_frobenius_probe(
    exponent: int,
) -> MersenneAdditiveEtaleFrobeniusProbe:
    p = int(exponent)
    if p < 3 or not (p & 1):
        raise ValueError(p)
    N = mersenne_number(p)
    powered, products = _quadratic_power_pair((3, 1), N, 3, N)
    expected = (3 % N, (-1) % N)
    defect = ((powered[0] - expected[0]) % N, (powered[1] - expected[1]) % N)
    gcds = tuple(
        sorted(
            {
                factor
                for coefficient in defect
                if (factor := factor_from_coefficient(N, coefficient)) is not None
            }
        )
    )
    return MersenneAdditiveEtaleFrobeniusProbe(
        p,
        N,
        powered,
        expected,
        defect,
        gcds,
        products,
        defect != (0, 0),
        False,
        False,
    )


def fermat_additive_etale_frobenius_probe(
    parameter: int,
) -> FermatAdditiveEtaleFrobeniusProbe:
    n = int(parameter)
    if n < 3:
        raise ValueError(
            (n, "probe is only a composite witness after level-2 is required")
        )
    N = fermat_number(n)
    # r1=t+t^-1 is the canonical first root of 2 and is candidate-derived.
    t = pow(2, 1 << (n - 2), N)
    r1 = (t + pow(t, -1, N)) % N
    powered, products = _quadratic_power_pair((1, 1), N, r1, N)
    defect = ((powered[0] - 1) % N, (powered[1] - 1) % N)
    gcds = tuple(
        sorted(
            {
                factor
                for coefficient in defect
                if (factor := factor_from_coefficient(N, coefficient)) is not None
            }
        )
    )
    composite = defect != (0, 0)
    return FermatAdditiveEtaleFrobeniusProbe(
        n,
        N,
        r1,
        powered,
        defect,
        gcds,
        products,
        composite,
        False,
        False,
    )


def factor_from_etale_root(modulus: int, defect: int) -> int | None:
    """Print a proper gcd from a supplied, checked quadratic root.

    The Isabelle theorem ``nontrivial_etale_root_prints_factor`` guarantees
    success away from the two global roots 0 and -2. This function constructs
    neither the root nor a terminal clock: admission costs one modular product
    and factor output costs a gcd, with no factor enumeration.
    """
    if type(modulus) is not int or type(defect) is not int:
        raise TypeError("modulus and defect must be exact integers")
    if modulus <= 2 or not 0 <= defect < modulus:
        raise ValueError("expected a canonical defect and modulus greater than two")
    if defect * (defect + 2) % modulus:
        raise ValueError("defect is not a quadratic etale root")
    return factor_from_coefficient(modulus, defect)


def factor_probe_product_count(family: str, parameter: int) -> int:
    """Exact binary-power product count without materializing the candidate."""
    if type(parameter) is not int:
        raise TypeError("parameter must be an exact integer")
    if family == "mersenne" and parameter >= 3:
        return 2 * parameter - 1
    if family == "fermat" and parameter >= 3:
        return (1 << parameter) + 2
    raise ValueError((family, parameter))


def factor_from_coefficient(modulus: int, coefficient: int) -> int | None:
    """The proper-coefficient-gcd consumer, without a quadratic-root premise.

    This is the branch certified by ``coefficient_gcd_prints_exact_factor``.
    Returning None makes no primality or universal factor-discovery claim.
    """
    if type(modulus) is not int or type(coefficient) is not int:
        raise TypeError("modulus and coefficient must be exact integers")
    from number_compiler.arithmetic.fields.tropical_divisor import TropicalDivisorState

    return TropicalDivisorState.observe(modulus, coefficient).proper_factor

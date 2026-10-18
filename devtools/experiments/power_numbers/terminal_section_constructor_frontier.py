"""Exact frontier for the terminal Frobenius section constructor.

The binary section law itself is already closed.  This module records two
candidate representations for the *source* of that law and proves that neither
silently removes the missing square-root existence problem:

* In the Fermat degree-one cyclotomic representation, extending conductor
  ``2**v`` to ``2**(v+1)`` is exactly adjoining a square root of the current
  primitive root ``zeta``.
* In the Mersenne degree-two real-cyclotomic representation, if
  ``T=zeta+zeta^-1`` then the next trace ``U`` satisfies exactly
  ``U**2=T+2``.  Thus the section is the same quadratic etale split query in
  half-angle coordinates.

The module also audits the tempting high-2-adic AKS/Berrizbeitia tradeoff on a
Fermat number.  The special identity ``2**(2**n) == -1 mod F_n`` can make the
required high-order power congruence tautological only by choosing a very deep
``u``; the corresponding polynomial degree then becomes enormous.  At the
small-degree endpoint ``u=1`` one recovers the ordinary Pepin-length order
check.  This is a representation tradeoff, not a new compact constructor.

Everything here is research-only.  No factor truth, prime label, or recurrence
result is used to manufacture a production branch decision.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.sequences.power_numbers.numbers import (
    fermat_number,
    mersenne_number,
)
from number_compiler.sequences.power_numbers.terminal_threshold import (
    terminal_threshold_spec,
)


@dataclass(frozen=True, slots=True)
class CyclotomicSectionEquivalence:
    family: str
    parameter: int
    decision_conductor_v2: int
    frobenius_degree: int
    current_coordinate: str
    next_coordinate: str
    section_equation: str
    section_is_quadratic_etale_query: bool
    candidate_derived_section_constructor_known: bool
    interpretation: str


def cyclotomic_section_equivalence(
    family: str,
    parameter: int,
) -> CyclotomicSectionEquivalence:
    spec = terminal_threshold_spec(str(family), int(parameter))
    v = spec.prime_decision_required_local_v2
    if spec.family == "fermat":
        return CyclotomicSectionEquivalence(
            "fermat",
            spec.parameter,
            v,
            1,
            "zeta_v (primitive 2^v root in Z/NZ)",
            "zeta_(v+1)",
            "zeta_(v+1)^2 = zeta_v",
            True,
            False,
            (
                "The degree-one orbit polynomial X-zeta does not provide a new "
                "section coordinate: doubling the conductor is exactly square-root "
                "extraction in the candidate base ring."
            ),
        )
    return CyclotomicSectionEquivalence(
        "mersenne",
        spec.parameter,
        v,
        2,
        "T_v = zeta_v + zeta_v^-1",
        "T_(v+1) = zeta_(v+1) + zeta_(v+1)^-1",
        "T_(v+1)^2 = T_v + 2",
        True,
        False,
        (
            "The degree-two real-cyclotomic orbit polynomial X^2-TX+1 does not "
            "avoid the split query: its conductor-doubling section is precisely "
            "the half-angle square-root equation U^2=T+2."
        ),
    )


@dataclass(frozen=True, slots=True)
class FermatHighTwoAdicAKSTradeoff:
    parameter: int
    modulus_bits: int
    k_v2_n_minus_1: int
    s_log2_base_degree: int
    endpoint: str
    u: int
    power_condition_squaring_depth: int
    polynomial_degree_log2: int
    polynomial_degree_bits: int
    compact_section_constructor: bool
    explanation: str


def fermat_high_two_adic_aks_tradeoff(
    parameter: int,
) -> tuple[FermatHighTwoAdicAKSTradeoff, ...]:
    """Return the two exact endpoint costs of the Berrizbeitia-style tradeoff.

    Write ``F_n-1=2^K`` with ``K=2^n``.  In the generalized high-2-adic
    congruence the polynomial exponent has log2-degree ``s+2(u-1)`` where
    ``s=ceil(2 log2 log2 F_n)=2n`` for these exact powers of two.

    * ``u=1`` keeps polynomial degree ``2^(2n)=K^2`` but the required
      nonresidue power condition is exactly the Pepin-depth ``K-1`` squaring
      chain when using the standard fixed base 3.
    * choosing ``a=2`` makes the power condition tautological at
      ``u=K-n`` because ``(F_n-1)/2^u=2^n`` and ``2^(2^n)=-1 mod F_n``.
      But then the polynomial log2-degree is ``2K-2``: essentially quadratic
      in the enormous candidate value, not a compact-parameter quotient.
    """
    n = int(parameter)
    if n < 2:
        raise ValueError(n)
    N = fermat_number(n)
    K = 1 << n
    s = 2 * n

    small_u = 1
    small_log_degree = s
    deep_u = K - n
    if deep_u < 1:
        raise AssertionError((n, K, deep_u))
    deep_log_degree = s + 2 * (deep_u - 1)
    if deep_log_degree != 2 * K - 2:
        raise AssertionError((n, deep_log_degree, 2 * K - 2))

    # At u=1 the standard Fermat/Proth power condition is 3^(2^(K-1))=-1;
    # repeated squaring from the fixed base therefore has K-1 squarings.
    small = FermatHighTwoAdicAKSTradeoff(
        n,
        N.bit_length(),
        K,
        s,
        "small-polynomial",
        small_u,
        K - 1,
        small_log_degree,
        small_log_degree + 1,
        False,
        (
            "Keeping u=1 makes the polynomial degree K^2, but the prerequisite "
            "power congruence is the ordinary Pepin-length order check."
        ),
    )

    # For a=2 and u=K-n, (N-1)/2^u = 2^n and the congruence is the defining
    # identity 2^(2^n)=N-1=-1 mod N, so no modular squaring chain is required.
    deep = FermatHighTwoAdicAKSTradeoff(
        n,
        N.bit_length(),
        K,
        s,
        "tautological-power-condition",
        deep_u,
        0,
        deep_log_degree,
        deep_log_degree + 1,
        False,
        (
            "Using base 2 moves all order work into the polynomial side: the "
            "power condition becomes tautological, but the polynomial degree is "
            "2^(2K-2), far larger than any acceptable compressed section state."
        ),
    )
    return (small, deep)


@dataclass(frozen=True, slots=True)
class SectionConstructorFrontier:
    family: str
    parameter: int
    modulus_bits: int
    semantic_section_law_closed: bool
    orbit_polynomial_section_collapses_to_square_query: bool
    saturated_extension_semantics_closed: bool
    compact_candidate_constructor_known: bool
    production_status: str
    remaining_operation: str


def section_constructor_frontier(
    family: str, parameter: int
) -> SectionConstructorFrontier:
    fam, par = str(family), int(parameter)
    eq = cyclotomic_section_equivalence(fam, par)
    modulus = fermat_number(par) if fam == "fermat" else mersenne_number(par)
    return SectionConstructorFrontier(
        fam,
        par,
        modulus.bit_length(),
        True,
        eq.section_is_quadratic_etale_query,
        True,
        False,
        "UNKNOWN",
        (
            "candidate-derived ZERO/ONE/SPLIT evaluation of the quadratic etale "
            "section equation without factoring, raw Lucas/Pepin replay, or a "
            "supplied local stride bit"
        ),
    )

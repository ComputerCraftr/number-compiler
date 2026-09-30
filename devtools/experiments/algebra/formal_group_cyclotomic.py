"""Formal-group/cyclotomic source-constructor research for Fermat/Mersenne bends.

The v0.52.5 bend/Fitting pass reduced the remaining terminal source theorem to
constructing the compact divisor/kernel state

    D = gcd(N, product_m (1 + C*m))

without evaluating an exponentially large admissible interval.  A natural hope
is to conjugate the additive slot action ``m -> m+1`` to a multiplicative orbit,
because a complete multiplicative orbit has the endpoint product collapse

    product_j (u - v*w^j) = u^L - v^L.

This module tests that hope exactly rather than treating ``exp/log`` notation as
an evaluator.  The main results are:

* on every hidden field F_q, translation has order q while a nontrivial
  multiplicative rotation has order dividing q-1; there is no nontrivial global
  rational semiconjugacy from translation to scaling;
* the denominator-free binomial exponential ``(1+C)^m`` matches the affine atom
  only to first order, and its second-order discrepancy is C^2, a unit modulo N;
* the characteristic-zero formal exponential first loses an invertible
  denominator at k=q, exactly the hidden prime, so its singularity reproduces
  the ghost but only after q coefficients;
* the native characteristic-q additive orbit *does* collapse through
  ``X^q-X`` once q is known.  The hidden factor then gives its bend slot by one
  inverse, but this assumes precisely the unknown valuation axis;
* the obvious Gaussian (Fermat) and Pell (Mersenne) constant-rank norm modules
  have determinant 0 and a unit 1x1 minor for every candidate, prime or
  composite, hence identical rank/Fitting profile.  Symmetric norming also
  erases the bend support on the adversarial composites;
* a Frobenius divisibility-closure forcing query can aggregate slots whose
  hidden bend index divides m, but one query covering all slots <=L needs
  m=lcm(1,...,L).  log(lcm(1,...,L)) is Theta(L), so binary powering reopens
  linear-in-window exponent work rather than producing a polylogarithmic source
  constructor.

Everything here is research-only.  Production must remain fail-closed.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
from math import gcd, lcm

from devtools.experiments.algebra.inputs import required_singularity
from devtools.experiments.power_numbers.special_transverse_jet import (
    SpecialJetProgressionSpec,
    first_special_transverse_singularity,
)
from number_compiler.arithmetic.fields.morphism_core import (
    binary_power_composition_count,
)
from number_compiler.arithmetic.fields.radix import bit_width
from number_compiler.arithmetic.fields.two_adic import v2_positive


def _factor_truth(value: int) -> tuple[int, ...]:
    """Complete bounded factorization for research controls only."""
    n = int(value)
    if n < 2:
        return ()
    out: list[int] = []
    q = 2
    while q * q <= n:
        if n % q:
            q = 3 if q == 2 else q + 2
            continue
        while n % q == 0:
            n //= q
            out.append(q)
        q = 3 if q == 2 else q + 2
    if n > 1:
        out.append(n)
    return tuple(out)


@dataclass(frozen=True, slots=True)
class TranslationRotationAudit:
    family: str
    parameter: int
    modulus: int
    hidden_factor: int
    bend_slot: int
    translation_order: int
    multiplicative_group_order: int
    orders_coprime: bool
    nontrivial_group_conjugacy_possible: bool
    rational_semiconjugacy_to_nontrivial_scaling_possible: bool
    translation_pgl_invariant: int
    sample_scale: int
    sample_scale_pgl_invariant: int
    pgl_invariants_equal: bool
    pgl_gap_equals_square_over_scale: bool


def translation_rotation_audit(family: str, parameter: int) -> TranslationRotationAudit:
    singular = first_special_transverse_singularity(family, parameter)
    if (
        not singular.found
        or singular.first_slot is None
        or singular.denominator_gcd <= 1
    ):
        raise ValueError("bounded composite singular control required")
    q = singular.denominator_gcd
    scale = 2 % q
    inv_scale = pow(scale, -1, q)
    translation_chi = 4 % q
    scale_chi = ((scale + 1) * (scale + 1) * inv_scale) % q
    gap = (scale_chi - translation_chi) % q
    expected_gap = ((scale - 1) * (scale - 1) * inv_scale) % q
    return TranslationRotationAudit(
        singular.family,
        singular.parameter,
        singular.modulus,
        q,
        singular.first_slot,
        q,
        q - 1,
        gcd(q, q - 1) == 1,
        False,
        False,
        translation_chi,
        scale,
        scale_chi,
        translation_chi == scale_chi,
        gap == expected_gap and gap != 0,
    )


@dataclass(frozen=True, slots=True)
class TangentExponentialAudit:
    family: str
    parameter: int
    modulus: int
    stride: int
    affine_0: int
    affine_1: int
    geometric_0: int
    geometric_1: int
    affine_2: int
    geometric_2: int
    second_order_discrepancy: int
    expected_discrepancy: int
    discrepancy_gcd: int
    stride_is_unit: bool
    tangent_matches_two_points_only: bool
    support_preserving_projection: bool


def tangent_exponential_audit(family: str, parameter: int) -> TangentExponentialAudit:
    spec = SpecialJetProgressionSpec.build(family, parameter)
    n, c = spec.modulus, spec.stride
    u = (1 + c) % n
    affine = tuple((1 + c * m) % n for m in range(3))
    geometric = tuple(pow(u, m, n) for m in range(3))
    discrepancy = (geometric[2] - affine[2]) % n
    expected = (c * c) % n
    dg = gcd(discrepancy, n)
    return TangentExponentialAudit(
        spec.family,
        spec.parameter,
        n,
        c,
        affine[0],
        affine[1],
        geometric[0],
        geometric[1],
        affine[2],
        geometric[2],
        discrepancy,
        expected,
        dg,
        gcd(c, n) == 1,
        affine[:2] == geometric[:2] and affine[2] != geometric[2],
        dg != 1,
    )


@dataclass(frozen=True, slots=True)
class FiniteIntervalConjugacyAudit:
    family: str
    parameter: int
    hidden_factor: int
    span: int
    scale: int
    exact_interpolation_degree: int
    top_newton_difference: int
    all_newton_differences_nonzero: bool
    degree_grows_linearly_with_span: bool
    bounded_degree_conjugacy_available: bool


def finite_interval_conjugacy_audit(
    family: str,
    parameter: int,
    *,
    span: int,
    scale: int = 2,
) -> FiniteIntervalConjugacyAudit:
    """Degree audit for h(1+C*m)=scale**m on a bounded hidden field axis.

    In Newton coordinates the r-th forward difference of scale**m at zero is
    (scale-1)^r.  For span<q and nontrivial scale in F_q, every coefficient
    through r=span-1 is nonzero, so the exact interpolation degree is span-1.
    """
    singular = first_special_transverse_singularity(family, parameter)
    if not singular.found or singular.denominator_gcd <= 1:
        raise ValueError("bounded composite singular control required")
    q = singular.denominator_gcd
    span = int(span)
    scale %= q
    if not 1 <= span < q or scale in (0, 1):
        raise ValueError((span, q, scale))
    differences = tuple(pow(scale - 1, r, q) for r in range(span))
    return FiniteIntervalConjugacyAudit(
        singular.family,
        singular.parameter,
        q,
        span,
        scale,
        span - 1,
        differences[-1],
        all(value != 0 for value in differences),
        True,
        False,
    )


@dataclass(frozen=True, slots=True)
class FormalExponentialDenominatorAudit:
    family: str
    parameter: int
    modulus: int
    hidden_factor: int
    bend_slot: int
    bend_atom: int
    first_nonunit_factorial_denominator: int
    legal_coefficients_before_failure: int
    denominator_gcd_at_failure: int
    failure_equals_hidden_factor: bool
    failure_equals_bend_atom: bool
    hidden_q_adic_input_valuation: int
    hidden_q_adic_log_convergent: bool
    two_adic_stride_valuation: int
    odd_modulus_is_two_adic_unit: bool
    two_adic_quotient_by_modulus_is_trivial: bool


def formal_exponential_denominator_audit(
    family: str,
    parameter: int,
) -> FormalExponentialDenominatorAudit:
    spec, singular = required_singularity(family, parameter)
    first_slot = singular.first_slot
    if first_slot is None:
        raise ValueError("required singularity has no first slot")
    q = min(_factor_truth(spec.modulus))
    bend_atom = spec.slot_value(first_slot)
    # exp(T)=sum T^k/k! is defined coefficientwise over Z/NZ exactly until the
    # first prime divisor of N enters k!.  Since q is the least prime factor,
    # every 1,...,q-1 is a unit and q! is the first failed denominator.
    return FormalExponentialDenominatorAudit(
        spec.family,
        spec.parameter,
        spec.modulus,
        q,
        first_slot,
        bend_atom,
        q,
        q - 1,
        gcd(q, spec.modulus),
        q == singular.denominator_gcd,
        q == bend_atom,
        0,  # q does not divide C*m at the bend; C*m == -1 mod q.
        False,
        v2_positive(spec.stride),
        True,
        True,
    )


@dataclass(frozen=True, slots=True)
class KnownAxisAdditiveOrbitAudit:
    family: str
    parameter: int
    modulus: int
    hidden_factor: int
    stride: int
    recovered_slot: int
    expected_slot: int
    additive_orbit_product_mod_q: int
    frobenius_endpoint_mod_q: int
    collapse_exact: bool
    one_inverse_locates_bend: bool
    assumes_hidden_axis: bool


def known_axis_additive_orbit_audit(
    family: str,
    parameter: int,
) -> KnownAxisAdditiveOrbitAudit:
    spec, singular = required_singularity(family, parameter)
    first_slot = singular.first_slot
    if first_slot is None:
        raise ValueError("required singularity has no first slot")
    q = singular.denominator_gcd
    c = spec.stride % q
    inv_c = pow(c, -1, q)
    slot = (-inv_c) % q
    # prod_{m in F_q}(X+m)=X^q-X.  Scale by C^q and X=C^-1.
    endpoint = (1 - pow(c, q - 1, q)) % q
    product = 1
    for m in range(q):
        product = product * (1 + c * m) % q
    return KnownAxisAdditiveOrbitAudit(
        spec.family,
        spec.parameter,
        spec.modulus,
        q,
        spec.stride,
        slot,
        first_slot,
        product,
        endpoint,
        product == endpoint == 0,
        slot == first_slot,
        True,
    )


@dataclass(frozen=True, slots=True)
class EndpointNormAudit:
    family: str
    parameter: int
    modulus: int
    endpoint_x: int
    endpoint_identity_exact: bool
    determinant_mod_n: int
    unit_minor_gcd: int
    kernel_witness: tuple[int, int]
    witness_maps_to_zero: bool
    fitting_zero_is_zero_ideal: bool
    fitting_one_is_unit_ideal: bool
    rank_profile_is_universally_one: bool


def endpoint_norm_audit(family: str, parameter: int) -> EndpointNormAudit:
    spec = SpecialJetProgressionSpec.build(family, parameter)
    n = spec.modulus
    if family == "fermat":
        k = 1 << int(parameter)
        x = 1 << (k // 2)
        identity = x * x + 1 == n
        # Multiplication by X+i on basis (1,i): [[X,-1],[1,X]].
        matrix = ((x % n, (-1) % n), (1, x % n))
        determinant = (x * x + 1) % n
        witness = (1, x % n)
    elif family == "mersenne":
        p = int(parameter)
        x = 1 << ((p - 1) // 2)
        identity = 2 * x * x - 1 == n
        # Multiplication by 1+X*sqrt(2): [[1,2X],[X,1]].
        matrix = ((1, (2 * x) % n), (x % n, 1))
        determinant = (1 - 2 * x * x) % n
        witness = ((-2 * x) % n, 1)
    else:
        raise ValueError(family)
    image = (
        (matrix[0][0] * witness[0] + matrix[0][1] * witness[1]) % n,
        (matrix[1][0] * witness[0] + matrix[1][1] * witness[1]) % n,
    )
    minor_gcd = gcd(n, matrix[0][0], matrix[0][1], matrix[1][0], matrix[1][1])
    return EndpointNormAudit(
        spec.family,
        spec.parameter,
        n,
        x,
        identity,
        determinant,
        minor_gcd,
        witness,
        image == (0, 0),
        determinant == 0,
        minor_gcd == 1,
        determinant == 0 and minor_gcd == 1,
    )


@dataclass(frozen=True, slots=True)
class NormSymmetrizationAudit:
    family: str
    parameter: int
    modulus: int
    hidden_factor: int
    bend_atom: int
    bend_atom_gcd: int
    norm_value_mod_n: int
    norm_value_gcd: int
    hidden_factor_survives_norm: bool


def norm_symmetrization_audit(family: str, parameter: int) -> NormSymmetrizationAudit:
    spec, singular = required_singularity(family, parameter)
    first_slot = singular.first_slot
    if first_slot is None:
        raise ValueError("required singularity has no first slot")
    y = spec.slot_value(first_slot)
    if family == "fermat":
        norm = (y * y + 1) % spec.modulus
    elif family == "mersenne":
        norm = (y * y - 2) % spec.modulus
    else:
        raise ValueError(family)
    ng = gcd(norm, spec.modulus)
    return NormSymmetrizationAudit(
        spec.family,
        spec.parameter,
        spec.modulus,
        singular.denominator_gcd,
        y,
        gcd(y, spec.modulus),
        norm,
        ng,
        norm % singular.denominator_gcd == 0,
    )


@dataclass(frozen=True, slots=True)
class DivisibilityClosureFactorRow:
    factor: int
    bend_slot: int
    query_slot: int
    exponent: int
    fixed_field_points: int
    whole_field_fixed: bool
    slot_divides_query: bool


@dataclass(frozen=True, slots=True)
class DivisibilityClosureAudit:
    family: str
    parameter: int
    modulus: int
    stride: int
    query_slot: int
    rows: tuple[DivisibilityClosureFactorRow, ...]
    closure_theorem_exact: bool
    factor_truth_only: bool


def divisibility_closure_audit(
    family: str,
    parameter: int,
    query_slot: int,
) -> DivisibilityClosureAudit:
    spec = SpecialJetProgressionSpec.build(family, parameter)
    m = int(query_slot)
    if m < 1:
        raise ValueError(m)
    exponent = 1 + spec.stride * m
    rows: list[DivisibilityClosureFactorRow] = []
    for q in sorted(set(_factor_truth(spec.modulus))):
        if (q - 1) % spec.stride:
            raise AssertionError((family, parameter, q, spec.stride))
        slot = (q - 1) // spec.stride
        fixed = 1 + gcd(exponent - 1, q - 1)
        whole = fixed == q
        divides = m % slot == 0
        rows.append(
            DivisibilityClosureFactorRow(
                q,
                slot,
                m,
                exponent,
                fixed,
                whole,
                divides,
            )
        )
    return DivisibilityClosureAudit(
        spec.family,
        spec.parameter,
        spec.modulus,
        spec.stride,
        m,
        tuple(rows),
        all(row.whole_field_fixed == row.slot_divides_query for row in rows),
        True,
    )


@dataclass(frozen=True, slots=True)
class LcmClosureAudit:
    family: str
    parameter: int
    span: int
    universal_query_slot: int
    query_slot_bits: int
    exponent_bits: int
    binary_power_multiplications: int
    all_slots_divide_query: bool
    query_descriptor_is_linear_scale_in_span: bool
    polylogarithmic_in_span: bool


def lcm_closure_audit(family: str, parameter: int, span: int) -> LcmClosureAudit:
    spec = SpecialJetProgressionSpec.build(family, parameter)
    span = int(span)
    if span < 1 or span > spec.max_slot:
        raise ValueError((span, spec.max_slot))
    query = 1
    for m in range(1, span + 1):
        query = lcm(query, m)
    exponent = 1 + spec.stride * query
    # log lcm(1,...,L)=psi(L)=Theta(L); the exact bounded bit count is recorded
    # here and the frontier rejects this as a polylogarithmic descriptor.
    return LcmClosureAudit(
        spec.family,
        spec.parameter,
        span,
        query,
        bit_width(query),
        bit_width(exponent),
        binary_power_composition_count(exponent),
        all(query % m == 0 for m in range(1, span + 1)),
        True,
        False,
    )


@dataclass(frozen=True, slots=True)
class ScalarLcmForcingAudit:
    family: str
    parameter: int
    modulus: int
    span: int
    base: int
    universal_query_slot: int
    exponent: int
    exponent_bits: int
    binary_power_multiplications: int
    forcing_gcd: int
    factor_truth: tuple[int, ...]
    candidate_is_prime_by_truth: bool
    criterion_classifies_control: bool
    criterion_is_general_for_family: bool
    polylogarithmic_in_span: bool
    comparison_reference_steps: int


def scalar_lcm_forcing_audit(
    family: str,
    parameter: int,
    *,
    base: int = 3,
) -> ScalarLcmForcingAudit:
    """Audit one lcm-exponent divisibility-closure forcing query.

    For Fermat, this is a genuine deterministic criterion on the special family:
    every composite F_n has a q<=sqrt(F_n) with q-1=C*s and s<=L, hence
    q-1 divides C*lcm(1..L).  If F_n is prime, Pepin's order theorem gives
    ord_{F_n}(3)=F_n-1, while the lcm exponent has insufficient 2-adic
    order, so the gcd is one.  The criterion is therefore semantically exact
    but its exponent description has Theta(L) bits.

    On Mersenne controls the same scalar construction is not a primality
    criterion: a prime candidate can have N-1 smooth enough that the lcm
    exponent fixes the chosen base as well.
    """
    spec = SpecialJetProgressionSpec.build(family, parameter)
    span = spec.max_slot
    if span < 1:
        raise ValueError("positive factor window required")
    query = 1
    for m in range(1, span + 1):
        query = lcm(query, m)
    exponent = 1 + spec.stride * query
    residue = (pow(int(base), exponent, spec.modulus) - int(base)) % spec.modulus
    g = gcd(spec.modulus, residue)
    factors = _factor_truth(spec.modulus)
    prime = len(factors) == 1 and factors[0] == spec.modulus
    if family == "fermat":
        classified = (g == 1) == prime
        general = True
        reference = (1 << int(parameter)) - 1  # Pepin repeated-squaring count.
    elif family == "mersenne":
        classified = (g == 1) == prime
        general = False
        reference = int(parameter) - 2  # Lucas--Lehmer recurrence steps.
    else:
        raise ValueError(family)
    return ScalarLcmForcingAudit(
        spec.family,
        spec.parameter,
        spec.modulus,
        span,
        int(base),
        query,
        exponent,
        bit_width(exponent),
        binary_power_composition_count(exponent),
        g,
        factors,
        prime,
        classified,
        general,
        False,
        reference,
    )


@dataclass(frozen=True, slots=True)
class FormalGroupCyclotomicFrontier:
    additive_to_multiplicative_global_conjugacy_possible: bool
    rational_semiconjugacy_possible: bool
    denominator_free_tangent_support_preserving: bool
    finite_interval_bounded_degree_conjugacy_available: bool
    formal_exponential_reproduces_hidden_factor: bool
    formal_exponential_polylogarithmic_source_constructor: bool
    known_axis_additive_frobenius_collapse_exact: bool
    known_axis_assumes_hidden_factor: bool
    endpoint_quadratic_norm_distinguishes_prime_from_composite: bool
    norm_symmetrization_preserves_bend_support: bool
    divisibility_closure_forcing_exact: bool
    lcm_closure_polylogarithmic: bool
    fermat_scalar_lcm_forcing_semantically_exact: bool
    fermat_scalar_lcm_forcing_polylogarithmic: bool
    mersenne_scalar_lcm_forcing_general: bool
    production_source_extractor_available: bool
    status: str
    missing_operation: str


def formal_group_cyclotomic_frontier() -> FormalGroupCyclotomicFrontier:
    return FormalGroupCyclotomicFrontier(
        additive_to_multiplicative_global_conjugacy_possible=False,
        rational_semiconjugacy_possible=False,
        denominator_free_tangent_support_preserving=False,
        finite_interval_bounded_degree_conjugacy_available=False,
        formal_exponential_reproduces_hidden_factor=True,
        formal_exponential_polylogarithmic_source_constructor=False,
        known_axis_additive_frobenius_collapse_exact=True,
        known_axis_assumes_hidden_factor=True,
        endpoint_quadratic_norm_distinguishes_prime_from_composite=False,
        norm_symmetrization_preserves_bend_support=False,
        divisibility_closure_forcing_exact=True,
        lcm_closure_polylogarithmic=False,
        fermat_scalar_lcm_forcing_semantically_exact=True,
        fermat_scalar_lcm_forcing_polylogarithmic=False,
        mersenne_scalar_lcm_forcing_general=False,
        production_source_extractor_available=False,
        status="UNKNOWN",
        missing_operation=(
            "an axis-free polylogarithmic constructor for the compact bend/kernel "
            "support.  Multiplicative cyclotomic conjugacy is impossible on each "
            "hidden F_q axis; formal exp/log expose q only when their denominator "
            "horizon reaches q; the native additive Frobenius collapse is compact "
            "only after q is supplied, while universal divisibility-closure queries "
            "require an lcm exponent with Theta(span) description bits"
        ),
    )


def formal_group_cyclotomic_metrics() -> dict[str, object]:
    composites = (("fermat", 5), ("mersenne", 11), ("mersenne", 29))
    prime_and_composite = (
        ("fermat", 4),
        ("fermat", 5),
        ("mersenne", 11),
        ("mersenne", 13),
        ("mersenne", 29),
    )
    return {
        "translation_rotation": [
            asdict(translation_rotation_audit(*key)) for key in composites
        ],
        "tangent_exponential": [
            asdict(tangent_exponential_audit(*key)) for key in prime_and_composite
        ],
        "finite_interval_conjugacy": [
            asdict(finite_interval_conjugacy_audit("fermat", 5, span=511)),
            asdict(finite_interval_conjugacy_audit("mersenne", 11, span=2)),
            asdict(finite_interval_conjugacy_audit("mersenne", 29, span=200)),
        ],
        "formal_exponential_denominators": [
            asdict(formal_exponential_denominator_audit(*key)) for key in composites
        ],
        "known_axis_additive_orbit": [
            asdict(known_axis_additive_orbit_audit(*key)) for key in composites
        ],
        "endpoint_norm": [
            asdict(endpoint_norm_audit(*key)) for key in prime_and_composite
        ],
        "norm_symmetrization": [
            asdict(norm_symmetrization_audit(*key)) for key in composites
        ],
        "divisibility_closure": [
            asdict(divisibility_closure_audit("fermat", 5, m)) for m in (5, 10, 52347)
        ]
        + [asdict(divisibility_closure_audit("mersenne", 29, m)) for m in (4, 19, 36)],
        "scalar_lcm_forcing": [
            asdict(scalar_lcm_forcing_audit("fermat", 4)),
            asdict(scalar_lcm_forcing_audit("fermat", 5)),
            asdict(scalar_lcm_forcing_audit("mersenne", 11)),
            asdict(scalar_lcm_forcing_audit("mersenne", 13)),
            asdict(scalar_lcm_forcing_audit("mersenne", 29)),
            asdict(scalar_lcm_forcing_audit("mersenne", 31)),
        ],
        "lcm_closure": [
            asdict(lcm_closure_audit("fermat", 5, span)) for span in (16, 64, 256, 511)
        ]
        + [
            asdict(lcm_closure_audit("mersenne", 29, span))
            for span in (16, 64, 256, 399)
        ],
        "frontier": asdict(formal_group_cyclotomic_frontier()),
    }


__all__ = [
    "DivisibilityClosureAudit",
    "DivisibilityClosureFactorRow",
    "EndpointNormAudit",
    "FiniteIntervalConjugacyAudit",
    "FormalExponentialDenominatorAudit",
    "FormalGroupCyclotomicFrontier",
    "KnownAxisAdditiveOrbitAudit",
    "LcmClosureAudit",
    "NormSymmetrizationAudit",
    "ScalarLcmForcingAudit",
    "TangentExponentialAudit",
    "TranslationRotationAudit",
    "divisibility_closure_audit",
    "endpoint_norm_audit",
    "finite_interval_conjugacy_audit",
    "formal_exponential_denominator_audit",
    "formal_group_cyclotomic_frontier",
    "formal_group_cyclotomic_metrics",
    "known_axis_additive_orbit_audit",
    "lcm_closure_audit",
    "norm_symmetrization_audit",
    "scalar_lcm_forcing_audit",
    "tangent_exponential_audit",
    "translation_rotation_audit",
]

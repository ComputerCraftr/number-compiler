"""Terminal divisor-norm reduction for the special-number certificate.

This module deliberately separates two statements:

1.  A *mathematical* reduction: the terminal Fermat/Mersenne all-local
    predicate is equivalent to a relative ideal-norm condition.  The local
    obstruction is valuation divisibility by the residue degree.  For the
    special candidates, a size bound proves that a proper prime-power factor
    always has exponent strictly smaller than that residue degree, so repeated
    factors cannot fake the terminal PASS.
2.  The *algorithmic* problem: compute that support-wise norm obstruction from
    the unfactored sparse principal ideal.  This remains unavailable.  Scalar
    Artin/power-residue products can cancel, and fixed linear Galois-module
    Fitting invariants are blind by the normal-basis/regular-module theorem.

Factorization is used below only by functions whose names contain ``truth`` or
``audit``.  Nothing in this module is imported by production.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import comb

from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.sequences.power_numbers.numbers import (
    fermat_number,
    mersenne_number,
)
from number_compiler.sequences.power_numbers.terminal_threshold import (
    terminal_threshold_spec,
)
from number_compiler.sequences.prime.set import smallest_factor


def _factor_multiplicities_truth(value: int) -> tuple[tuple[int, int], ...]:
    """Complete bounded factorization for research labels only."""
    remaining = int(value)
    if remaining < 2:
        return ()
    out: list[tuple[int, int]] = []
    while remaining > 1:
        f = smallest_factor(remaining)
        q = remaining if f is None else f
        e = 0
        while remaining % q == 0:
            remaining //= q
            e += 1
        out.append((q, e))
    return tuple(out)


def _mul_pow2_exceeds(multiplier: int, exponent_log2: int, bound: int) -> bool:
    """Return multiplier*2^exponent_log2 > bound without huge shifts."""
    multiplier = int(multiplier)
    exponent_log2 = int(exponent_log2)
    bound = int(bound)
    if multiplier <= 0 or exponent_log2 < 0 or bound < 0:
        raise ValueError((multiplier, exponent_log2, bound))
    # If 2^r alone already exceeds bound, avoid materializing it.
    if exponent_log2 >= max(1, bound.bit_length()):
        return True
    return (multiplier << exponent_log2) > bound


@dataclass(frozen=True, slots=True)
class LocalDivisorNormRow:
    family: str
    parameter: int
    prime: int
    multiplicity: int
    local_capacity_v2: int
    residue_degree_log2: int
    residue_degree: int | None
    local_norm_allowed: bool
    proper_factor: bool
    multiplicity_strictly_below_residue_degree: bool
    size_bound_proves_strictness: bool


@dataclass(frozen=True, slots=True)
class TerminalDivisorNormAudit:
    family: str
    parameter: int
    candidate_modulus: int
    terminal_level: int
    relative_degree_log2: int
    local_rows: tuple[LocalDivisorNormRow, ...]
    divisor_norm_exists: bool
    candidate_is_prime_by_truth: bool
    divisor_norm_iff_prime: bool
    scalar_character_sufficient: bool
    factor_truth_only: bool = True


@dataclass(frozen=True, slots=True)
class RegularArtinEulerCoefficientAudit:
    """Support-preserving coefficient of the relative regular Artin Euler product.

    If P has residue degree f and there are g=d/f primes above it, then the
    local regular Artin/Dedekind-zeta factor is

        (1 - T^f)^(-g).

    Hence the coefficient at P^e is zero unless f|e; if f|e it is
    C(e/f+g-1,g-1).  The global coefficient is nonzero exactly when the input
    ideal is an ideal norm.  We retain only bounded exact coefficients; for
    large d the nonzero/zero theorem is enough and avoids giant integers.
    """

    family: str
    parameter: int
    relative_degree_log2: int
    local_nonzero: tuple[bool, ...]
    coefficient_nonzero: bool
    bounded_exact_coefficient: int | None
    ideal_norm_equivalent: bool
    factor_truth_only: bool = True


@dataclass(frozen=True, slots=True)
class FermatFullPowerResiduePhaseAudit:
    """Audit the full 2^(n+1)-th power-residue phase of base 3.

    This is stronger than the rational +/-1 symbol.  Each local symbol is
    expressed in the canonical zeta coordinate selected by
    ``1-2*zeta_(2^(n+1))``.  F5 is the key adversary: its two local phases add
    to exactly the same aggregate phase as prime F4-style reciprocity predicts,
    demonstrating that even a full root-of-unity Artin product is not the
    support selector.
    """

    parameter: int
    symbol_order: int
    local_exponents: tuple[int, ...]
    aggregate_exponent: int
    prime_formula_exponent: int
    aggregate_matches_prime_formula: bool
    candidate_is_prime_by_truth: bool
    factor_truth_only: bool = True


@dataclass(frozen=True, slots=True)
class QuadraticSubresultantBlindAudit:
    family: str
    parameter: int
    radicand: int
    modulus: int
    discriminant_gcd: int
    derivative_resultant_gcd: int
    all_linear_subresultant_data_units: bool
    splitting_truth: bool
    factor_truth_only: bool = True


@dataclass(frozen=True, slots=True)
class RawPowerLowerBoundAudit:
    family: str
    parameter: int
    squaring_depth: int
    minimum_generic_multiplications: int
    binary_composition_cannot_reduce_raw_evaluation: bool
    proof: str


@dataclass(frozen=True, slots=True)
class SupportEulerCoefficientTarget:
    family: str
    parameter: int
    terminal_level: int
    semantic_object: str
    aggregate_artin_rejected: bool
    fixed_linear_fitting_rejected: bool
    factor_free_evaluator_available: bool
    status: str


@dataclass(frozen=True, slots=True)
class AggregateArtinBlindAudit:
    family: str
    parameter: int
    conductor_log2: int
    candidate_residue: int
    identity_representative: int
    aggregate_artin_is_identity: bool
    all_scalar_characters_blind: bool
    proof: str


@dataclass(frozen=True, slots=True)
class LinearGaloisFittingBlindAudit:
    """Fixed linear G-action cannot see residue degree.

    For an unramified Galois extension, every residue algebra is a G-Galois
    algebra and, by the normal-basis theorem, its underlying F_q[G]-module is
    the regular module independent of decomposition type.  Therefore the
    characteristic polynomial/ranks/Fitting ideals of any *fixed G-linear*
    combination are identical in split and nonsplit controls.  Frobenius (and
    thus support) is semilinear and is exactly the missing datum.
    """

    group_order_log2: int
    tested_operator: str
    split_characteristic_polynomial: tuple[int, ...]
    nonsplit_characteristic_polynomial: tuple[int, ...]
    same_linear_signature: bool
    conclusion: str


def _fermat_local_row(n: int, q: int, e: int, modulus: int) -> LocalDivisorNormRow:
    T = 1 << n
    t = v2_positive(q - 1)
    r = max(0, T - t)
    f = (1 << r) if r <= 62 else None
    local_norm = r == 0 or (f is not None and e % f == 0)
    proper = q < modulus

    if r == 0:
        strict = False
        size_bound = not proper
    else:
        # q = 1 mod 2^t gives q > 2^t.  If q^f divided F_n and
        # t*f > T, then q^f > 2^T+1=F_n, so every actual exponent e is < f.
        size_bound = _mul_pow2_exceeds(t, r, T)
        strict = bool(proper and size_bound and (f is None or e < f))
        if proper and not size_bound:
            raise AssertionError((n, q, e, t, r, "Fermat multiplicity bound"))
        if proper and f is not None and not e < f:
            raise AssertionError((n, q, e, f))
        if proper:
            local_norm = False

    return LocalDivisorNormRow(
        "fermat",
        n,
        q,
        e,
        t,
        r,
        f,
        local_norm,
        proper,
        strict,
        size_bound,
    )


def _mersenne_real_cyclotomic_local_row(
    p: int,
    q: int,
    e: int,
    modulus: int,
) -> LocalDivisorNormRow:
    # In Q(zeta_(2^p))^+, Frobenius is the class of q modulo +/-1.  Put
    # u=max(v2(q-1),v2(q+1)); its order in (Z/2^p Z)^*/{+/-1} is
    # 2^(p-u) for u<p, and 1 for u>=p.
    u = max(v2_positive(q - 1), v2_positive(q + 1))
    r = max(0, p - u)
    f = (1 << r) if r <= 62 else None
    local_norm = r == 0 or (f is not None and e % f == 0)
    proper = q < modulus

    if r == 0:
        strict = False
        size_bound = not proper
    else:
        # q == +/-1 mod 2^u gives q > 2^(u-1).  Thus q^f > 2^p > M_p
        # once (u-1)*f > p.  This holds for p>=5 and every proper divisor.
        if p == 3:
            size_bound = True
        else:
            size_bound = _mul_pow2_exceeds(max(1, u - 1), r, p)
        strict = bool(proper and size_bound and (f is None or e < f))
        if proper and not size_bound:
            raise AssertionError((p, q, e, u, r, "Mersenne multiplicity bound"))
        if proper and f is not None and not e < f:
            raise AssertionError((p, q, e, f))
        if proper:
            local_norm = False

    # ``local_capacity_v2`` here is the +/-1 cyclotomic splitting capacity u;
    # it is terminal-equivalent to the LL torus condition but avoids the
    # unnecessary sqrt(3) twist at the final level.
    return LocalDivisorNormRow(
        "mersenne",
        p,
        q,
        e,
        u,
        r,
        f,
        local_norm,
        proper,
        strict,
        size_bound,
    )


def terminal_divisor_norm_truth_audit(
    family: str, parameter: int
) -> TerminalDivisorNormAudit:
    family = str(family)
    parameter = int(parameter)
    spec = terminal_threshold_spec(family, parameter)
    if family == "fermat":
        modulus = fermat_number(parameter)
        factors = _factor_multiplicities_truth(modulus)
        rows = tuple(_fermat_local_row(parameter, q, e, modulus) for q, e in factors)
        degree_log2 = spec.terminal_level
    elif family == "mersenne":
        modulus = mersenne_number(parameter)
        factors = _factor_multiplicities_truth(modulus)
        rows = tuple(
            _mersenne_real_cyclotomic_local_row(parameter, q, e, modulus)
            for q, e in factors
        )
        degree_log2 = parameter - 2
    else:
        raise ValueError(family)

    norm_exists = all(row.local_norm_allowed for row in rows)
    prime_truth = (
        len(rows) == 1 and rows[0].prime == modulus and rows[0].multiplicity == 1
    )
    # Scalar character products are known insufficient; this field is an
    # explicit semantic statement, not an experimental guess.
    return TerminalDivisorNormAudit(
        family,
        parameter,
        modulus,
        spec.terminal_level,
        degree_log2,
        rows,
        norm_exists,
        prime_truth,
        norm_exists == prime_truth,
        False,
    )


def regular_artin_euler_coefficient_truth_audit(
    family: str,
    parameter: int,
) -> RegularArtinEulerCoefficientAudit:
    audit = terminal_divisor_norm_truth_audit(family, parameter)
    d_log = audit.relative_degree_log2
    local_nonzero: list[bool] = []
    exact = 1
    exact_available = d_log <= 14
    d = 1 << d_log if exact_available else None

    for row in audit.local_rows:
        r = row.residue_degree_log2
        if r == 0:
            f = 1
        elif r <= 62:
            f = 1 << r
        else:
            f = None
        nz = r == 0 or (f is not None and row.multiplicity % f == 0)
        local_nonzero.append(nz)
        if exact_available and nz:
            assert d is not None and f is not None
            g = d // f
            m = row.multiplicity // f
            exact *= comb(m + g - 1, g - 1)
        elif not nz:
            exact = 0

    nonzero = all(local_nonzero)
    return RegularArtinEulerCoefficientAudit(
        family,
        parameter,
        d_log,
        tuple(local_nonzero),
        nonzero,
        exact if exact_available else None,
        nonzero == audit.divisor_norm_exists,
    )


def _dlog_small_subgroup(base: int, value: int, modulus: int, order: int) -> int:
    x = 1
    for exponent in range(order):
        if x == value:
            return exponent
        x = x * base % modulus
    raise AssertionError((base, value, modulus, order))


def fermat_full_power_residue_phase_truth_audit(
    index: int,
) -> FermatFullPowerResiduePhaseAudit:
    n = int(index)
    if n < 2:
        raise ValueError(n)
    modulus = fermat_number(n)
    factors = _factor_multiplicities_truth(modulus)
    m = 1 << (n + 1)
    local: list[int] = []
    for q, e in factors:
        if (q - 1) % m:
            raise AssertionError((n, q, m))
        # zeta is the image selected by 1-2*zeta: zeta = 2^-1 mod q.
        zeta = pow(2, -1, q)
        phase = pow(3, (q - 1) // m, q)
        exponent = _dlog_small_subgroup(zeta, phase, q, m)
        local.extend([exponent] * e)
    aggregate = sum(local) % m
    expected = ((1 << n) - 3) % m
    prime_truth = len(factors) == 1 and factors[0] == (modulus, 1)
    return FermatFullPowerResiduePhaseAudit(
        n,
        m,
        tuple(local),
        aggregate,
        expected,
        aggregate == expected,
        prime_truth,
    )


def aggregate_artin_blind_audit(
    family: str, parameter: int
) -> AggregateArtinBlindAudit:
    """Prove that the product Artin element is forced to the identity.

    Fermat: in the terminal cyclotomic extension the local Frobenius classes
    multiply to the rational norm F_n, and F_n == 1 mod 2^(2^n).

    Mersenne: use the real 2^p-cyclotomic field.  Frobenius lives in
    (Z/2^p Z)^*/{+/-1}; M_p == -1 mod 2^p, which is the identity class.

    Hence every one-dimensional Artin/Hecke character of the *aggregate*
    divisor is predetermined by the special form.  Reciprocity can simplify
    such a character but cannot recover the non-cancelling support statistic.
    """
    family = str(family)
    parameter = int(parameter)
    if family == "fermat":
        T = 1 << parameter
        modulus = fermat_number(parameter)
        conductor = 1 << T
        residue = modulus % conductor
        identity = 1
        ok = residue == identity
        proof = "F_n=2^(2^n)+1 is 1 modulo the terminal 2-power conductor"
        conductor_log2 = T
    elif family == "mersenne":
        p = parameter
        modulus = mersenne_number(p)
        conductor = 1 << p
        residue = modulus % conductor
        # In the real cyclotomic quotient, +/-1 are the same identity class.
        identity = conductor - 1
        ok = residue in (1, conductor - 1)
        proof = (
            "M_p=2^p-1 is -1 modulo 2^p, identity in the real-cyclotomic +/-1 quotient"
        )
        conductor_log2 = p
    else:
        raise ValueError(family)
    return AggregateArtinBlindAudit(
        family,
        parameter,
        conductor_log2,
        residue,
        identity,
        ok,
        ok,
        proof,
    )


def linear_galois_fitting_blind_audit(
    group_order_log2: int = 4,
) -> LinearGaloisFittingBlindAudit:
    r = int(group_order_log2)
    if r < 1 or r > 10:
        raise ValueError(r)
    d = 1 << r
    # Characteristic polynomial of the regular cyclic shift is X^d-1.  We
    # store coefficients low-to-high.  Normal basis says the same regular
    # module occurs for every unramified decomposition type.
    poly = [-1] + [0] * (d - 1) + [1]
    signature = tuple(poly)
    return LinearGaloisFittingBlindAudit(
        r,
        "regular-generator",
        signature,
        signature,
        True,
        "fixed G-linear Fitting/rank data is regular-module data; local Frobenius is missing",
    )


def repeated_factor_multiplicity_guard(
    family: str,
    parameter: int,
    local_capacity_v2: int,
    multiplicity: int,
) -> bool:
    """Pure arithmetic guard used by tests for repeated-factor adversaries.

    Returns True exactly when the special-form size theorem proves
    ``multiplicity < residue_degree`` for a hypothetical proper local factor.
    No factor identity is needed.
    """
    family = str(family)
    parameter = int(parameter)
    t = int(local_capacity_v2)
    e = int(multiplicity)
    if e < 1:
        raise ValueError(e)
    if family == "fermat":
        T = 1 << parameter
        r = T - t
        if r < 1:
            return False
        if not _mul_pow2_exceeds(t, r, T):
            return False
    elif family == "mersenne":
        p = parameter
        r = p - t
        if r < 1:
            return False
        if not _mul_pow2_exceeds(max(1, t - 1), r, p):
            return False
    else:
        raise ValueError(family)
    if r >= e.bit_length() + 1:
        return True
    return e < (1 << r)


def quadratic_subresultant_blind_audit(index: int) -> QuadraticSubresultantBlindAudit:
    """Audit the first undecided Fermat Kummer layer.

    The layer polynomial is ``X^2-r1`` over ``Z/F_n Z``.  Its derivative
    resultant/discriminant is a unit whenever ``r1`` is a unit, regardless of
    whether the polynomial splits.  Thus the ordinary subresultant/Fitting
    sequence can detect ramification/nonunits but not split versus inert.

    ``splitting_truth`` is factor-backed and is retained only as the adversarial
    label; the unit calculations themselves are candidate-ring calculations.
    """
    n = int(index)
    if n < 2:
        raise ValueError(n)
    N = fermat_number(n)
    t = 1 << (1 << (n - 2))
    r1 = (t + pow(t, -1, N)) % N
    disc = (4 * r1) % N
    disc_gcd = __import__("math").gcd(disc, N)
    # Res(X^2-r1, 2X) = -4*r1, so its nonunit content is identical.
    res_gcd = __import__("math").gcd((-4 * r1) % N, N)
    factors = _factor_multiplicities_truth(N)
    split = all(pow(r1 % q, (q - 1) // 2, q) == 1 for q, _e in factors)
    return QuadraticSubresultantBlindAudit(
        "fermat",
        n,
        r1,
        N,
        disc_gcd,
        res_gcd,
        disc_gcd == res_gcd == 1,
        split,
    )


def raw_power_lower_bound_audit(family: str, parameter: int) -> RawPowerLowerBoundAudit:
    """Formal anti-fake-green lower bound for raw ``2^k`` powering.

    Starting from exponent one, one multiplication can at most double the
    largest exponent represented by an addition chain.  Therefore producing
    ``x^(2^k)`` in a generic multiplication algebra needs at least ``k``
    multiplications, with repeated squaring attaining the bound.  Binary
    composition may compress the *description* of the map, but applying that
    map to an unconstrained candidate-ring element cannot use fewer raw
    multiplications without an additional quotient theorem.
    """
    family = str(family)
    parameter = int(parameter)
    spec = terminal_threshold_spec(family, parameter)
    k = spec.terminal_level
    return RawPowerLowerBoundAudit(
        family,
        parameter,
        k,
        k,
        True,
        "addition-chain maximum exponent doubles at most once per multiplication",
    )


def support_euler_coefficient_target(
    family: str, parameter: int
) -> SupportEulerCoefficientTarget:
    """Describe the surviving non-cancelling terminal selector target.

    This is intentionally not an evaluator.  The semantic object is the
    coefficient of the sparse principal ideal in the relative regular-Artin /
    Dedekind-zeta Euler product, equivalently relative ideal-norm membership.
    A factor-free algorithm for that coefficient remains unavailable.
    """
    spec = terminal_threshold_spec(family, parameter)
    return SupportEulerCoefficientTarget(
        spec.family,
        spec.parameter,
        spec.terminal_level,
        "relative-regular-Artin-Euler-coefficient / divisor-norm membership",
        True,
        True,
        False,
        "UNKNOWN",
    )


__all__ = [
    "AggregateArtinBlindAudit",
    "FermatFullPowerResiduePhaseAudit",
    "LinearGaloisFittingBlindAudit",
    "LocalDivisorNormRow",
    "QuadraticSubresultantBlindAudit",
    "RawPowerLowerBoundAudit",
    "RegularArtinEulerCoefficientAudit",
    "SupportEulerCoefficientTarget",
    "TerminalDivisorNormAudit",
    "aggregate_artin_blind_audit",
    "fermat_full_power_residue_phase_truth_audit",
    "linear_galois_fitting_blind_audit",
    "quadratic_subresultant_blind_audit",
    "raw_power_lower_bound_audit",
    "regular_artin_euler_coefficient_truth_audit",
    "repeated_factor_multiplicity_guard",
    "support_euler_coefficient_target",
    "terminal_divisor_norm_truth_audit",
]

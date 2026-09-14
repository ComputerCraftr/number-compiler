"""Partial Frobenius/cyclotomic quotients for the terminal etale split bit.

This follow-up deliberately targets the *one* missing quadratic split bit.  It
contains two exact quotients:

1.  A quadratic additive probe ``u=a+b*y`` is projected to the base ring by its
    Cayley ratio ``z=u/conj(u)``.  The trace ``x=z+z^-1`` evolves under squaring
    by the Lucas map ``x -> x^2-2``.  The discriminant ``x^2-4`` has exactly the
    same square class as the original radicand ``d``.  The coefficient of ``z``
    in ``z^e`` is the second-kind Dickson/Lucas coefficient and retains the
    local Frobenius orientation ``+1/-1``.

2.  For a Fermat divisor ``q`` whose previous dyadic layer is known, write
    ``q=1+m*k`` with ``m`` a power of two and work in ``Phi_(2m)=X^m+1``.
    Characteristic-q Frobenius and the exact power-of-two cyclotomic identity

        (1+X)^m = A_m(X)

    give

        A_m(X)^k (1+X) = 1 + (-1)^k X.                 (*)

    Thus the *one coefficient sign on the right of (*)* is exactly the next
    Kummer/etale split bit.  This is the partial cyclotomic Frobenius equation
    that the prime-field theorem was using implicitly; no full Frobenius matrix
    or support histogram is needed.

The module also records, fail-honestly, why the candidate-global exponent does
not yet provide that local sign on composites: if ``N=q*c`` then the cofactor
has the same dyadic sign and the on-circle actions compose to the identity.
The remaining production theorem is therefore a quotient of this cofactor
coupling, not recovery of a full local Frobenius/support vector.

All factor-backed rows in this module are audit-only and are never imported by
production.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import comb, gcd

from devtools.experiments.algebra.dyadic_difference_germ_core import (
    ambient_capacity_truth,
)
from number_compiler.sequences.power_numbers.numbers import (
    fermat_number,
    mersenne_composite_exponent_factor,
    mersenne_number,
)


@dataclass(frozen=True, slots=True)
class QuadraticCayleyTraceQuotient:
    modulus: int
    radicand: int
    a: int
    b: int
    norm: int
    norm_gcd: int
    trace: int | None
    discriminant: int | None
    square_multiplier: int | None
    discriminant_matches_radicand_square_class: bool
    split_witness_gcd: int | None
    candidate_derived: bool = True


@dataclass(frozen=True, slots=True)
class CayleySquareCommutationAudit:
    modulus: int
    radicand: int
    initial_pair: tuple[int, int]
    squared_pair: tuple[int, int]
    initial_trace: int
    trace_after_pair_square: int
    lucas_trace_step: int
    exact: bool


@dataclass(frozen=True, slots=True)
class DicksonOrientationState:
    """Base-ring trace/orientation of ``z^exponent``.

    ``orientation`` is B_e(x)=(z^e-z^-e)/(z-z^-1), with B_1=1.  Hence

        z^e = B_e(x) z - B_(e-1)(x).

    For a local q-Frobenius on a quadratic etale fibre this is +1 on the split
    fibre and -1 on the nonsplit fibre.
    """

    modulus: int
    exponent: int
    trace: int
    orientation: int
    compositions: int


@dataclass(frozen=True, slots=True)
class MersenneCayleyLucasQuotientAudit:
    exponent: int
    modulus: int
    additive_probe: tuple[int, int]
    additive_norm: int
    cayley_unit: tuple[int, int]
    cayley_norm: int
    trace: int
    exact_cayley_identity: bool
    lucas_lehmer_seed: int
    extension_state_required: bool = False


@dataclass(frozen=True, slots=True)
class FermatReixLucasQuotientAudit:
    parameter: int
    modulus: int
    quadratic_radicand: int
    norm_one_unit_twice: tuple[int, int]
    trace_seed: int
    horizon: int
    terminal_trace: int
    terminal_zero: bool
    ring_squarings: int
    theorem_total: bool = True
    factor_enumeration: int = 0
    scalable_powering: bool = False


@dataclass(frozen=True, slots=True)
class SpecialLucasTerminalQuotient:
    family: str
    parameter: int
    modulus: int
    trace_seed: int
    horizon: int
    terminal_trace: int
    terminal_zero: bool
    classification: str
    theorem: str
    quotient_cells: int
    retained_extension_coordinates: int
    ring_squarings: int
    total_composite_safe: bool
    scalable_powering: bool
    factor_enumeration: int = 0
    oracle_calls: int = 0


@dataclass(frozen=True, slots=True)
class ExistingSquaringMorphismReuseAudit:
    """Audit reuse of the production :class:`QuadraticPower` operator.

    The operator itself is the exact temporal quotient for ``x -> x^2-2`` and
    is constructed with logarithmically many semantic compositions.  The
    remaining distinction is source *injection*: the finite target-distance
    machine needs the source's Moore/order-depth code.  Assigning the prime
    source code ``horizon+1`` before proving terminal hit would assume the
    primality result.  Therefore ``semantic_source_code`` is ``None`` unless an
    independent candidate-derived extractor exists.
    """

    family: str
    parameter: int
    modulus: int
    trace_seed: int
    horizon: int
    operator_depth: int
    operator_build_compositions: int
    operator_description_bits: int
    raw_apply_trace_squarings: int
    prime_conditional_source_code: int
    semantic_machine_classes: int
    semantic_power_compositions: int
    prime_conditional_terminal_output: bool
    semantic_source_code: int | None
    source_code_candidate_derived: bool
    direct_log_time_terminal_decision_ready: bool
    blocker: str


@dataclass(frozen=True, slots=True)
class FermatLocalCyclotomicFrobeniusAudit:
    parameter: int
    level: int
    supplied_prime_factor: int
    factor_truth_only: bool
    cyclotomic_half_order: int
    stride_k: int
    stride_parity: int
    local_depth: int
    expected_split_bit: bool
    frobenius_rhs_sign: int
    equation_exact: bool
    ring_compositions: int
    equation: str


@dataclass(frozen=True, slots=True)
class FermatCofactorSignCancellationAudit:
    parameter: int
    level: int
    supplied_prime_factor: int
    cofactor: int
    cyclotomic_half_order: int
    factor_stride_k: int
    cofactor_stride_l: int
    factor_parity: int
    cofactor_parity: int
    same_parity: bool
    candidate_residue_mod_2m: int
    local_actions_compose_to_identity_on_X: bool
    conclusion: str
    factor_truth_only: bool = True


@dataclass(frozen=True, slots=True)
class FermatGlobalCyclotomicProbe:
    """Bounded candidate-global version of the partial equation.

    It computes ``(1+X)^(N-1)`` in ``(Z/NZ)[X]/(X^m+1)``.  A prime candidate
    is exactly 1.  Composite controls can fail strongly, but this bounded
    polynomial power is *not* promoted as the missing selector: generic
    all-split composites can be Frobenius pseudoprimes/false negatives for a
    particular probe and the cost is still linear in the exponent bit length.
    """

    parameter: int
    level: int
    modulus: int
    cyclotomic_half_order: int
    exponent_squarings: int
    residue_is_one: bool
    nonzero_coefficients: int
    nontrivial_gcds: tuple[int, ...]
    scalable: bool = False
    candidate_derived: bool = True


@dataclass(frozen=True, slots=True)
class FermatTerminalFoldFormula:
    """Root-free terminal fold of the additive Frobenius polynomial.

    At the terminal conductor ``m=(N-1)/2`` only two copies of the binomial row
    fold into each residue coefficient.  The complete polynomial congruence is
    therefore represented by

        c_0 = 2-C(2m,m)
        c_r = C(2m,r)-C(2m,r+m),  0<r<m.

    This removes the terminal Kummer carrier and the enormous power *as a
    symbolic formula*.  It does not make the central/folded binomial residues
    cheap to evaluate modulo a composite N; a nonunit denominator encountered
    by such an evaluator is a natural factor witness.
    """

    parameter: int
    modulus: int
    half_degree_log2: int
    fold_copies_per_coefficient: int
    constant_formula: str
    nonconstant_formula: str
    carrier_materialized: bool
    raw_power_replayed: bool
    factor_free_fast_evaluator_available: bool


def _inv_or_gcd(value: int, modulus: int) -> tuple[int | None, int]:
    value %= modulus
    g = gcd(value, modulus)
    if g != 1:
        return None, g
    return pow(value, -1, modulus), 1


def quadratic_cayley_trace_quotient(
    modulus: int,
    radicand: int,
    *,
    a: int = 1,
    b: int = 1,
) -> QuadraticCayleyTraceQuotient:
    """Project ``a+b*y`` in ``R[y]/(y^2-d)`` to its base-ring Cayley trace."""
    N, d, a, b = map(int, (modulus, radicand, a, b))
    if N <= 2 or not (N & 1):
        raise ValueError(N)
    d %= N
    a %= N
    b %= N
    norm = (a * a - b * b * d) % N
    inv, ng = _inv_or_gcd(norm, N)
    if inv is None:
        proper = ng if 1 < ng < N else None
        return QuadraticCayleyTraceQuotient(
            N,
            d,
            a,
            b,
            norm,
            ng,
            None,
            None,
            None,
            False,
            proper,
        )
    trace = (2 * (a * a + b * b * d) * inv) % N
    multiplier = (4 * a * b * inv) % N
    discr = (trace * trace - 4) % N
    exact = discr == (multiplier * multiplier * d) % N
    if not exact:
        raise AssertionError((N, d, a, b, trace, discr, multiplier))
    return QuadraticCayleyTraceQuotient(
        N,
        d,
        a,
        b,
        norm,
        1,
        trace,
        discr,
        multiplier,
        True,
        None,
    )


def _quadratic_pair_square(pair: tuple[int, int], d: int, N: int) -> tuple[int, int]:
    a, b = pair
    return ((a * a + b * b * d) % N, (2 * a * b) % N)


def cayley_square_commutation_audit(
    modulus: int,
    radicand: int,
    *,
    a: int = 1,
    b: int = 1,
) -> CayleySquareCommutationAudit:
    N, d = int(modulus), int(radicand) % int(modulus)
    first = quadratic_cayley_trace_quotient(N, d, a=a, b=b)
    if first.trace is None:
        raise ValueError(("nonunit-cayley-norm", first.norm_gcd))
    sq = _quadratic_pair_square((a % N, b % N), d, N)
    second = quadratic_cayley_trace_quotient(N, d, a=sq[0], b=sq[1])
    if second.trace is None:
        raise ValueError(("nonunit-squared-cayley-norm", second.norm_gcd))
    lucas = (first.trace * first.trace - 2) % N
    return CayleySquareCommutationAudit(
        N,
        d,
        (a % N, b % N),
        sq,
        first.trace,
        second.trace,
        lucas,
        second.trace == lucas,
    )


def dickson_orientation_power_of_two(
    trace: int,
    doublings: int,
    modulus: int,
) -> DicksonOrientationState:
    """Return trace/orientation for ``z^(2^doublings)`` with no extension state."""
    N, x, r = int(modulus), int(trace) % int(modulus), int(doublings)
    if N <= 1 or r < 0:
        raise ValueError((N, r))
    orient = 1 % N
    exponent = 1
    for _ in range(r):
        # B_(2e)=D_e * B_e; D_(2e)=D_e^2-2.
        orient = orient * x % N
        x = (x * x - 2) % N
        exponent <<= 1
    return DicksonOrientationState(N, exponent, x, orient, r)


def _negacyclic_mul(
    left: tuple[int, ...], right: tuple[int, ...], modulus: int
) -> tuple[int, ...]:
    m = len(left)
    if len(right) != m:
        raise ValueError((len(left), len(right)))
    out = [0] * m
    for i, a in enumerate(left):
        if not a:
            continue
        for j, b in enumerate(right):
            if not b:
                continue
            k = i + j
            value = a * b
            if k >= m:
                out[k - m] -= value
            else:
                out[k] += value
    return tuple(value % modulus for value in out)


def _negacyclic_power(
    base: tuple[int, ...], exponent: int, modulus: int
) -> tuple[tuple[int, ...], int]:
    m = len(base)
    e = int(exponent)
    result = (1,) + (0,) * (m - 1)
    current = tuple(v % modulus for v in base)
    compositions = 0
    while e:
        if e & 1:
            result = _negacyclic_mul(result, current, modulus)
            compositions += 1
        e >>= 1
        if e:
            current = _negacyclic_mul(current, current, modulus)
            compositions += 1
    return result, compositions


def _one_plus_x(m: int) -> tuple[int, ...]:
    if m < 2:
        raise ValueError(m)
    return (1, 1) + (0,) * (m - 2)


def _one_plus_x_to_m(m: int, modulus: int) -> tuple[int, ...]:
    """Exact residue of ``(1+X)^m`` under ``X^m=-1``."""
    # The two endpoints cancel: 1 + X^m -> 0.
    return (0,) + tuple(comb(m, j) % modulus for j in range(1, m))


def fermat_local_cyclotomic_frobenius_audit(
    parameter: int,
    level: int,
    supplied_prime_factor: int,
) -> FermatLocalCyclotomicFrobeniusAudit:
    """Verify the exact local partial-Frobenius sign equation ``(*)``.

    ``level`` is the Kummer split level from the existing germ convention.
    Put ``m=2^(n+level)``.  Fermat factors reaching the previous boundary have
    ``m | q-1`` and level ``level`` passes exactly when ``(q-1)/m`` is even.
    """
    n, level, q = int(parameter), int(level), int(supplied_prime_factor)
    if n < 2 or level < 1 or q <= 2:
        raise ValueError((n, level, q))
    m = 1 << (n + level)
    if (q - 1) % m:
        raise ValueError(("factor-does-not-reach-previous-layer", n, level, q, m))
    k = (q - 1) // m
    truth = ambient_capacity_truth("fermat", n)
    try:
        index = truth.local_factors.index(q)
    except ValueError as exc:
        raise ValueError(("not-an-audited-Fermat-factor", n, q)) from exc
    local_depth = truth.local_lift_depths[index]
    split = local_depth >= level
    if split != (k % 2 == 0):
        raise AssertionError((n, level, q, local_depth, k))

    A = _one_plus_x_to_m(m, q)
    Ak, compositions = _negacyclic_power(A, k, q)
    lhs = _negacyclic_mul(Ak, _one_plus_x(m), q)
    rhs = [0] * m
    rhs[0] = 1
    rhs[1] = 1 if (k & 1) == 0 else q - 1
    exact = lhs == tuple(rhs)
    if not exact:
        raise AssertionError((n, level, q, k, lhs[:8], tuple(rhs[:8])))
    return FermatLocalCyclotomicFrobeniusAudit(
        n,
        level,
        q,
        True,
        m,
        k,
        k & 1,
        local_depth,
        split,
        1 if split else -1,
        True,
        compositions,
        "A_m(X)^k(1+X)=1+(-1)^k X in F_q[X]/(X^m+1)",
    )


def fermat_cofactor_sign_cancellation_audit(
    parameter: int,
    level: int,
    supplied_prime_factor: int,
) -> FermatCofactorSignCancellationAudit:
    """Show exactly where the composite cofactor cancels the on-circle sign."""
    n, level, q = int(parameter), int(level), int(supplied_prime_factor)
    N = fermat_number(n)
    if N % q:
        raise ValueError((n, q))
    m = 1 << (n + level)
    if (q - 1) % m:
        raise ValueError(("factor-does-not-reach-previous-layer", n, level, q))
    c = N // q
    if (c - 1) % m:
        raise AssertionError((n, level, q, c, m))
    k = (q - 1) // m
    cofactor_exponent = (c - 1) // m
    # N == 1 (mod 2m).  Since q is 1 or 1+m modulo 2m at this one-bit
    # boundary and both residues are self-inverse, c has the same residue.
    if N % (2 * m) != 1:
        raise ValueError(("candidate-not-yet-at-this-global-boundary", n, level, 2 * m))
    same = (k & 1) == (cofactor_exponent & 1)
    if not same:
        raise AssertionError((n, level, q, c, k, cofactor_exponent))
    # X^q=(-1)^k X and X^c=(-1)^l X, so X^(qc)=X.
    return FermatCofactorSignCancellationAudit(
        n,
        level,
        q,
        c,
        m,
        k,
        cofactor_exponent,
        k & 1,
        cofactor_exponent & 1,
        True,
        N % (2 * m),
        True,
        "local Frobenius sign is real, but q and N/q carry the same bit so the on-circle N-action squares it away",
    )


def fermat_global_cyclotomic_probe(
    parameter: int, level: int
) -> FermatGlobalCyclotomicProbe:
    """Bounded whole-candidate partial Frobenius congruence.

    This is intentionally limited to modest ``m`` for research.  It never
    factors N and never calls Pepin, but it still performs one polynomial
    squaring per exponent bit and is therefore not a scalable release path.
    """
    n, level = int(parameter), int(level)
    if n < 2 or level < 1:
        raise ValueError((n, level))
    N = fermat_number(n)
    m = 1 << (n + level)
    if m > 512:
        raise ValueError(("bounded-cyclotomic-probe", m))
    residue, compositions = _negacyclic_power(_one_plus_x(m), N - 1, N)
    is_one = residue[0] == 1 and not any(residue[1:])
    gcds = tuple(
        sorted(
            {
                g
                for coefficient in residue
                for g in (
                    gcd((coefficient - (1 if coefficient is residue[0] else 0)) % N, N),
                )
                if 1 < g < N
            }
        )
    )
    return FermatGlobalCyclotomicProbe(
        n,
        level,
        N,
        m,
        compositions,
        is_one,
        sum(value != 0 for value in residue),
        gcds,
    )


def fermat_terminal_fold_formula(parameter: int) -> FermatTerminalFoldFormula:
    n = int(parameter)
    if n < 2:
        raise ValueError(n)
    N = fermat_number(n)
    # N-1 = 2*m at the terminal additive Frobenius fold.
    # m itself is represented by its log2; it is never materialized as a
    # polynomial degree or a coefficient vector.
    m_log2 = (1 << n) - 1
    return FermatTerminalFoldFormula(
        n,
        N,
        m_log2,
        2,
        "2 - C(2m,m) (mod N)",
        "C(2m,r) - C(2m,r+m) (mod N), 0<r<m",
        False,
        False,
        False,
    )


def _quadratic_pair_mul(
    left: tuple[int, int],
    right: tuple[int, int],
    d: int,
    modulus: int,
) -> tuple[int, int]:
    a, b = left
    c, e = right
    return ((a * c + b * e * d) % modulus, (a * e + b * c) % modulus)


def mersenne_cayley_lucas_quotient(exponent: int) -> MersenneCayleyLucasQuotientAudit:
    """Show that the additive Mersenne Frobenius probe is exactly LL trace 4.

    In ``R[s]/(s^2-3)`` take ``u=3+s``.  Since ``Norm(u)=6`` is a
    unit on every Mersenne candidate with odd exponent,

        u/conj(u) = (3+s)/(3-s) = 2+s.

    The latter has norm one and trace four, and squaring its trace is the
    Lucas--Lehmer map ``x -> x^2-2``.  Thus the quadratic additive probe has
    no independent extension-state payload after the Cayley quotient.
    """
    p = int(exponent)
    if p < 3 or not (p & 1):
        raise ValueError(p)
    N = mersenne_number(p)
    inv6, g = _inv_or_gcd(6, N)
    if inv6 is None:
        raise ValueError(("nonunit-six", p, N, g))
    # (3+s)/(3-s) = (3+s)^2 / 6 = 2+s.
    u2 = _quadratic_pair_square((3, 1), 3, N)
    ratio = (u2[0] * inv6 % N, u2[1] * inv6 % N)
    cayley = (2 % N, 1 % N)
    norm = (cayley[0] * cayley[0] - 3 * cayley[1] * cayley[1]) % N
    trace = (2 * cayley[0]) % N
    return MersenneCayleyLucasQuotientAudit(
        p,
        N,
        (3, 1),
        6 % N,
        cayley,
        norm,
        trace,
        ratio == cayley,
        4,
    )


def _lucas_trace_iterate(seed: int, steps: int, modulus: int) -> tuple[int, int]:
    x = int(seed) % int(modulus)
    steps = int(steps)
    if steps < 0:
        raise ValueError(steps)
    for _ in range(steps):
        x = (x * x - 2) % modulus
    return x, steps


def fermat_reix_lucas_quotient(
    parameter: int, *, max_steps: int = 1_000_000
) -> FermatReixLucasQuotientAudit:
    """Total composite-safe scalar Fermat quotient (Reix/Lucas theorem).

    Let ``z=(5+sqrt(21))/2``.  It has norm one and trace five, so
    ``z^(2^j)+z^(-2^j)`` obeys exactly ``x -> x^2-2``.  The Lucas/Lehmer
    rank-of-apparition theorem gives, for ``n>=1``,

        F_n prime  <=>  S_(2^n-2) == 0 (mod F_n),
        S_0=5, S_(j+1)=S_j^2-2.

    This closes the *semantic* composite-side quotient to one base-ring scalar.
    The direct evaluator below remains deliberately charged one ring squaring
    per recurrence level and is not promoted as binary-powered production.
    """
    n = int(parameter)
    if n < 1:
        raise ValueError(n)
    horizon = (1 << n) - 2
    if horizon > int(max_steps):
        raise ValueError(("bounded-Reix-audit", horizon, max_steps))
    N = fermat_number(n)
    terminal, work = _lucas_trace_iterate(5, horizon, N)
    return FermatReixLucasQuotientAudit(
        n,
        N,
        21,
        (5, 1),
        5,
        horizon,
        terminal,
        terminal == 0,
        work,
    )


def special_lucas_terminal_quotient(
    family: str,
    parameter: int,
    *,
    max_steps: int = 1_000_000,
) -> SpecialLucasTerminalQuotient:
    """One common total scalar quotient for the Fermat/Mersenne certificate.

    The two families differ only in seed/horizon:

    * Fermat: seed 5, horizon ``2^n-2`` (Reix/Lucas rank-of-apparition).
    * Mersenne: seed 4, horizon ``p-2`` (Lucas--Lehmer), after rejecting a
      composite exponent symbolically.

    The semantic state is one base-ring trace.  This function is research-only
    because direct recurrence evaluation is still linear in the horizon.
    """
    family = str(family)
    parameter = int(parameter)
    if family == "fermat":
        row = fermat_reix_lucas_quotient(parameter, max_steps=max_steps)
        return SpecialLucasTerminalQuotient(
            family,
            parameter,
            row.modulus,
            5,
            row.horizon,
            row.terminal_trace,
            row.terminal_zero,
            "prime" if row.terminal_zero else "composite",
            "Reix-Lucas rank-of-apparition",
            1,
            0,
            row.ring_squarings,
            True,
            False,
        )
    if family != "mersenne":
        raise ValueError(family)
    p = parameter
    if p < 2:
        raise ValueError(p)
    factor = mersenne_composite_exponent_factor(p)
    N = mersenne_number(p)
    if factor is not None:
        return SpecialLucasTerminalQuotient(
            family,
            p,
            N,
            4,
            0,
            1,
            False,
            "composite",
            "symbolic composite-exponent divisor",
            1,
            0,
            0,
            True,
            True,
        )
    if p == 2:
        return SpecialLucasTerminalQuotient(
            family,
            p,
            N,
            4,
            0,
            0,
            True,
            "prime",
            "M_2 base case",
            1,
            0,
            0,
            True,
            True,
        )
    horizon = p - 2
    if horizon > int(max_steps):
        raise ValueError(("bounded-LL-audit", horizon, max_steps))
    terminal, work = _lucas_trace_iterate(4, horizon, N)
    return SpecialLucasTerminalQuotient(
        family,
        p,
        N,
        4,
        horizon,
        terminal,
        terminal == 0,
        "prime" if terminal == 0 else "composite",
        "Lucas-Lehmer",
        1,
        0,
        work,
        True,
        False,
    )


def existing_squaring_morphism_reuse_audit(
    family: str,
    parameter: int,
    *,
    validate_raw: bool = True,
    max_steps: int = 1_000_000,
) -> ExistingSquaringMorphismReuseAudit:
    """Connect the Lucas trace quotient to the existing production power object.

    This function deliberately distinguishes two operations:

    * building/powering the *semantic transition* ``x -> x^2-2``; and
    * injecting the raw candidate seed into the finite target-distance quotient.

    The first operation is already logarithmic via :class:`QuadraticPower`.
    The second is exactly the still-missing extractor.  ``validate_raw`` may be
    enabled in research tests to compare against the direct Lucas recurrence,
    but that validation result is never used to fill ``semantic_source_code``.
    """
    from devtools.proofs.special_power_monoid import (
        build_special_power_program,
    )
    from number_compiler.arithmetic.functions.finite_unary import (
        unary_target_distance_machine,
    )

    fam = str(family)
    par = int(parameter)
    if fam == "fermat":
        if par < 1:
            raise ValueError((fam, par))
        modulus = fermat_number(par)
        seed = 5
        horizon = (1 << par) - 2
    elif fam == "mersenne":
        if par < 3 or not (par & 1):
            raise ValueError((fam, par))
        if mersenne_composite_exponent_factor(par) is not None:
            raise ValueError(("composite-exponent-has-symbolic-rejection", par))
        modulus = mersenne_number(par)
        seed = 4
        horizon = par - 2
    else:
        raise ValueError(fam)

    program = build_special_power_program(fam, par, horizon)
    if program.operator.depth != horizon:
        raise AssertionError((program.operator.depth, horizon))

    # The canonical finite quotient, *conditional on knowing the source really
    # is horizon transitions from target*, has source code horizon+1.
    machine = unary_target_distance_machine(horizon)
    source_if_prime = horizon + 1
    powered_state, semantic_ops, _nodes = machine.power_state(source_if_prime, horizon)
    prime_output = bool(machine.output(powered_state))
    if not prime_output:
        raise AssertionError((fam, par, horizon, powered_state))

    # Optional research differential only.  Crucially, this is not converted
    # into a source code: terminal zero is precisely the primality fact being
    # extracted.
    raw_work = 0
    if validate_raw:
        if horizon > int(max_steps):
            raise ValueError(("bounded-morphism-reuse-audit", horizon, max_steps))
        _terminal = program.operator.apply_trace(seed, modulus)
        raw_work = horizon

    return ExistingSquaringMorphismReuseAudit(
        fam,
        par,
        modulus,
        seed,
        horizon,
        program.operator.depth,
        program.construction_compositions,
        program.operator_description_bits,
        raw_work,
        source_if_prime,
        machine.classes,
        semantic_ops,
        prime_output,
        None,
        False,
        False,
        (
            "QuadraticPower already powers the transition; the Frobenius/Lucas "
            "quotient currently supplies only raw trace seed, not the candidate-derived "
            "target-distance/order-depth source code. Assigning horizon+1 would assume "
            "terminal hit/primality; raw apply_trace still costs one squaring per horizon."
        ),
    )


__all__ = [name for name in globals() if not name.startswith("_")]

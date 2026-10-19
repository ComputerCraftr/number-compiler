"""Normalized Fermat norm class and sparse t -> t^2 cyclotomic tower."""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd, isqrt

from devtools.experiments.algebra.dyadic_difference_germ_norm import (
    fermat_first_lift_norm_audit,
    gaussian_norm,
    gaussian_primary,
    quartic_jacobi_gaussian,
    zeta8_multiply,
    zeta8_subtract,
)
from number_compiler.sequences.power_numbers.numbers import fermat_number

# ---------------------------------------------------------------------------
# Normalized Fermat norm class and the t -> t^2 cyclotomic tower.
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class FermatNormalizedNormClassAudit:
    """Normalize the moving Kummer target to the two-term element 1-t*w.

    The previously constructed target

        alpha1(t) = (-t,-1,t-1,t-1)

    satisfies ``alpha1 = epsilon * beta`` with

        beta = 1 - t*w,
        epsilon = -(w+w^2+w^3).

    The correction ``epsilon`` is itself a *fixed* relative norm from
    ``K1(sqrt(sqrt(2)))/K1``.  Hence alpha1 and beta represent exactly the
    same class in the relative norm quotient for every Fermat parameter.
    This removes the moving four-coefficient target without using factors,
    CRT components, or local roots.
    """

    parameter: int
    modulus: int
    t: int
    alpha1: tuple[int, int, int, int]
    beta: tuple[int, int, int, int]
    fixed_unit: tuple[int, int, int, int]
    fixed_preimage_u: tuple[int, int, int, int]
    fixed_preimage_v: tuple[int, int, int, int]
    fixed_unit_norm: tuple[int, int, int, int]
    reconstructed_alpha1: tuple[int, int, int, int]
    candidate_derived: bool = True
    factor_enumeration: int = 0
    root_branch_enumeration: int = 0

    @property
    def exact(self) -> bool:
        return (
            self.fixed_unit_norm == self.fixed_unit
            and self.reconstructed_alpha1 == self.alpha1
        )


@dataclass(frozen=True, slots=True)
class FermatCyclotomicNormTowerStep:
    """One coefficient-halving cyclotomic norm identity.

    If ``z_next^2=z`` then

        Norm(1-a*z_next) = (1-a*z_next)(1+a*z_next)
                              = 1-a^2*z.

    Thus a Fermat coefficient that is itself a square can be moved one level
    upward in the 2-power cyclotomic tower while taking its integer square
    root.  The representation stores only exponents/coefficients; it never
    materializes the exponentially growing cyclotomic basis.
    """

    source_root_order: int
    lifted_root_order: int
    source_coefficient: int
    lifted_coefficient: int
    source_terms: int = 2
    lifted_terms: int = 2

    @property
    def exact(self) -> bool:
        return (
            self.lifted_root_order == 2 * self.source_root_order
            and self.lifted_coefficient * self.lifted_coefficient
            == self.source_coefficient
        )


@dataclass(frozen=True, slots=True)
class FermatCyclotomicNormTowerAudit:
    """Compact alternate-radix form of the normalized Fermat target.

    Starting with ``beta_t = 1-t*zeta_8`` and
    ``t=2^(2^(n-2))``, repeated exact cyclotomic norm lifting yields

        beta_t = Norm_{Q(zeta_(2^(n+1)))/Q(zeta_8)}
                     (1 - 2*zeta_(2^(n+1))).

    The terminal element always has two nonzero coefficients.  Only its
    *address* in the cyclotomic tower grows, in O(n) steps.  This proves the
    huge Fermat coefficient is not the remaining source of exponential state.
    It does not by itself decide the Kummer norm class: the odd-prime support
    of the terminal principal ideal can still contain split and inert packets.
    """

    parameter: int
    start_t: int
    start_root_order: int
    terminal_root_order: int
    terminal_coefficient: int
    steps: tuple[FermatCyclotomicNormTowerStep, ...]
    terminal_descriptor: str
    candidate_modulus: int
    terminal_absolute_norm: int
    materialized_cyclotomic_coefficients: int = 0
    candidate_derived: bool = True

    @property
    def exact(self) -> bool:
        return (
            all(step.exact for step in self.steps)
            and self.terminal_coefficient == 2
            and self.terminal_root_order == 1 << (self.parameter + 1)
            and len(self.steps) == self.parameter - 2
            and self.terminal_absolute_norm == self.candidate_modulus
        )


@dataclass(frozen=True, slots=True)
class FermatFixedTraceNormShortcutAudit:
    """One-sided exact norm witness obtained from a fixed trace section.

    For ``beta_t=1-t*w`` choose the fixed

        U0 = -w + w^2 + w^3.

    Then an exact identity reduces the relative norm equation to

        V^2 = t/2 + (t/2-2)i.

    The right side lies in ``Z[i]``.  It is a square in ``Z[zeta_8]`` iff it
    is a Gaussian square itself or becomes one after division by ``i``.  This
    can be checked and a witness constructed using integer square roots only.

    A hit is an unconditional positive certificate.  A miss is *not* a
    negative certificate because other choices of U can solve the norm equation.
    """

    parameter: int
    t: int
    beta: tuple[int, int, int, int]
    fixed_u: tuple[int, int, int, int]
    gaussian_square_target: tuple[int, int]
    v: tuple[int, int, int, int] | None
    norm_value: tuple[int, int, int, int] | None
    modular_fourth_root: int | None
    modular_fourth_root_square: int | None
    expected_first_root: int
    integer_square_roots: int
    candidate_derived: bool = True
    negative_certificate: bool = False

    @property
    def found(self) -> bool:
        return self.v is not None

    @property
    def exact(self) -> bool:
        return (
            self.found
            and self.norm_value == self.beta
            and self.modular_fourth_root is not None
            and self.modular_fourth_root_square == self.expected_first_root
        )


@dataclass(frozen=True, slots=True)
class QuarticAuxiliarySignatureCollision:
    """A holdout collision for a finite vector of candidate-derived quartic phases.

    The two ``t`` values have the same complete phase vector for the supplied
    rational auxiliaries but opposite all-local next-lift truth.  Truth is
    audit-only; the signatures themselves are obtained by Gaussian reciprocity
    directly from ``t^4+1`` without factoring it.
    """

    auxiliaries: tuple[int, ...]
    left_t: int
    right_t: int
    signature: tuple[int | None, ...]
    left_all_local_truth: bool
    right_all_local_truth: bool

    @property
    def defeats_signature(self) -> bool:
        return self.left_all_local_truth != self.right_all_local_truth and bool(
            self.signature
        )


def fermat_normalized_norm_class(parameter: int) -> FermatNormalizedNormClassAudit:
    """Return the exact two-term representative of the second-lift norm class."""
    n = int(parameter)
    if n < 2:
        raise ValueError(n)
    first = fermat_first_lift_norm_audit(n)
    t = first.t
    alpha1 = (-t, -1, t - 1, t - 1)
    beta = (1, -t, 0, 0)
    epsilon = (0, -1, -1, -1)

    # epsilon = Norm(U0 + sqrt(sqrt(2))*V0), with U0=V0 fixed forever.
    preimage = (-1, -1, -1, 0)
    sqrt2 = (0, 1, 0, -1)
    epsilon_norm = zeta8_subtract(
        zeta8_multiply(preimage, preimage),
        zeta8_multiply(sqrt2, zeta8_multiply(preimage, preimage)),
    )
    rebuilt = zeta8_multiply(epsilon, beta)
    return FermatNormalizedNormClassAudit(
        n,
        first.modulus,
        t,
        alpha1,
        beta,
        epsilon,
        preimage,
        preimage,
        epsilon_norm,
        rebuilt,
    )


def fermat_cyclotomic_norm_tower(parameter: int) -> FermatCyclotomicNormTowerAudit:
    """Compress ``1-t*zeta_8`` to ``1-2*zeta_(2^(n+1))`` by norm lifting."""
    n = int(parameter)
    if n < 2:
        raise ValueError(n)
    t = 1 << (1 << (n - 2))
    coefficient = t
    root_order = 8
    steps: list[FermatCyclotomicNormTowerStep] = []
    while coefficient > 2:
        lifted = isqrt(coefficient)
        if lifted * lifted != coefficient:
            raise AssertionError((n, coefficient))
        step = FermatCyclotomicNormTowerStep(
            root_order,
            root_order * 2,
            coefficient,
            lifted,
        )
        if not step.exact:
            raise AssertionError(step)
        steps.append(step)
        coefficient = lifted
        root_order *= 2
    candidate = fermat_number(n)
    # Phi_(2^(n+1))(2) = 2^(2^n)+1 = F_n.  Since the terminal root order is a
    # power of two, the absolute norm of 1-2*zeta is exactly that cyclotomic
    # value.  Compute it from the sparse descriptor, not from a degree-2^n basis.
    absolute_norm = (1 << (root_order // 2)) + 1
    return FermatCyclotomicNormTowerAudit(
        n,
        t,
        8,
        root_order,
        coefficient,
        tuple(steps),
        f"1 - 2*zeta_{root_order}",
        candidate,
        absolute_norm,
    )


def _gaussian_integer_square_root(value: tuple[int, int]) -> tuple[int, int] | None:
    """Return one exact square root in Z[i], or None."""
    a, b = map(int, value)
    norm = a * a + b * b
    radius = isqrt(norm)
    if radius * radius != norm:
        return None
    p2_num = radius + a
    q2_num = radius - a
    if (p2_num & 1) or (q2_num & 1):
        return None
    p2, q2 = p2_num // 2, q2_num // 2
    if p2 < 0 or q2 < 0:
        return None
    p, q = isqrt(p2), isqrt(q2)
    if p * p != p2 or q * q != q2:
        return None
    if 2 * p * q != abs(b):
        return None
    if b < 0:
        q = -q
    return p, q


def fermat_fixed_trace_norm_shortcut(
    parameter: int,
) -> FermatFixedTraceNormShortcutAudit:
    """Try the fixed-trace Gaussian-square section of the normalized norm conic."""
    normalized = fermat_normalized_norm_class(parameter)
    t = normalized.t
    if t & 1:
        raise AssertionError(t)
    half = t // 2
    gaussian = (half, half - 2)
    fixed_u = (0, -1, 1, 1)
    sqrt2 = (0, 1, 0, -1)

    # First try V in Q(i).
    root = _gaussian_integer_square_root(gaussian)
    v: tuple[int, int, int, int] | None = None
    square_root_calls = 1
    if root is not None:
        v = (root[0], 0, root[1], 0)
    else:
        # If V=w*y, then V^2=i*y^2.  Therefore y^2=gaussian/i.
        divided_by_i = (gaussian[1], -gaussian[0])
        root = _gaussian_integer_square_root(divided_by_i)
        square_root_calls += 1
        if root is not None:
            v = (0, root[0], 0, root[1])

    value = None
    modular_root = None
    modular_square = None
    first = fermat_first_lift_norm_audit(parameter)
    if v is not None:
        value = zeta8_subtract(
            zeta8_multiply(fixed_u, fixed_u),
            zeta8_multiply(sqrt2, zeta8_multiply(v, v)),
        )
        if value != normalized.beta:
            raise AssertionError((parameter, value, normalized.beta))
        # Modulo beta=1-t*w we have w=t^-1.  Dividing U by V therefore gives
        # an actual square root of sqrt(2) in Z/F_nZ whenever V is a unit.
        N = normalized.modulus
        w_value = pow(t, -1, N)

        def evaluate(coefficients: tuple[int, int, int, int]) -> int:
            return (
                sum(int(c) * pow(w_value, j, N) for j, c in enumerate(coefficients)) % N
            )

        u_mod = evaluate(fixed_u)
        v_mod = evaluate(v)
        if gcd(v_mod, N) == 1:
            modular_root = u_mod * pow(v_mod, -1, N) % N
            modular_square = modular_root * modular_root % N
            if modular_square != first.canonical_root:
                raise AssertionError((parameter, modular_square, first.canonical_root))
    return FermatFixedTraceNormShortcutAudit(
        int(parameter),
        t,
        normalized.beta,
        fixed_u,
        gaussian,
        v,
        value,
        modular_root,
        modular_square,
        first.canonical_root,
        square_root_calls,
    )


def _quartic_auxiliary_signature_for_t(
    t: int,
    auxiliaries: tuple[int, ...],
) -> tuple[int | None, ...]:
    """Candidate-derived quartic phase vector for the generalized t^4+1 control."""
    tt = int(t)
    if tt <= 0 or tt & 1:
        raise ValueError(t)
    modulus = tt**4 + 1
    denominator = (1, -(tt * tt))
    if not gaussian_primary(denominator) or gaussian_norm(denominator) != modulus:
        raise AssertionError((tt, denominator, modulus))
    out: list[int | None] = []
    for auxiliary in auxiliaries:
        phase, _steps, _gcds = quartic_jacobi_gaussian(
            (int(auxiliary), 0),
            denominator,
            rational_modulus=modulus,
        )
        out.append(phase)
    return tuple(out)


def fermat_quartic_auxiliary_holdout_guard() -> tuple[
    QuarticAuxiliarySignatureCollision, ...
]:
    """Freeze holdout failures of a bounded four-auxiliary phase-vector fit.

    ``(34,22,42,5)`` separates the generalized even ``t<=100`` training controls
    after a greedy bounded search, but it does not generalize.  These four exact
    collisions use only candidate-derived phase vectors.  The Boolean labels are
    independently audited from the displayed small factorizations in the test
    suite; they never feed back into phase computation.

    This does not prove that every possible auxiliary family fails.  It prevents
    a finite character vector fitted on the Fermat-sized controls from being
    promoted as the all-local norm selector without a theorem.
    """
    auxiliaries = (34, 22, 42, 5)
    controls = (
        # training t, holdout t, training truth, holdout truth
        (12, 148, True, False),
        (68, 152, False, True),
        (14, 176, False, True),
        (28, 192, True, False),
    )
    rows: list[QuarticAuxiliarySignatureCollision] = []
    for left_t, right_t, left_truth, right_truth in controls:
        left_signature = _quartic_auxiliary_signature_for_t(left_t, auxiliaries)
        right_signature = _quartic_auxiliary_signature_for_t(right_t, auxiliaries)
        if left_signature != right_signature:
            raise AssertionError((left_t, right_t, left_signature, right_signature))
        rows.append(
            QuarticAuxiliarySignatureCollision(
                auxiliaries,
                left_t,
                right_t,
                left_signature,
                left_truth,
                right_truth,
            )
        )
    return tuple(rows)

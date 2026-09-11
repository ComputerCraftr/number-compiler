"""Lifted quartic reciprocity and fixed-rank Fermat relative-norm experiments."""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass
from math import gcd

from devtools.experiments.algebra.dyadic_difference_germ_core import (
    ambient_capacity_truth,
)
from number_compiler.sequences.prime.set import jacobi_symbol

# ---------------------------------------------------------------------------
# Lifted quartic reciprocity and the first exact Fermat norm lift.
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class GaussianQuarticStep:
    """One exact Euclidean step in Z[i] for the quartic Jacobi symbol."""

    alpha: tuple[int, int]
    beta: tuple[int, int]
    quotient: tuple[int, int]
    remainder: tuple[int, int]
    ramified_power: int
    primary_unit_power: int
    next_beta: tuple[int, int]
    phase_delta: int
    remainder_norm_gcd: int


@dataclass(frozen=True, slots=True)
class GaussianQuarticReciprocityAudit:
    """Uncollapsed quartic-Jacobi descent on the canonical Fermat ideal.

    The phase is encoded as an exponent of ``i`` in ``0..3``.  Keeping the
    entire Euclidean transcript is stronger than keeping only the rational
    ``+/-1`` quartic-residuosity bit, but it is still an *ideal product*
    character: local quartic phases multiply.  F4/F5 are the bounded guard
    showing that the even bad packet can therefore disappear completely.
    """

    parameter: int
    modulus: int
    numerator: tuple[int, int]
    primary_denominator: tuple[int, int]
    phase_exponent: int | None
    steps: tuple[GaussianQuarticStep, ...]
    natural_gcds: tuple[int, ...]
    candidate_derived: bool = True
    factor_enumeration: int = 0
    root_branch_enumeration: int = 0
    splitting_sensitive: bool = False

    @property
    def phase_unit(self) -> str:
        if self.phase_exponent is None:
            return "0"
        return {0: "1", 1: "i", 2: "-1", 3: "-i"}.get(self.phase_exponent, "0")


@dataclass(frozen=True, slots=True)
class FermatFirstLiftNormAudit:
    """Exact factor-free first transverse lift and its Gaussian norm identity.

    Write ``A=2^(2^(n-1))`` and ``t^2=A``.  The identity

        (-t+(t-1)i)^2 - 2(-t/2+(t/2-1)i)^2 = 1 - A i

    is an integral relative-norm witness.  Modulo ``F_n`` it is the same
    cyclotomic half-angle fact that gives the canonical square root of 2

        r1 = t + t^-1.

    This is the guaranteed first extra local layer.  It does not solve the
    next lift: asking for ``sqrt(r1)`` is exactly where F4 and F5 diverge.
    """

    parameter: int
    modulus: int
    t: int
    canonical_root: int
    root_square: int
    gaussian_x: tuple[int, int]
    gaussian_y: tuple[int, int]
    gaussian_target: tuple[int, int]
    gaussian_norm_value: tuple[int, int]
    radix_squarings: int
    inversions: int
    candidate_derived: bool = True
    factor_enumeration: int = 0
    root_branch_enumeration: int = 0

    @property
    def exact(self) -> bool:
        return (
            self.root_square == 2 % self.modulus
            and self.gaussian_norm_value == self.gaussian_target
        )


@dataclass(frozen=True, slots=True)
class FermatNextLiftGuard:
    """Candidate-only data available at the first genuinely missing lift."""

    parameter: int
    modulus: int
    current_root: int
    jacobi_phase: int
    quartic_phase_exponent: int | None
    next_equation: str
    candidate_derived: bool = True
    factor_enumeration: int = 0
    root_branch_enumeration: int = 0
    decided: bool = False


def _gaussian_mul(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    a, b = left
    c, d = right
    return a * c - b * d, a * d + b * c


def _gaussian_sub(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    return left[0] - right[0], left[1] - right[1]


def _gaussian_norm(value: tuple[int, int]) -> int:
    return value[0] * value[0] + value[1] * value[1]


def _nearest_integer(numerator: int, denominator: int) -> int:
    """Nearest integer to an exact rational, with deterministic even ties."""
    if denominator <= 0:
        raise ValueError(denominator)
    q, r = divmod(int(numerator), int(denominator))
    twice = 2 * r
    if twice < denominator:
        return q
    if twice > denominator:
        return q + 1
    return q if not (q & 1) else q + 1


def _gaussian_quotient(
    alpha: tuple[int, int], beta: tuple[int, int]
) -> tuple[int, int]:
    """Coordinatewise nearest Gaussian integer to alpha/beta."""
    a, b = alpha
    c, d = beta
    denominator = _gaussian_norm(beta)
    if not denominator:
        raise ZeroDivisionError(beta)
    real = a * c + b * d
    imag = b * c - a * d
    return _nearest_integer(real, denominator), _nearest_integer(imag, denominator)


def _gaussian_divide_one_plus_i(value: tuple[int, int]) -> tuple[int, int]:
    a, b = value
    if (a - b) & 1:
        raise ValueError(("not-divisible-by-1+i", value))
    return (a + b) // 2, (b - a) // 2


def _gaussian_mul_i_power(value: tuple[int, int], exponent: int) -> tuple[int, int]:
    a, b = value
    return ((a, b), (-b, a), (-a, -b), (b, -a))[int(exponent) & 3]


def _gaussian_primary(value: tuple[int, int]) -> bool:
    a, b = value
    return not (b & 1) and (a + b) % 4 == 1


def _gaussian_make_primary(value: tuple[int, int]) -> tuple[tuple[int, int], int]:
    # Return gamma / i^n, exactly matching the reciprocity recurrence.
    for n in range(4):
        candidate = _gaussian_mul_i_power(value, -n)
        if _gaussian_primary(candidate):
            return candidate, n
    raise AssertionError(("no-primary-associate", value))


def _quartic_jacobi_gaussian(
    alpha: tuple[int, int],
    beta: tuple[int, int],
    *,
    rational_modulus: int,
) -> tuple[int | None, tuple[GaussianQuarticStep, ...], tuple[int, ...]]:
    """Eisenstein's exact quartic-Jacobi Euclidean descent in Z[i].

    The recurrence is the Gaussian specialization recorded by Bach--Sandlund
    (their equations (17)--(20) and Section 7).  ``None`` denotes symbol zero.
    We additionally retain gcd(N, Norm(remainder)) at every step; this is a
    legal natural reduction witness and is never used to choose a factor.
    """
    if not _gaussian_primary(beta):
        raise ValueError(("primary-denominator-required", beta))
    N = int(rational_modulus)
    if N <= 1:
        raise ValueError(N)
    phase = 0
    steps: list[GaussianQuarticStep] = []
    gcds: set[int] = set()
    current_alpha = (int(alpha[0]), int(alpha[1]))
    current_beta = (int(beta[0]), int(beta[1]))
    while True:
        if current_beta == (1, 0) or current_alpha == (1, 0):
            return phase & 3, tuple(steps), tuple(sorted(gcds))
        quotient = _gaussian_quotient(current_alpha, current_beta)
        remainder = _gaussian_sub(current_alpha, _gaussian_mul(quotient, current_beta))
        if remainder == (0, 0):
            return None, tuple(steps), tuple(sorted(gcds))
        norm_gcd = gcd(_gaussian_norm(remainder), N)
        if 1 < norm_gcd < N:
            gcds.add(norm_gcd)

        ramified = 0
        reduced = remainder
        while not ((reduced[0] - reduced[1]) & 1):
            reduced = _gaussian_divide_one_plus_i(reduced)
            ramified += 1
        next_beta, unit_power = _gaussian_make_primary(reduced)

        c, d = current_beta
        e, _f = next_beta
        first_numerator = c - d - d * d - 1
        if first_numerator % 4 or (c - 1) % 2 or ((e - 1) * (c - 1)) % 4:
            raise AssertionError((current_beta, next_beta))
        delta = (
            ramified * (first_numerator // 4)
            - unit_power * ((c - 1) // 2)
            + 2 * (((e - 1) * (c - 1)) // 4)
        ) & 3
        steps.append(
            GaussianQuarticStep(
                current_alpha,
                current_beta,
                quotient,
                remainder,
                ramified,
                unit_power,
                next_beta,
                delta,
                norm_gcd,
            )
        )
        phase = (phase + delta) & 3
        current_alpha, current_beta = current_beta, next_beta


def fermat_gaussian_quartic_reciprocity_audit(
    parameter: int,
    *,
    numerator: int = 2,
) -> GaussianQuarticReciprocityAudit:
    """Run the full quartic phase descent on the canonical Fermat ideal.

    ``F_n=A^2+1`` gives a canonical Gaussian prime-ideal product of norm F_n.
    The primary associate ``1-A*i`` is used as denominator.  No rational or
    Gaussian factorization is performed.
    """
    n = int(parameter)
    if n < 2:
        raise ValueError(n)
    A = 1 << (1 << (n - 1))
    modulus = A * A + 1
    beta = (1, -A)
    if not _gaussian_primary(beta) or _gaussian_norm(beta) != modulus:
        raise AssertionError((n, beta, modulus))
    phase, steps, gcds = _quartic_jacobi_gaussian(
        (int(numerator), 0),
        beta,
        rational_modulus=modulus,
    )
    return GaussianQuarticReciprocityAudit(
        n,
        modulus,
        (int(numerator), 0),
        beta,
        phase,
        steps,
        gcds,
    )


def fermat_first_lift_norm_audit(parameter: int) -> FermatFirstLiftNormAudit:
    """Construct the guaranteed first Fermat half-root with no local roots."""
    n = int(parameter)
    if n < 2:
        raise ValueError(n)
    width = 1 << n
    modulus = (1 << width) + 1
    t = 1 << (1 << (n - 2))
    t_mod = t % modulus
    canonical_root = (t_mod + pow(t_mod, -1, modulus)) % modulus

    # Integral Gaussian norm identity.  Here t^2=A and A^2+1=F_n.
    x = (-t, t - 1)
    y = (-t // 2, t // 2 - 1)
    x2 = _gaussian_mul(x, x)
    y2 = _gaussian_mul(y, y)
    norm_value = (x2[0] - 2 * y2[0], x2[1] - 2 * y2[1])
    target = (1, -(t * t))
    return FermatFirstLiftNormAudit(
        n,
        modulus,
        t,
        canonical_root,
        canonical_root * canonical_root % modulus,
        x,
        y,
        target,
        norm_value,
        max(0, n - 2),
        1,
    )


def fermat_next_lift_guard(parameter: int) -> FermatNextLiftGuard:
    """Expose exactly what remains after the factor-free first lift.

    The next predicate is ``exists x: x^2=r1`` in every local component.
    Jacobi and the complete Gaussian quartic ideal-product phase both collapse
    on F4/F5, so this routine deliberately does not manufacture a decision.
    """
    first = fermat_first_lift_norm_audit(parameter)
    quartic = fermat_gaussian_quartic_reciprocity_audit(parameter)
    return FermatNextLiftGuard(
        int(parameter),
        first.modulus,
        first.canonical_root,
        jacobi_symbol(first.canonical_root, first.modulus),
        quartic.phase_exponent,
        "x^2 = r1 in every local component (equivalently the next relative norm preimage)",
    )


@dataclass(frozen=True, slots=True)
class FermatSecondLiftNormSearchAudit:
    """Bounded candidate-only search for the next relative norm preimage.

    Work in O_K = Z[zeta_8], with ``w=zeta_8`` and ``sqrt(2)=w-w^3``.
    The first exact lift gives an element ``alpha1`` whose coordinates are

        (-t, -1, t-1, t-1),  t=2^(2^(n-2)).

    A second lift would provide U,V in O_K satisfying

        U^2 - sqrt(2) V^2 = alpha1.

    This meet-in-the-middle search enumerates *coefficient vectors*, never
    factors, CRT components, or local roots.  Finding a preimage is an exact
    positive witness.  Exhausting a finite coefficient box is deliberately
    not treated as a negative certificate.
    """

    parameter: int
    modulus: int
    coefficient_bound: int
    target: tuple[int, int, int, int]
    u: tuple[int, int, int, int] | None
    v: tuple[int, int, int, int] | None
    norm_value: tuple[int, int, int, int] | None
    coefficient_vectors_scanned: int
    candidate_derived: bool = True
    factor_enumeration: int = 0
    root_branch_enumeration: int = 0
    negative_certificate: bool = False

    @property
    def found(self) -> bool:
        return self.u is not None

    @property
    def exact(self) -> bool:
        return self.found and self.norm_value == self.target


def _zeta8_mul(
    left: tuple[int, int, int, int],
    right: tuple[int, int, int, int],
) -> tuple[int, int, int, int]:
    """Multiply in Z[w]/(w^4+1), w=zeta_8."""
    temporary = [0] * 7
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            temporary[i + j] += a * b
    for degree in range(6, 3, -1):
        temporary[degree - 4] -= temporary[degree]
    return temporary[0], temporary[1], temporary[2], temporary[3]


def _zeta8_sub(
    left: tuple[int, int, int, int],
    right: tuple[int, int, int, int],
) -> tuple[int, int, int, int]:
    return (
        left[0] - right[0],
        left[1] - right[1],
        left[2] - right[2],
        left[3] - right[3],
    )


def _coefficient_vectors(bound: int) -> Iterator[tuple[int, int, int, int]]:
    values = range(-bound, bound + 1)
    for a in values:
        for b in values:
            for c in values:
                for d in values:
                    yield (a, b, c, d)


def fermat_second_lift_norm_search(
    parameter: int,
    *,
    coefficient_bound: int = 4,
) -> FermatSecondLiftNormSearchAudit:
    """Search a fixed Z[zeta_8] coefficient box for the second norm lift.

    The search is a diagnostic for the new all-local norm formulation.  It is
    intentionally not wired to ``candidate_derived_splitting_weight`` because
    a bounded miss proves nothing and the search cost is exponential in the
    coefficient bound.
    """
    n = int(parameter)
    bound = int(coefficient_bound)
    if n < 2 or bound < 0:
        raise ValueError((n, bound))
    first = fermat_first_lift_norm_audit(n)
    t = first.t
    target = (-t, -1, t - 1, t - 1)
    sqrt2 = (0, 1, 0, -1)

    # Hash U^2 once, then scan V.  This is O(B^4) state and O(B^4) probes,
    # rather than the naive O(B^8) pair enumeration.
    squares: dict[tuple[int, int, int, int], tuple[int, int, int, int]] = {}
    count = 0
    for u in _coefficient_vectors(bound):
        squares.setdefault(_zeta8_mul(u, u), u)
        count += 1
    for v in _coefficient_vectors(bound):
        sv2 = _zeta8_mul(sqrt2, _zeta8_mul(v, v))
        required_u2 = (
            target[0] + sv2[0],
            target[1] + sv2[1],
            target[2] + sv2[2],
            target[3] + sv2[3],
        )
        count += 1
        match = squares.get(required_u2)
        if match is not None:
            u = match
            value = _zeta8_sub(_zeta8_mul(u, u), sv2)
            return FermatSecondLiftNormSearchAudit(
                n,
                first.modulus,
                bound,
                target,
                u,
                v,
                value,
                count,
            )
    return FermatSecondLiftNormSearchAudit(
        n,
        first.modulus,
        bound,
        target,
        None,
        None,
        None,
        count,
    )


def fermat_second_lift_local_truth(parameter: int) -> tuple[bool, tuple[bool, ...]]:
    """Factor-backed audit truth for the second norm lift; never a solver."""
    truth = ambient_capacity_truth("fermat", int(parameter))
    local = tuple(depth >= 2 for depth in truth.local_lift_depths)
    return all(local), local


@dataclass(frozen=True, slots=True)
class FermatCyclotomicGermComparison:
    """Audit the historical Fermat order character against the new germ bit.

    The v0.32 ``CyclotomicOrderCharacter`` encoded the two-primary order/Moore
    class of an already-present phase.  On a prime Fermat field, the ambient
    group order is globally known, so that order class can also answer higher
    residuosity questions.  On a composite candidate those are different
    pieces of information: the current phase can have the same fixed order in
    every CRT component while the *ambient* group has different remaining
    two-capacity.

    Candidate-derived fields below use only the canonical first transverse root
    and repeated squaring modulo ``F_n``.  Factor-backed local fields are audit
    labels only; they are never used to construct the character depth.
    """

    parameter: int
    modulus: int
    baseline_order_v2: int
    canonical_first_root: int
    candidate_root_order_v2: int | None
    normalized_current_character_depth: int | None
    local_factors: tuple[int, ...]
    local_root_order_v2: tuple[int | None, ...]
    local_ambient_v2: tuple[int, ...]
    local_germ_depths: tuple[int, ...]
    next_germ_bits: tuple[bool, ...]
    all_local_next_germ: bool
    candidate_derived_character: bool = True
    factor_truth_is_audit_only: bool = True

    @property
    def current_character_is_uniform_locally(self) -> bool:
        values = {value for value in self.local_root_order_v2}
        return len(values) <= 1

    @property
    def character_alone_decides_next_germ(self) -> bool:
        # A current-order character reports the order of the phase that already
        # exists.  It contains no ambient group-order coordinate, so it cannot
        # certify the existence of a preimage one layer higher.
        return False


@dataclass(frozen=True, slots=True)
class FermatHistoricalSignGuard:
    """Cross-candidate guard separating old sign notions from the germ."""

    left_parameter: int
    right_parameter: int
    same_normalized_current_character: bool
    same_next_germ_bit: bool
    historical_radix_sign_was_depth_quotient: bool
    conclusion: str


def _two_power_order_exponent_from_squaring(
    value: int,
    modulus: int,
    *,
    max_steps: int,
) -> int | None:
    """Return k when value has exact order 2**k, else ``None``.

    This intentionally performs no factorization and no discrete logarithm.
    It is suitable for the canonical Fermat first root, whose order is known to
    be a power of two whenever that root exists.
    """
    x = int(value) % int(modulus)
    if gcd(x, modulus) != 1:
        return None
    for exponent in range(int(max_steps) + 1):
        if x == 1:
            return exponent
        x = x * x % modulus
    return None


def fermat_cyclotomic_germ_comparison(parameter: int) -> FermatCyclotomicGermComparison:
    """Compare the old current-phase order character with the next germ bit.

    The character side is candidate-derived.  The local ambient/germ columns
    are factor-backed differential truth, exactly like ``ambient_capacity_truth``.
    This makes F4/F5 a non-circular counterexample: both canonical first roots
    have normalized current order depth one, but only F4 has another local
    half-root.
    """
    n = int(parameter)
    if n < 2:
        raise ValueError(n)
    first = fermat_first_lift_norm_audit(n)
    baseline = n + 1
    candidate_order = _two_power_order_exponent_from_squaring(
        first.canonical_root,
        first.modulus,
        max_steps=baseline + 2,
    )
    normalized = None if candidate_order is None else candidate_order - baseline

    truth = ambient_capacity_truth("fermat", n)
    local_orders = tuple(
        _two_power_order_exponent_from_squaring(
            first.canonical_root % q,
            q,
            max_steps=baseline + 2,
        )
        for q in truth.local_factors
    )
    next_bits = tuple(depth >= 2 for depth in truth.local_lift_depths)
    return FermatCyclotomicGermComparison(
        n,
        first.modulus,
        baseline,
        first.canonical_root,
        candidate_order,
        normalized,
        truth.local_factors,
        local_orders,
        truth.local_ambient_v2,
        truth.local_lift_depths,
        next_bits,
        all(next_bits),
    )


def fermat_historical_sign_guard() -> FermatHistoricalSignGuard:
    """Lock in the F4/F5 distinction between phase order and ambient lift.

    The historical v0.31 ``radix_sign`` is also explicitly *not* promoted: its
    bounded CEGAR result reconstructed all Fermat source states rather than the
    small order-depth quotient.  This function records that historical semantic
    guard while the executable F4/F5 check addresses the v0.32 order character.
    """
    f4 = fermat_cyclotomic_germ_comparison(4)
    f5 = fermat_cyclotomic_germ_comparison(5)
    return FermatHistoricalSignGuard(
        4,
        5,
        f4.normalized_current_character_depth == f5.normalized_current_character_depth,
        f4.all_local_next_germ == f5.all_local_next_germ,
        False,
        (
            "the old coefficient-lift radix sign is source orientation, and the "
            "old current-phase order character records an already-present circle; "
            "the missing germ bit is the next higher residuosity/Kummer-preimage sign"
        ),
    )

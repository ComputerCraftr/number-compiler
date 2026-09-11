"""Sparse candidate quotients and minimal Fermat/Mersenne terminal thresholds."""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd

from devtools.experiments.algebra.dyadic_difference_germ_core import (
    AmbientCapacityUnavailable,
)
from devtools.experiments.algebra.dyadic_difference_germ_norm import (
    fermat_first_lift_norm_audit,
)
from devtools.experiments.algebra.dyadic_difference_germ_tower import (
    fermat_fixed_trace_norm_shortcut,
)
from number_compiler.sequences.power_numbers.numbers import (
    fermat_number,
    mersenne_number,
)
from number_compiler.sequences.power_numbers.terminal_threshold import (
    mersenne_terminal_threshold_spec,
    terminal_threshold_spec,
)
from number_compiler.sequences.prime.set import smallest_factor

# ---------------------------------------------------------------------------
# Sparse quotient / minimum-threshold audit after the norm-recurrence attack.
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class FermatSparseCandidateQuotientAudit:
    """Exact identification of the sparse cyclotomic quotient with Z/F_n Z.

    Put ``m=2^(n+1)``, ``d=phi(m)=2^n`` and ``z=zeta_m``.  The terminal
    sparse principal element is ``beta=1-2z``.  Evaluation ``z -> 2^-1``
    defines a surjection

        Z[z]/(Phi_m(z), 1-2z) -> Z/F_n Z.

    The resultant is ``|Res(Phi_m,1-2x)| = Phi_m(2) = F_n``.  Since the
    source quotient has exactly that additive order, the map is an
    isomorphism.  This is a candidate-ring identification, not a splitting
    decision in the next Kummer layer.
    """

    parameter: int
    cyclotomic_order: int
    cyclotomic_degree: int
    candidate_modulus: int
    zeta_image: int
    linear_relation_residue: int
    cyclotomic_relation_residue: int
    resultant: int
    quotient_cardinality: int
    constants_surjective: bool
    candidate_derived: bool = True

    @property
    def exact(self) -> bool:
        return (
            self.linear_relation_residue == 0
            and self.cyclotomic_relation_residue == 0
            and self.resultant == self.candidate_modulus
            and self.quotient_cardinality == self.candidate_modulus
            and self.constants_surjective
        )


@dataclass(frozen=True, slots=True)
class FermatSparseKummerBaseChangeAudit:
    """Base-change the next Kummer algebra directly to the candidate ring.

    The embedded zeta_8 is ``zeta_(2^(n+1))^(2^(n-2))``.  Under the sparse
    quotient it maps to ``t^-1``.  Hence ``sqrt(2)=zeta_8-zeta_8^3`` maps to
    the independently constructed canonical first transverse root
    ``r1=t+t^-1``.  The next lift is therefore exactly the candidate-ring
    etale algebra ``R[y]/(y^2-r1)``.

    Ordinary module rank remains two whether this algebra splits or not; the
    missing datum is the local Frobenius/Artin action ``y -> +/- y``.
    """

    parameter: int
    candidate_modulus: int
    terminal_cyclotomic_order: int
    terminal_zeta_image: int
    zeta8_exponent: int
    zeta8_image: int
    sqrt2_image: int
    canonical_first_root: int
    kummer_discriminant: int
    discriminant_gcd: int
    module_rank: int
    desired_local_artin_action: str
    candidate_derived: bool = True
    factor_enumeration: int = 0
    root_branch_enumeration: int = 0

    @property
    def exact(self) -> bool:
        return (
            self.sqrt2_image == self.canonical_first_root
            and self.discriminant_gcd == 1
            and self.module_rank == 2
        )


@dataclass(frozen=True, slots=True)
class FermatFiltrationRequirementAudit:
    """How much of the hidden local-depth vector the Fermat certificate needs.

    For every prime divisor ``q | F_n`` one has ``ord_q(2)=2^(n+1)``.  If
    ``s_q=v2(q-1)-(n+1)``, the terminal pure-Fermat level is

        k* = 2^n - n - 1.

    ``s_q >= k*`` is equivalent to ``2^(2^n) | q-1``.  The least positive
    integer congruent to one modulo this power is ``F_n`` itself.  Therefore
    an all-local PASS at this *single* threshold forces every prime divisor to
    equal ``F_n`` and hence proves primality.  Conversely a prime ``F_n``
    plainly passes because ``v2(F_n-1)=2^n``.

    Thus the full histogram ``c_k`` is not needed for the Fermat prime bit or
    for the pure filtration after PASS: the closed pure theorem reconstructs
    the latter.  A failed Boolean threshold does *not* reconstruct the exact
    composite stable residual, so that stronger diagnostic remains a separate
    problem.
    """

    parameter: int
    width: int
    baseline_order_v2: int
    terminal_level: int
    required_local_v2: int
    candidate_modulus: int
    least_possible_passing_prime: int
    terminal_pass_iff_prime: bool
    full_histogram_required_for_prime_decision: bool
    full_histogram_required_for_pure_reconstruction_after_pass: bool
    full_histogram_required_for_exact_composite_residual: bool
    bounded_reference_matches_pure_theorem: bool | None


@dataclass(frozen=True, slots=True)
class MersenneSparseCandidateQuotientAudit:
    """Exact sparse cyclotomic quotient for a prime Mersenne exponent.

    For prime ``p``, ``Phi_p(2)=2^p-1=M_p``.  Evaluation ``zeta_p -> 2``
    therefore identifies

        Z[zeta_p] / (2-zeta_p)  ~=  Z/M_p Z.

    As in the Fermat sparse quotient, this removes representation ambiguity but
    does not decide the dyadic torus/Kummer support above the candidate ring.
    """

    exponent: int
    cyclotomic_order: int
    cyclotomic_degree: int
    candidate_modulus: int
    zeta_image: int
    linear_relation_residue: int
    cyclotomic_relation_residue: int
    resultant: int
    quotient_cardinality: int
    constants_surjective: bool
    candidate_derived: bool = True

    @property
    def exact(self) -> bool:
        return (
            self.linear_relation_residue == 0
            and self.cyclotomic_relation_residue == 0
            and self.resultant == self.candidate_modulus
            and self.quotient_cardinality == self.candidate_modulus
            and self.constants_surjective
        )


@dataclass(frozen=True, slots=True)
class MersenneSparseTorusBaseChangeAudit:
    """Attach the Lucas--Lehmer norm-one torus to the sparse candidate quotient.

    In ``R[s]/(s^2-3)`` the canonical element ``y0=2+s`` has norm one and
    trace four.  The LL recurrence is the trace of repeated squaring of ``y0``.
    The terminal prime-style condition is exact order ``2^p``; replacing local
    q-Frobenius by the candidate exponent gives ``M_p == -1 mod 2^p`` and hence
    only the predetermined inversion action, so it is not a support selector.
    """

    exponent: int
    candidate_modulus: int
    zeta_image: int
    torus_trace: int
    torus_norm: int
    formal_terminal_order: int
    candidate_exponent_residue: int
    candidate_action: str
    terminal_level: int
    candidate_derived: bool = True
    factor_enumeration: int = 0
    root_branch_enumeration: int = 0

    @property
    def exact(self) -> bool:
        return (
            self.torus_trace == 4
            and self.torus_norm == 1
            and self.candidate_exponent_residue == self.formal_terminal_order - 1
            and self.candidate_action == "inversion"
            and self.terminal_level == self.exponent - 2
        )


@dataclass(frozen=True, slots=True)
class MersenneFiltrationRequirementAudit:
    """Minimal all-local torus threshold needed for Mersenne primality.

    For a prime divisor ``q | M_p`` the reverse Lucas--Lehmer terminal phase
    has order four in the local torus of order ``q-(12/q)``.  If

        s_q = max(0, v2(q-(12/q)) - 2),

    then the single terminal threshold is ``k*=p-2``.  Passing it gives
    ``2^p | q-(12/q)``.  The ``+1`` character branch would imply
    ``q >= 2^p+1 > M_p`` and is impossible; the ``-1`` branch gives
    ``q >= 2^p-1=M_p``.  Since ``q`` divides the candidate, all-local PASS
    forces ``q=M_p`` and hence primality.

    Thus, exactly as for Fermat, the complete local-depth histogram is not
    required for the prime/composite bit or for the pure filtration after a
    terminal PASS.  It remains necessary only for an exact composite stable
    residual descriptor.
    """

    exponent: int
    terminal_level: int
    baseline_order_v2: int
    required_local_v2: int
    candidate_modulus: int
    plus_branch_least_prime: int
    minus_branch_least_prime: int
    terminal_pass_iff_prime: bool
    full_histogram_required_for_prime_decision: bool
    full_histogram_required_for_pure_reconstruction_after_pass: bool
    full_histogram_required_for_exact_composite_residual: bool
    bounded_reference_status: str | None
    bounded_reference_matches_pure_theorem: bool | None


@dataclass(frozen=True, slots=True)
class MersenneKummerThresholdProbe:
    """Fail-closed torus terminal-threshold query surface.

    No higher local Artin selector is currently known scalably.  This object
    exists to freeze the exact target and prevent bounded carrier or LL replay
    from being relabeled as a terminal Kummer decision.
    """

    exponent: int
    level: int
    candidate_modulus: int
    status: str
    method: str
    gcd_packet: int | None = None
    candidate_derived: bool = True
    factor_enumeration: int = 0
    root_branch_enumeration: int = 0
    raw_lucas_lehmer_steps: int = 0

    def __post_init__(self) -> None:
        if self.status not in ("ALL_PASS", "ALL_FAIL", "SPLIT", "UNKNOWN"):
            raise ValueError(self.status)
        if self.status == "SPLIT":
            if self.gcd_packet is None or not (
                1 < self.gcd_packet < self.candidate_modulus
            ):
                raise ValueError((self.status, self.gcd_packet, self.candidate_modulus))
        elif self.gcd_packet is not None:
            raise ValueError((self.status, self.gcd_packet))
        if self.raw_lucas_lehmer_steps:
            raise ValueError("threshold probe cannot replay Lucas--Lehmer")

    @property
    def decided(self) -> bool:
        return self.status != "UNKNOWN"

    @property
    def all_pass(self) -> bool:
        return self.status == "ALL_PASS"


@dataclass(frozen=True, slots=True)
class FermatKummerThresholdProbe:
    """Fail-closed candidate-only all-local threshold probe.

    Status is one of ``ALL_PASS``, ``ALL_FAIL``, ``SPLIT`` or ``UNKNOWN``.
    ``ALL_PASS`` requires an explicit global root/preimage witness, which is
    automatically valid in every CRT component.  ``SPLIT`` is reserved for a
    nontrivial gcd emitted naturally by a reduction.  No current path emits
    ``ALL_FAIL``: a bounded/section miss is never promoted to a negative
    certificate.
    """

    parameter: int
    level: int
    candidate_modulus: int
    status: str
    method: str
    root_witness: int | None = None
    witness_power_residue: int | None = None
    gcd_packet: int | None = None
    candidate_derived: bool = True
    factor_enumeration: int = 0
    root_branch_enumeration: int = 0

    def __post_init__(self) -> None:
        if self.status not in ("ALL_PASS", "ALL_FAIL", "SPLIT", "UNKNOWN"):
            raise ValueError(self.status)
        if self.status == "SPLIT":
            if self.gcd_packet is None or not (
                1 < self.gcd_packet < self.candidate_modulus
            ):
                raise ValueError((self.status, self.gcd_packet, self.candidate_modulus))
        elif self.gcd_packet is not None:
            raise ValueError((self.status, self.gcd_packet))

    @property
    def decided(self) -> bool:
        return self.status != "UNKNOWN"

    @property
    def all_pass(self) -> bool:
        return self.status == "ALL_PASS"


@dataclass(frozen=True, slots=True)
class FermatCandidateArtinGuard:
    """Direct candidate-ring Kummer/Frobenius attempt and its rejection guard.

    In ``R[y]/(y^2-r1)``, a true local q-Frobenius sends ``y`` to ``+y`` on a
    split component and ``-y`` on a nonsplit component.  Replacing that local
    exponent by the global candidate exponent sends

        y^N = y * r1^((N-1)/2).

    But ``r1`` has the already-known order ``2^(n+2)`` and
    ``F_n == 1 (mod 2^(n+2))``, so the multiplier is identically ``+1`` in the
    formal algebra.  This is an exact candidate-ring construction but remains
    blind to ambient extension capacity; it must never be reported as Artin
    extraction.
    """

    parameter: int
    candidate_modulus: int
    current_root: int
    formal_root_order: int
    candidate_exponent_residue: int
    global_multiplier: int
    gcd_plus: int
    gcd_minus: int
    selective: bool
    accepted_as_local_artin: bool = False
    candidate_derived: bool = True


def fermat_sparse_candidate_quotient_audit(
    parameter: int,
) -> FermatSparseCandidateQuotientAudit:
    n = int(parameter)
    if n < 2:
        raise ValueError(n)
    degree = 1 << n
    order = 1 << (n + 1)
    modulus = fermat_number(n)
    zeta_image = pow(2, -1, modulus)
    linear = (1 - 2 * zeta_image) % modulus
    # Phi_(2^(n+1))(x) = x^(2^n) + 1.
    cyclotomic = (pow(zeta_image, degree, modulus) + 1) % modulus
    resultant = (1 << degree) + 1
    return FermatSparseCandidateQuotientAudit(
        n,
        order,
        degree,
        modulus,
        zeta_image,
        linear,
        cyclotomic,
        resultant,
        resultant,
        True,
    )


def fermat_sparse_kummer_base_change_audit(
    parameter: int,
) -> FermatSparseKummerBaseChangeAudit:
    n = int(parameter)
    quotient = fermat_sparse_candidate_quotient_audit(n)
    modulus = quotient.candidate_modulus
    exponent = 1 << (n - 2)
    zeta8 = pow(quotient.zeta_image, exponent, modulus)
    sqrt2 = (zeta8 - pow(zeta8, 3, modulus)) % modulus
    first = fermat_first_lift_norm_audit(n)
    discriminant = (4 * sqrt2) % modulus
    return FermatSparseKummerBaseChangeAudit(
        n,
        modulus,
        quotient.cyclotomic_order,
        quotient.zeta_image,
        exponent,
        zeta8,
        sqrt2,
        first.canonical_root,
        discriminant,
        gcd(discriminant, modulus),
        2,
        "local Frobenius: y -> +y iff split, y -> -y iff nonsplit",
    )


def fermat_filtration_requirement_audit(
    parameter: int,
) -> FermatFiltrationRequirementAudit:
    n = int(parameter)
    if n < 2:
        raise ValueError(n)
    width = 1 << n
    baseline = n + 1
    terminal = width - baseline
    required = baseline + terminal
    modulus = fermat_number(n)
    least = (1 << required) + 1
    if required != width or least != modulus:
        raise AssertionError((n, width, required, least, modulus))

    bounded_match: bool | None = None
    # The existing bounded carrier gate reaches Fermat widths through 16.  Use
    # it only as a differential check that a terminal PASS may hand off to the
    # closed theorem; it is not part of the threshold proof.
    if width <= 16:
        from devtools.proofs.oracles.bounded_filtration import (
            bounded_candidate_image_filtration,
        )
        from number_compiler.arithmetic.polynomials.two_primary_filtration import (
            pure_two_primary_image_filtration,
        )

        bounded = bounded_candidate_image_filtration("fermat", n, max_fermat_width=16)
        pure = pure_two_primary_image_filtration("fermat", n)
        bounded_match = bool(
            bounded.pure_two_primary_shape
            and bounded.image_ranks == pure.image_ranks
            and bounded.depth_strata == pure.depth_strata
            and bounded.target_image_depths == pure.target_image_depths
        )

    return FermatFiltrationRequirementAudit(
        n,
        width,
        baseline,
        terminal,
        required,
        modulus,
        least,
        True,
        False,
        False,
        True,
        bounded_match,
    )


def mersenne_sparse_candidate_quotient_audit(
    exponent: int,
) -> MersenneSparseCandidateQuotientAudit:
    p = int(exponent)
    if p < 3 or not (p & 1):
        raise ValueError(p)
    # This quotient formula is the prime-exponent branch.  The production
    # compiler rejects composite exponents before the Mersenne number-level
    # certificate.  In research, fail closed if p itself is composite.
    if smallest_factor(p) is not None:
        raise ValueError((p, "prime exponent required"))
    modulus = mersenne_number(p)
    zeta_image = 2 % modulus
    linear = (2 - zeta_image) % modulus
    # Phi_p(2)=1+2+...+2^(p-1)=2^p-1 for prime p.
    cyclotomic_value = (1 << p) - 1
    cyclotomic = cyclotomic_value % modulus
    return MersenneSparseCandidateQuotientAudit(
        p,
        p,
        p - 1,
        modulus,
        zeta_image,
        linear,
        cyclotomic,
        cyclotomic_value,
        cyclotomic_value,
        True,
    )


def mersenne_sparse_torus_base_change_audit(
    exponent: int,
) -> MersenneSparseTorusBaseChangeAudit:
    p = int(exponent)
    quotient = mersenne_sparse_candidate_quotient_audit(p)
    order = 1 << p
    residue = quotient.candidate_modulus % order
    return MersenneSparseTorusBaseChangeAudit(
        p,
        quotient.candidate_modulus,
        quotient.zeta_image,
        4,
        1,
        order,
        residue,
        "inversion",
        p - 2,
    )


def mersenne_filtration_requirement_audit(
    exponent: int,
) -> MersenneFiltrationRequirementAudit:
    p = int(exponent)
    if p < 3 or not (p & 1):
        raise ValueError(p)
    spec = mersenne_terminal_threshold_spec(p)
    modulus = mersenne_number(p)
    plus_least = (1 << p) + 1
    minus_least = (1 << p) - 1
    if spec.terminal_level != p - 2 or spec.required_local_v2 != p:
        raise AssertionError((p, spec))
    if plus_least <= modulus or minus_least != modulus:
        raise AssertionError((p, plus_least, minus_least, modulus))

    bounded_status: str | None = None
    bounded_match: bool | None = None
    if p <= 13:
        from devtools.proofs.oracles.bounded_filtration import (
            bounded_candidate_image_filtration,
        )
        from number_compiler.arithmetic.polynomials.two_primary_filtration import (
            pure_two_primary_image_filtration,
        )

        bounded = bounded_candidate_image_filtration(
            "mersenne",
            p,
            max_mersenne_exponent=13,
        )
        bounded_status = bounded.status
        if bounded.pure_two_primary_shape:
            pure = pure_two_primary_image_filtration("mersenne", p)
            bounded_match = bool(
                bounded.image_ranks == pure.image_ranks
                and bounded.depth_strata == pure.depth_strata
                and bounded.target_image_depths == pure.target_image_depths
            )
        else:
            bounded_match = None

    return MersenneFiltrationRequirementAudit(
        p,
        spec.terminal_level,
        spec.baseline_local_v2,
        spec.required_local_v2,
        modulus,
        plus_least,
        minus_least,
        True,
        False,
        False,
        True,
        bounded_status,
        bounded_match,
    )


def mersenne_kummer_threshold_probe(
    exponent: int, level: int
) -> MersenneKummerThresholdProbe:
    p = int(exponent)
    level = int(level)
    if p < 3 or not (p & 1) or level < 1:
        raise ValueError((p, level))
    modulus = mersenne_number(p)
    return MersenneKummerThresholdProbe(
        p,
        level,
        modulus,
        "UNKNOWN",
        "higher-torus-kummer-artin-selector-unavailable",
    )


def mersenne_terminal_threshold_probe(exponent: int) -> MersenneKummerThresholdProbe:
    audit = mersenne_filtration_requirement_audit(exponent)
    return mersenne_kummer_threshold_probe(audit.exponent, audit.terminal_level)


def special_terminal_threshold_audit(
    family: str, parameter: int
) -> FermatFiltrationRequirementAudit | MersenneFiltrationRequirementAudit:
    """Common theorem descriptor used by the release integration audit."""
    spec = terminal_threshold_spec(family, parameter)
    if spec.family == "fermat":
        return fermat_filtration_requirement_audit(spec.parameter)
    return mersenne_filtration_requirement_audit(spec.parameter)


def fermat_candidate_artin_guard(parameter: int) -> FermatCandidateArtinGuard:
    n = int(parameter)
    if n < 2:
        raise ValueError(n)
    first = fermat_first_lift_norm_audit(n)
    modulus = first.modulus
    order = 1 << (n + 2)
    residue = modulus % order
    # Because r1 has order dividing 2^(n+2) and N == 1 mod that order, the
    # global N-Frobenius multiplier is formally +1.  Compute it once as an
    # executable guard against accidental changes in the normalization.
    multiplier = pow(first.canonical_root, (modulus - 1) // 2, modulus)
    plus = gcd(multiplier - 1, modulus)
    minus = gcd(multiplier + 1, modulus)
    selective = (1 < plus < modulus) or (1 < minus < modulus)
    return FermatCandidateArtinGuard(
        n,
        modulus,
        first.canonical_root,
        order,
        residue,
        multiplier,
        plus,
        minus,
        selective,
    )


def fermat_kummer_threshold_probe(
    parameter: int, level: int
) -> FermatKummerThresholdProbe:
    """Candidate-only threshold probe with exact positive witnesses where known."""
    n = int(parameter)
    level = int(level)
    if n < 2 or level < 1:
        raise ValueError((n, level))
    modulus = fermat_number(n)

    if level == 1:
        first = fermat_first_lift_norm_audit(n)
        witness = first.canonical_root
        residue = pow(witness, 2, modulus)
        if residue != 2 % modulus:
            raise AssertionError((n, level, witness, residue))
        return FermatKummerThresholdProbe(
            n,
            level,
            modulus,
            "ALL_PASS",
            "explicit-first-transverse-root",
            witness,
            residue,
        )

    if level == 2:
        shortcut = fermat_fixed_trace_norm_shortcut(n)
        if shortcut.exact and shortcut.modular_fourth_root is not None:
            witness = shortcut.modular_fourth_root
            residue = pow(witness, 1 << level, modulus)
            if residue != 2 % modulus:
                raise AssertionError((n, level, witness, residue))
            return FermatKummerThresholdProbe(
                n,
                level,
                modulus,
                "ALL_PASS",
                "fixed-trace-relative-norm-witness",
                witness,
                residue,
            )
        return FermatKummerThresholdProbe(
            n,
            level,
            modulus,
            "UNKNOWN",
            "fixed-trace-section-miss-not-negative",
        )

    return FermatKummerThresholdProbe(
        n,
        level,
        modulus,
        "UNKNOWN",
        "higher-kummer-support-selector-unavailable",
    )


def fermat_terminal_threshold_probe(parameter: int) -> FermatKummerThresholdProbe:
    audit = fermat_filtration_requirement_audit(parameter)
    return fermat_kummer_threshold_probe(audit.parameter, audit.terminal_level)


def candidate_derived_splitting_weight(family: str, parameter: int, level: int) -> int:
    """Fail closed until a genuinely selective candidate-ring evaluator exists."""
    raise AmbientCapacityUnavailable((str(family), int(parameter), int(level)))

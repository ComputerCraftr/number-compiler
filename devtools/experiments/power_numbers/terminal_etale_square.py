"""Minimal terminal quadratic-etale split-bit research for Fermat/Mersenne.

This module deliberately narrows the v0.51 theorem target.  The prime release
needs one Boolean all-local split predicate, not the complete local-support
histogram and not a regular-Artin/Dedekind-zeta coefficient.

All functions labelled ``truth`` use bounded factor truth only as an audit
label.  Candidate-derived guards never factor the candidate and never replay
Pepin/Lucas--Lehmer.
"""

from __future__ import annotations

from dataclasses import dataclass
from number_compiler.sequences.power_numbers.etale_factor import (
    MersenneAdditiveEtaleFrobeniusProbe as MersenneAdditiveEtaleFrobeniusProbe,
    FermatAdditiveEtaleFrobeniusProbe as FermatAdditiveEtaleFrobeniusProbe,
    mersenne_additive_etale_frobenius_probe as mersenne_additive_etale_frobenius_probe,
    fermat_additive_etale_frobenius_probe as fermat_additive_etale_frobenius_probe,
)

from math import prod

from devtools.experiments.algebra.dyadic_difference_germ_core import (
    ambient_capacity_truth,
    formal_phase_frobenius_audit,
)
from number_compiler.sequences.power_numbers.numbers import (
    fermat_number,
    mersenne_number,
)
from number_compiler.projection.output_quotient import SpecialSourceShape
from number_compiler.sequences.power_numbers.germ import (
    SpecialGermTransfer,
    build_special_germ_plan,
)
from number_compiler.sequences.power_numbers.terminal_threshold import (
    prime_decision_chunk_spec,
    terminal_threshold_probe,
    terminal_threshold_spec,
)


@dataclass(frozen=True, slots=True)
class EtaleSquareBitTruthAudit:
    """The actual Boolean required by one Kummer/half-root layer.

    ``local_square_bits`` records whether the canonical current radicand has a
    square root in each local component.  The desired candidate-ring answer is
    their Boolean AND.  ``product_sign`` is the corresponding +/-1 product and
    is retained only to freeze the cancellation counterexample: it is *not*
    the required semantic object.
    """

    family: str
    parameter: int
    level: int
    candidate_modulus: int
    local_square_bits: tuple[bool, ...]
    all_local_square: bool
    product_sign: int
    product_sign_decides_all_local: bool
    factor_truth_only: bool = True


@dataclass(frozen=True, slots=True)
class BitNotSuccessorClosedAudit:
    """Counterexample to treating the one split bit as the powered state."""

    left_family: str
    left_parameter: int
    right_family: str
    right_parameter: int
    common_level: int
    left_current_bit: bool
    right_current_bit: bool
    left_next_bit: bool
    right_next_bit: bool
    same_current_bit: bool
    different_next_bit: bool
    conclusion: str


@dataclass(frozen=True, slots=True)
class FermatTerminalRootTorsorAudit:
    """Direct, root-free description of the Fermat terminal certificate.

    Let T=2^n and k*=T-n-1.  The terminal Boolean is simply whether

        X^(2^k*) = 2

    has a solution in R=Z/F_n Z.  Any solution has exact order 2^T=F_n-1,
    which itself forces F_n to be prime.  Conversely a prime F_n has the
    required 2-primary capacity.

    In the formal torsor B=R[X]/(X^(2^k*)-2), however, the candidate-global
    N-power map is identically X -> X because

        X^(2^T) = 2^(2^(n+1)) = (2^T)^2 = 1 mod F_n.

    Thus the usual X^N-X Frobenius split test is a *special-form identity* on
    every Fermat candidate and cannot evaluate the bit.
    """

    parameter: int
    candidate_modulus: int
    T: int
    terminal_level: int
    torsor_exponent_log2: int
    terminal_root_order: int
    terminal_root_would_be_maximal_order_unit: bool
    terminal_root_exists_iff_prime: bool
    global_candidate_frobenius_remainder: str
    global_frobenius_is_formally_identity: bool
    raw_power_evaluation_required_by_this_audit: bool = False
    candidate_derived: bool = True


@dataclass(frozen=True, slots=True)
class MersenneTerminalTorusBitAudit:
    """Minimal Mersenne terminal bit and the formally blind global action."""

    exponent: int
    candidate_modulus: int
    terminal_level: int
    formal_torus_order: int
    terminal_split_iff_prime: bool
    candidate_exponent_residue: int
    global_candidate_action: str
    global_action_is_formally_predetermined: bool
    raw_lucas_lehmer_steps: int = 0
    candidate_derived: bool = True


@dataclass(frozen=True, slots=True)
class MinimalEtaleSelectorTarget:
    """Release theorem contract after discarding the overstrong support target."""

    family: str
    parameter: int
    terminal_level: int
    semantic_query: str
    output_bits: int
    full_support_required: bool
    splitting_weight_required: bool
    euler_coefficient_required: bool
    generic_higher_residue_hardness_claimed: bool
    factor_free_evaluator_available: bool
    production_status: str


@dataclass(frozen=True, slots=True)
class SpecialEtaleTileApplicabilityAudit:
    """Exact boundary between reusable tile structure and the missing theorem.

    Fermat and Mersenne source geometry fixes a negacyclic or cyclic boundary,
    and the existing germ composes its angular transport without publishing a
    state for every lift level.  The terminal etale selector is an output port,
    not part of that action identity.  Promotion to the shared tile runtime is
    still unsafe while the candidate-derived selector is unavailable.
    """

    family: str
    parameter: int
    closure: str
    boundary_sign: int
    geometry_key: tuple[object, ...]
    angular_action_key: tuple[object, ...]
    selector_port_key: tuple[object, ...]
    powered_span: int
    binary_compositions: int
    per_level_states_retained: int
    exact_source_digits_retained: int
    selector_in_action_identity: bool
    selector_value: bool | None
    candidate_selector_available: bool
    certified_tile_family: bool
    scheduler_promotion_safe: bool
    production_status: str


@dataclass(frozen=True, slots=True)
class FormalExpressionCannotSeeFieldOfDefinitionAudit:
    """Freeze the semantic boundary of the quadratic etale query.

    Split and nonsplit fibres both contain a universal ``y`` satisfying the
    same relation ``y^2=d`` in an algebraic closure.  Consequently every fixed
    polynomial/rational identity derived only from that relation has identical
    formal truth on the two fibres.  The missing bit is *field of definition*:
    whether one of the two roots is already in the base ring.
    """

    relation: str
    split_universal_relation: str
    nonsplit_universal_relation: str
    same_formal_algebraic_identities: bool
    missing_property: str
    conclusion: str


@dataclass(frozen=True, slots=True)
class FermatPrimePhaseCompressionAudit:
    """Bounded prime-side compression of the terminal root to n+1 phase bits.

    Under the *independently audited prime premise*, Pepin's base 3 has exact
    order 2^T, T=2^n.  Since 2 has order 2^(n+1), its discrete-log exponent
    relative to 3 is 2^k* times an odd residue e modulo 2^(n+1).  The terminal
    root is therefore simply 3^e.  This demonstrates compact witness/state
    size after purity is known; finding e without the deep power is still the
    extraction problem and is not solved here.
    """

    parameter: int
    candidate_modulus: int
    terminal_level: int
    phase_modulus: int
    odd_phase: int
    terminal_root: int
    terminal_root_power_residue: int
    retained_phase_bits: int
    raw_deep_power_used_for_audit: bool
    prime_assumption_only: bool = True


@dataclass(frozen=True, slots=True)
class FermatPureOrderLayerAudit:
    """Why powers of the universal quadratic generator cannot see splitting.

    Suppose the current radicand ``d`` has exact local order 2^h.  In
    A=F_q[y]/(y^2-d), the universal ``y`` has exact order 2^(h+1) whether A is
    split (F_q x F_q) or nonsplit (F_q^2).  Splitting is only the assertion
    that an element with this order already exists in the base field, i.e.
    v2(q-1)>=h+1.  Any computation using only the formal relation y^2=d and
    powers of y therefore has the same result on both sides.
    """

    parameter: int
    level_being_tested: int
    current_order_log2: int
    universal_root_order_log2: int
    split_requires_local_v2: int
    split_universal_root_order: int
    nonsplit_universal_root_order: int
    same_formal_order: bool
    conclusion: str


def etale_square_bit_truth_audit(
    family: str, parameter: int, level: int
) -> EtaleSquareBitTruthAudit:
    family = str(family)
    parameter = int(parameter)
    level = int(level)
    if level < 1:
        raise ValueError(level)
    truth = ambient_capacity_truth(family, parameter)
    bits = tuple(depth >= level for depth in truth.local_lift_depths)
    sign = prod(1 if bit else -1 for bit in bits)
    all_local = all(bits)
    # The +/-1 product can equal +1 both for all-pass and for an even packet
    # of failures.  Record whether it happens to decide this audit row, while
    # never promoting that accidental agreement to a theorem.
    product_decides = (sign == 1) == all_local
    return EtaleSquareBitTruthAudit(
        family,
        parameter,
        level,
        truth.modulus,
        bits,
        all_local,
        sign,
        product_decides,
    )


def bit_not_successor_closed_audit() -> BitNotSuccessorClosedAudit:
    """Freeze the F4/F5 first-layer counterexample.

    Both candidates admit the guaranteed first square root of 2, but only F4
    admits the next square root.  Therefore ``split?`` is the correct query but
    cannot itself be the state of a successor automaton.
    """
    f4_now = etale_square_bit_truth_audit("fermat", 4, 1)
    f5_now = etale_square_bit_truth_audit("fermat", 5, 1)
    f4_next = etale_square_bit_truth_audit("fermat", 4, 2)
    f5_next = etale_square_bit_truth_audit("fermat", 5, 2)
    return BitNotSuccessorClosedAudit(
        "fermat",
        4,
        "fermat",
        5,
        1,
        f4_now.all_local_square,
        f5_now.all_local_square,
        f4_next.all_local_square,
        f5_next.all_local_square,
        f4_now.all_local_square == f5_now.all_local_square,
        f4_next.all_local_square != f5_next.all_local_square,
        "one etale split bit is the output query, not a successor-closed powered state",
    )


def fermat_terminal_root_torsor_audit(parameter: int) -> FermatTerminalRootTorsorAudit:
    n = int(parameter)
    if n < 2:
        raise ValueError(n)
    T = 1 << n
    spec = terminal_threshold_spec("fermat", n)
    k = spec.terminal_level
    N = fermat_number(n)
    if k != T - n - 1:
        raise AssertionError((n, k, T))

    # A terminal root x satisfies x^(2^k)=2.  Since 2 has exact order
    # 2^(n+1) modulo every prime divisor of F_n, such an x has exact order
    # 2^(n+1+k)=2^T=N-1 in every local component.  Existence therefore forces
    # every prime divisor to have q-1 >= N-1 and hence q=N.
    terminal_order = 1 << T
    if (n + 1 + k) != T or terminal_order != N - 1:
        raise AssertionError((n, k, terminal_order, N))

    # In B=R[X]/(X^(2^k)-2), repeatedly applying the defining relation gives
    # X^(2^T) = 2^(2^(T-k)) = 2^(2^(n+1)).  But 2^T=-1 mod F_n, so this is 1.
    # Hence X^N-X=0 identically in B.  This uses exponent identities only; no
    # degree-2^k polynomial or raw squaring trajectory is materialized.
    if T - k != n + 1:
        raise AssertionError((T, k, n))
    two_power_residue = pow(2, 1 << (n + 1), N)
    if two_power_residue != 1:
        raise AssertionError((n, two_power_residue))
    return FermatTerminalRootTorsorAudit(
        n,
        N,
        T,
        k,
        k,
        terminal_order,
        True,
        True,
        "X^N-X == 0 in R[X]/(X^(2^k*)-2)",
        True,
    )


def mersenne_terminal_torus_bit_audit(exponent: int) -> MersenneTerminalTorusBitAudit:
    p = int(exponent)
    if p < 3 or not (p & 1):
        raise ValueError(p)
    spec = terminal_threshold_spec("mersenne", p)
    N = mersenne_number(p)
    order = 1 << p
    residue = N % order
    formal = formal_phase_frobenius_audit("mersenne", p, spec.terminal_level)
    if residue != order - 1 or formal.canonical_action != "inversion":
        raise AssertionError((p, residue, formal))
    return MersenneTerminalTorusBitAudit(
        p,
        N,
        spec.terminal_level,
        order,
        True,
        residue,
        "inversion",
        True,
    )


def fermat_pure_order_layer_audit(
    parameter: int, level_being_tested: int
) -> FermatPureOrderLayerAudit:
    n = int(parameter)
    level = int(level_being_tested)
    if n < 2 or level < 1:
        raise ValueError((n, level))
    # Before testing level L, a successful level-(L-1) root has order
    # 2^(n+L).  The universal square root in the rank-two algebra has one more
    # factor of two in its exact order regardless of split/nonsplit status.
    current_h = n + level
    universal_h = current_h + 1
    return FermatPureOrderLayerAudit(
        n,
        level,
        current_h,
        universal_h,
        universal_h,
        1 << universal_h,
        1 << universal_h,
        True,
        "formal powers of the universal root are split-blind; only base-ring membership is missing",
    )


def formal_expression_cannot_see_field_of_definition_audit() -> (
    FormalExpressionCannotSeeFieldOfDefinitionAudit
):
    return FormalExpressionCannotSeeFieldOfDefinitionAudit(
        "y^2=d",
        "the universal root satisfies y^2=d in the split algebra",
        "the universal root satisfies y^2=d in the quadratic field fibre",
        True,
        "existence of an R-valued root / nontrivial idempotent",
        "the etale split bit needs base-ring arithmetic; formal Kummer identities alone are necessarily blind",
    )


def fermat_prime_phase_compression_audit(
    parameter: int,
) -> FermatPrimePhaseCompressionAudit:
    """Bounded audit of the n+1-bit odd terminal phase for F2/F3/F4."""
    n = int(parameter)
    if n not in (2, 3, 4):
        raise ValueError((n, "bounded independently-prime controls only"))
    row = fermat_terminal_root_torsor_audit(n)
    N = row.candidate_modulus
    k = row.terminal_level
    phase_modulus = 1 << (n + 1)

    # This bounded audit intentionally performs the old deep exponent once to
    # expose the compact prime-side phase.  It is research/oracle evidence only
    # and is never imported by production.
    generator_at_baseline = pow(3, 1 << k, N)
    phase = None
    value = 1
    for e in range(1, phase_modulus, 2):
        value = pow(generator_at_baseline, e, N)
        if value == 2 % N:
            phase = e
            break
    if phase is None:
        raise AssertionError((n, generator_at_baseline, phase_modulus))
    root = pow(3, phase, N)
    residue = pow(root, 1 << k, N)
    if residue != 2 % N:
        raise AssertionError((n, phase, root, residue))
    return FermatPrimePhaseCompressionAudit(
        n,
        N,
        k,
        phase_modulus,
        phase,
        root,
        residue,
        n + 1,
        True,
    )


def minimal_etale_selector_target(
    family: str, parameter: int
) -> MinimalEtaleSelectorTarget:
    spec = terminal_threshold_spec(str(family), int(parameter))
    if spec.family == "fermat":
        query = (
            f"exists x in Z/F_{spec.parameter}Z with x^(2^{spec.terminal_level}) = 2"
        )
    else:
        query = (
            f"terminal Lucas--Lehmer 2-primary torus phase splits through "
            f"level {spec.terminal_level}"
        )
    return MinimalEtaleSelectorTarget(
        spec.family,
        spec.parameter,
        spec.terminal_level,
        query,
        1,
        False,
        False,
        False,
        False,
        False,
        "UNKNOWN",
    )


def special_etale_tile_applicability_audit(
    family: str, parameter: int
) -> SpecialEtaleTileApplicabilityAudit:
    """Describe the sound scheduler handoff without manufacturing a prime bit.

    This audit deliberately uses the same geometry-first split as the decimal
    carry quotients: closure geometry chooses the cyclic law, then a powered
    value action is composed, and only the demanded output observes the etale
    selector.  It does not register a tile adapter; production admission is
    currently certified only for reverse-add and Collatz.
    """
    shape = SpecialSourceShape(str(family), int(parameter))
    threshold = terminal_threshold_spec(shape.family, shape.parameter)
    result = terminal_threshold_probe(shape.family, shape.parameter)
    selector = None
    if result.status == "ALL_PASS":
        selector = True
    elif result.status in ("ALL_FAIL", "SPLIT"):
        selector = False
    available = selector is not None
    if available:
        transfer = SpecialGermTransfer.identity(shape.family)
        start_level, span = result.level, 0
        compositions = 0
    else:
        chunk = prime_decision_chunk_spec(threshold)
        plan = build_special_germ_plan(chunk)
        transfer = plan.transfer
        start_level, span = chunk.start_level, chunk.span
        compositions = plan.binary_compositions
    closure = "negacyclic" if shape.boundary_sign == -1 else "cyclic"
    geometry_key = (
        "special-source-geometry",
        closure,
        shape.bit_length,
        shape.top_bit,
    )
    selector_key = (
        "special-etale-selector-port",
        shape.family,
        shape.parameter,
        start_level,
        span,
    )
    return SpecialEtaleTileApplicabilityAudit(
        shape.family,
        shape.parameter,
        closure,
        shape.boundary_sign,
        geometry_key,
        transfer.canonical_key,
        selector_key,
        span,
        compositions,
        0,
        0,
        False,
        selector,
        available,
        False,
        False,
        "RESEARCH_ONLY" if not available else "AWAITING_TILE_FAMILY_CERTIFICATE",
    )


__all__ = [name for name in globals() if not name.startswith("_")]

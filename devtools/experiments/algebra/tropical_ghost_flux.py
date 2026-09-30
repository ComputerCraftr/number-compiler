"""Tropical/divisor-lattice audit for the special-number ghost current.

The arithmetic-Stokes pass identified the exact defect current

    x_m = 1 + C*m,
    GhostFlux(a,l) = gcd(N, product x_m).

This module asks whether that current admits a genuinely smaller tropical
source evaluator.  Multiplicative/divisor semantics *do* tropicalize exactly:
for every hidden prime power q^e || N, the coordinate

    h_q(x) = min(e, v_q(x))

turns multiplication into saturated addition, gcd into componentwise minimum,
and lcm into componentwise maximum.  Factor-free, the whole valuation vector is
encoded by the divisor d=gcd(x,N), with saturated product

    d1 (*) d2 = gcd(N, d1*d2).

The decisive limitation is source detection.  At the special affine defect,
``1`` and ``C*m`` have equal q-valuation zero and the nonzero valuation of their
sum is created entirely by leading-residue cancellation.  Plain min-plus state
therefore predicts the same value on a regular slot and the singular slot.
Keeping the leading residue resolves the tie only after the hidden q-axis is
known.  Those axes are exactly the prime divisors of N.

The module also audits reversible sliding.  Saturated valuation state forgets
multiplicity after reaching the exponent of q in N, so exact deletion requires
either factor-indexed overflow counters or a factor-free lift to divisors of
N^r whose bit size grows linearly with the supported multiplicity horizon.

Factor-free divisor operations are owned by production; the audits here remain research-only.  Production must not import this module or
promote factor-backed tropical axes into the terminal source projector.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd

from devtools.experiments.algebra.arithmetic_ghost_flux import (
    arithmetic_ghost_flux_block,
)
from devtools.experiments.algebra.inputs import bounded_jet_spec
from devtools.experiments.power_numbers.special_transverse_jet import (
    SpecialJetProgressionSpec,
    first_special_transverse_singularity,
)
from number_compiler.arithmetic.fields.adic_morphism import ValuationSensitivityMorphism
from number_compiler.arithmetic.fields.radix import bit_width
from number_compiler.arithmetic.fields.tropical_divisor import (
    TropicalDivisorState,
)


def _vp(value: int, prime: int) -> int:
    value, prime = abs(int(value)), int(prime)
    if prime < 2:
        raise ValueError(prime)
    if value == 0:
        raise ValueError("unbounded valuation of zero is not used in this audit")
    out = 0
    while value % prime == 0:
        value //= prime
        out += 1
    return out


def _factor_multiplicities_truth(value: int) -> tuple[tuple[int, int], ...]:
    """Complete bounded factorization for research controls only."""
    n = int(value)
    if n < 2:
        raise ValueError(n)
    out: list[tuple[int, int]] = []
    q = 2
    while q * q <= n:
        if n % q:
            q = 3 if q == 2 else q + 2
            continue
        exponent = 0
        while n % q == 0:
            n //= q
            exponent += 1
        out.append((q, exponent))
        q = 3 if q == 2 else q + 2
    if n > 1:
        out.append((n, 1))
    return tuple(out)


@dataclass(frozen=True, slots=True)
class TropicalDivisorSemiringAudit:
    modulus: int
    factor_truth: tuple[tuple[int, int], ...]
    left_divisor: int
    right_divisor: int
    product_divisor: int
    meet_divisor: int
    join_divisor: int
    local_product_heights: tuple[tuple[int, int], ...]
    local_expected_heights: tuple[tuple[int, int], ...]
    saturated_multiplication_exact: bool
    meet_is_componentwise_min: bool
    join_is_componentwise_max: bool
    factor_free_operations: bool = True


def tropical_divisor_semiring_audit(
    modulus: int,
    left_divisor: int,
    right_divisor: int,
) -> TropicalDivisorSemiringAudit:
    modulus = int(modulus)
    factors = _factor_multiplicities_truth(modulus)
    left = TropicalDivisorState(modulus, int(left_divisor))
    right = TropicalDivisorState(modulus, int(right_divisor))
    product = left.multiply(right)
    meet = left.meet(right)
    join = left.join(right)
    got_product: list[tuple[int, int]] = []
    expected_product: list[tuple[int, int]] = []
    min_ok = max_ok = True
    for q, e in factors:
        lv = left.local_height(q, e)
        rv = right.local_height(q, e)
        pv = product.local_height(q, e)
        mv = meet.local_height(q, e)
        jv = join.local_height(q, e)
        got_product.append((q, pv))
        expected_product.append((q, min(e, lv + rv)))
        min_ok &= mv == min(lv, rv)
        max_ok &= jv == max(lv, rv)
    return TropicalDivisorSemiringAudit(
        modulus,
        factors,
        left.divisor,
        right.divisor,
        product.divisor,
        meet.divisor,
        join.divisor,
        tuple(got_product),
        tuple(expected_product),
        tuple(got_product) == tuple(expected_product),
        min_ok,
        max_ok,
    )


@dataclass(frozen=True, slots=True)
class TropicalBlockCompositionAudit:
    family: str
    parameter: int
    start: int
    span: int
    modulus: int
    tropical_divisor: int
    direct_flux_gcd: int
    exact: bool
    leaf_source_gcds: int
    semiring_compositions: int
    semiring_integer_multiplications: int
    semiring_combine_gcds: int
    direct_product_multiplications: int
    direct_final_gcds: int
    state_divisor_fields_per_node: int
    binary_parallel_depth: int
    state_constant_size: bool
    source_work_linear_in_span: bool
    asymptotic_source_work_improved: bool


def tropical_block_composition_audit(
    family: str,
    parameter: int,
    *,
    start: int,
    span: int,
) -> TropicalBlockCompositionAudit:
    """Compose exact divisor states through a balanced tree.

    The state at every node is one divisor, but every leaf still needs the
    source observation ``gcd(N,1+C*m)``.  Internal semiring multiplication also
    requires a saturated gcd.  This is therefore a state compression, not a
    source-work compression.
    """
    spec, start, span = bounded_jet_spec(family, parameter, start, span)
    level = [
        TropicalDivisorState.observe(spec.modulus, spec.slot_value(slot))
        for slot in range(start, start + span)
    ]
    compositions = depth = 0
    while len(level) > 1:
        nxt: list[TropicalDivisorState] = []
        for index in range(0, len(level), 2):
            if index + 1 == len(level):
                nxt.append(level[index])
            else:
                nxt.append(level[index].multiply(level[index + 1]))
                compositions += 1
        level = nxt
        depth += 1
    got = level[0].divisor
    direct = arithmetic_ghost_flux_block(
        family,
        parameter,
        start=start,
        span=span,
    )
    return TropicalBlockCompositionAudit(
        spec.family,
        spec.parameter,
        start,
        span,
        spec.modulus,
        got,
        direct.support_gcd,
        got == direct.support_gcd,
        span,
        compositions,
        compositions,
        compositions,
        direct.multiplications,
        1,
        1,
        depth,
        True,
        True,
        False,
    )


@dataclass(frozen=True, slots=True)
class TropicalTieCancellationAudit:
    family: str
    parameter: int
    hidden_factor: int
    regular_slot: int
    singular_slot: int
    regular_input_valuations: tuple[int, int]
    singular_input_valuations: tuple[int, int]
    plain_tropical_regular_sum: int
    plain_tropical_singular_sum: int
    actual_regular_sum_valuation: int
    actual_singular_sum_valuation: int
    singular_excess_valuation: int
    regular_leading_residues: tuple[int, int]
    singular_leading_residues: tuple[int, int]
    regular_residue_sum: int
    singular_residue_sum: int
    plain_tropical_signatures_equal: bool
    plain_tropical_detects_defect: bool
    supertropical_tie_marks_regular: bool
    supertropical_tie_marks_singular: bool
    supertropical_tie_distinguishes_defect: bool
    enriched_residue_phase_detects_defect: bool
    hidden_axis_required: bool = True


def tropical_tie_cancellation_audit(
    family: str,
    parameter: int,
) -> TropicalTieCancellationAudit:
    """Show that the ghost is equal-valuation cancellation, not min-plus depth."""
    singular = first_special_transverse_singularity(family, parameter)
    if (
        not singular.found
        or singular.first_slot is None
        or singular.denominator_gcd <= 1
    ):
        raise ValueError("composite singular control required")
    spec = SpecialJetProgressionSpec.build(family, parameter)
    q = singular.denominator_gcd
    bad = singular.first_slot
    candidates = [slot for slot in range(1, spec.max_slot + 1) if slot != bad]
    regular = next(slot for slot in candidates if spec.slot_value(slot) % q != 0)

    def row(slot: int) -> tuple[tuple[int, int], int, int, tuple[int, int], int]:
        left, right = 1, spec.stride * slot
        lv, rv = _vp(left, q), _vp(right, q)
        tropical = min(lv, rv)
        actual = _vp(left + right, q)
        lres = (left // (q**lv)) % q
        rres = (right // (q**rv)) % q
        return (lv, rv), tropical, actual, (lres, rres), (lres + rres) % q

    r_sig, r_trop, r_actual, r_res, r_sum = row(regular)
    s_sig, s_trop, s_actual, s_res, s_sum = row(bad)
    return TropicalTieCancellationAudit(
        spec.family,
        spec.parameter,
        q,
        regular,
        bad,
        r_sig,
        s_sig,
        r_trop,
        s_trop,
        r_actual,
        s_actual,
        s_actual - s_trop,
        r_res,
        s_res,
        r_sum,
        s_sum,
        r_sig == s_sig,
        s_trop == s_actual,
        r_sig[0] == r_sig[1],
        s_sig[0] == s_sig[1],
        (r_sig[0] == r_sig[1]) != (s_sig[0] == s_sig[1]),
        r_sum != 0 and s_sum == 0 and s_actual > s_trop,
        True,
    )


@dataclass(frozen=True, slots=True)
class TropicalAdditionNonclosureAudit:
    modulus: int
    hidden_factor: int
    regular_inputs: tuple[int, int]
    cancelling_inputs: tuple[int, int]
    regular_input_divisors: tuple[int, int]
    cancelling_input_divisors: tuple[int, int]
    regular_sum_divisor: int
    cancelling_sum_divisor: int
    same_divisor_inputs: bool
    different_exact_sum_divisors: bool
    divisor_only_addition_closed: bool


def tropical_addition_nonclosure_audit(
    family: str,
    parameter: int,
) -> TropicalAdditionNonclosureAudit:
    spec = SpecialJetProgressionSpec.build(family, parameter)
    factors = _factor_multiplicities_truth(spec.modulus)
    if len(factors) < 2:
        raise ValueError("composite control required")
    q = factors[0][0]
    regular = (1, 1)
    cancelling = (1, q - 1)
    rd = (gcd(spec.modulus, regular[0]), gcd(spec.modulus, regular[1]))
    cd = (gcd(spec.modulus, cancelling[0]), gcd(spec.modulus, cancelling[1]))
    rout = gcd(spec.modulus, sum(regular))
    cout = gcd(spec.modulus, sum(cancelling))
    same = rd == cd
    different = rout != cout
    return TropicalAdditionNonclosureAudit(
        spec.modulus,
        q,
        regular,
        cancelling,
        rd,
        cd,
        rout,
        cout,
        same,
        different,
        not (same and different),
    )


@dataclass(frozen=True, slots=True)
class TropicalAxisFluxRow:
    prime: int
    exponent_in_candidate: int
    first_slot_residue: int
    q_level_hits: int
    full_product_valuation: int
    saturated_kernel_height: int
    congruence_levels_tested: int
    morphism_height: int
    exact: bool


def _count_residue_hits(start: int, span: int, residue: int, period: int) -> int:
    end = start + span
    first = start + ((residue - start) % period)
    if first >= end:
        return 0
    return 1 + (end - 1 - first) // period


def _known_axis_flux(
    spec: SpecialJetProgressionSpec,
    q: int,
    exponent: int,
    start: int,
    span: int,
) -> TropicalAxisFluxRow:
    if gcd(spec.stride, q) != 1:
        raise ValueError((spec.stride, q))
    end_slot = start + span - 1
    max_atom = spec.slot_value(end_slot)
    q_power = q
    total = levels = hits_q = 0
    first_residue = (-pow(spec.stride, -1, q)) % q
    while q_power <= max_atom:
        residue = (-pow(spec.stride, -1, q_power)) % q_power
        hits = _count_residue_hits(start, span, residue, q_power)
        if q_power == q:
            hits_q = hits
        total += hits
        levels += 1
        q_power *= q
    saturated = min(exponent, total)
    morphism = ValuationSensitivityMorphism(
        q,
        exponent,
        1,
        saturated,
        span,
        0,
    )
    return TropicalAxisFluxRow(
        q,
        exponent,
        first_residue,
        hits_q,
        total,
        saturated,
        levels,
        morphism.apply(0),
        morphism.apply(0) == saturated,
    )


@dataclass(frozen=True, slots=True)
class TropicalAxisReconstructionAudit:
    family: str
    parameter: int
    start: int
    span: int
    modulus: int
    factor_truth: tuple[tuple[int, int], ...]
    rows: tuple[TropicalAxisFluxRow, ...]
    reconstructed_divisor: int
    direct_flux_gcd: int
    exact: bool
    axis_count: int
    congruence_level_evaluations: int
    interior_atom_evaluations: int
    compact_given_factor_axes: bool
    factor_truth_only: bool
    factor_free_axis_discovery_available: bool


def tropical_axis_reconstruction_audit(
    family: str,
    parameter: int,
    *,
    start: int,
    span: int,
) -> TropicalAxisReconstructionAudit:
    """Evaluate the tropical flux cheaply *after* all hidden q-axes are known."""
    spec, start, span = bounded_jet_spec(family, parameter, start, span)
    factors = _factor_multiplicities_truth(spec.modulus)
    rows = tuple(_known_axis_flux(spec, q, e, start, span) for q, e in factors)
    reconstructed = 1
    for row in rows:
        reconstructed *= row.prime**row.saturated_kernel_height
    direct = arithmetic_ghost_flux_block(
        family,
        parameter,
        start=start,
        span=span,
    ).support_gcd
    return TropicalAxisReconstructionAudit(
        spec.family,
        spec.parameter,
        start,
        span,
        spec.modulus,
        factors,
        rows,
        reconstructed,
        direct,
        reconstructed == direct and all(row.exact for row in rows),
        len(rows),
        sum(row.congruence_levels_tested for row in rows),
        0,
        True,
        True,
        False,
    )


@dataclass(frozen=True, slots=True)
class EnrichedTropicalPhaseCompressionAudit:
    family: str
    parameter: int
    modulus: int
    factor_truth: tuple[tuple[int, int], ...]
    radical: int
    squarefree: bool
    universal_leading_phase_modulus: int
    universal_phase_bits: int
    original_residue_bits: int
    strict_phase_state_compression: bool
    factor_truth_only: bool


def enriched_tropical_phase_compression_audit(
    family: str,
    parameter: int,
) -> EnrichedTropicalPhaseCompressionAudit:
    """Measure the exact phase retained by all hidden valuation axes.

    For a unit, the collection of leading residues modulo every q|N is, by CRT,
    exactly one residue modulo rad(N).  On a squarefree candidate rad(N)=N, so
    the fully enriched tropical unit phase is the ordinary ring residue again.
    """
    spec = SpecialJetProgressionSpec.build(family, parameter)
    factors = _factor_multiplicities_truth(spec.modulus)
    radical = 1
    squarefree = True
    for q, e in factors:
        radical *= q
        squarefree &= e == 1
    return EnrichedTropicalPhaseCompressionAudit(
        spec.family,
        spec.parameter,
        spec.modulus,
        factors,
        radical,
        squarefree,
        radical,
        bit_width(radical),
        bit_width(spec.modulus),
        bit_width(radical) < bit_width(spec.modulus),
        True,
    )


@dataclass(frozen=True, slots=True)
class TropicalSaturationDeletionAudit:
    modulus: int
    hidden_factor: int
    exponent_in_candidate: int
    saturated_state_at_e_occurrences: int
    saturated_state_at_e_plus_one_occurrences: int
    same_saturated_state: bool
    after_deleting_one_from_e: int
    after_deleting_one_from_e_plus_one: int
    deletion_outputs_differ: bool
    exact_delete_from_saturated_state_exists: bool
    factor_free_n_squared_lift_distinguishes: bool


def tropical_saturation_deletion_audit(
    family: str,
    parameter: int,
) -> TropicalSaturationDeletionAudit:
    spec = SpecialJetProgressionSpec.build(family, parameter)
    factors = _factor_multiplicities_truth(spec.modulus)
    if len(factors) < 2:
        raise ValueError("composite control required")
    q, e = factors[0]
    at_e = gcd(spec.modulus, q**e)
    at_e1 = gcd(spec.modulus, q ** (e + 1))
    delete_e = gcd(spec.modulus, q ** max(0, e - 1))
    delete_e1 = gcd(spec.modulus, q**e)
    lift_modulus = spec.modulus * spec.modulus
    lifted_e = gcd(lift_modulus, q**e)
    lifted_e1 = gcd(lift_modulus, q ** (e + 1))
    return TropicalSaturationDeletionAudit(
        spec.modulus,
        q,
        e,
        at_e,
        at_e1,
        at_e == at_e1,
        delete_e,
        delete_e1,
        delete_e != delete_e1,
        not (at_e == at_e1 and delete_e != delete_e1),
        lifted_e != lifted_e1,
    )


@dataclass(frozen=True, slots=True)
class TropicalMultiplicityLiftScalingAudit:
    modulus: int
    hidden_factor: int
    exponent_in_candidate: int
    multiplicity_horizon: int
    required_power_of_modulus: int
    factor_free_lift_description_bits_upper_bound: int
    factor_indexed_counter_bits_upper_bound: int
    factor_free_lift_bits_linear_in_horizon: bool
    factor_indexed_counter_requires_hidden_axis: bool


def tropical_multiplicity_lift_scaling_audit(
    family: str,
    parameter: int,
    *,
    multiplicity_horizon: int,
) -> TropicalMultiplicityLiftScalingAudit:
    spec = SpecialJetProgressionSpec.build(family, parameter)
    factors = _factor_multiplicities_truth(spec.modulus)
    if len(factors) < 2:
        raise ValueError("composite control required")
    q, e = factors[0]
    horizon = int(multiplicity_horizon)
    if horizon < 1:
        raise ValueError(horizon)
    power = (horizon + e - 1) // e
    return TropicalMultiplicityLiftScalingAudit(
        spec.modulus,
        q,
        e,
        horizon,
        power,
        power * bit_width(spec.modulus),
        bit_width(horizon) + bit_width(q),
        True,
        True,
    )


@dataclass(frozen=True, slots=True)
class TropicalGhostFluxFrontier:
    divisor_semiring_closed: bool
    factor_free_divisor_state_closed: bool
    tropical_block_state_constant_size: bool
    tropical_block_source_work_polylogarithmic: bool
    plain_min_plus_source_detects_tie_defect: bool
    enriched_residue_phase_detects_given_axis: bool
    factor_free_enriched_phase_available: bool
    fully_enriched_phase_strictly_smaller_on_squarefree_controls: bool
    divisor_only_addition_closed: bool
    known_axis_flux_compact: bool
    known_axis_flux_factor_truth_only: bool
    saturated_state_reversible: bool
    factor_free_overflow_state_polylogarithmic: bool
    production_source_extractor_available: bool
    status: str
    missing_operation: str


def tropical_ghost_flux_frontier() -> TropicalGhostFluxFrontier:
    return TropicalGhostFluxFrontier(
        divisor_semiring_closed=True,
        factor_free_divisor_state_closed=True,
        tropical_block_state_constant_size=True,
        tropical_block_source_work_polylogarithmic=False,
        plain_min_plus_source_detects_tie_defect=False,
        enriched_residue_phase_detects_given_axis=True,
        factor_free_enriched_phase_available=False,
        fully_enriched_phase_strictly_smaller_on_squarefree_controls=False,
        divisor_only_addition_closed=False,
        known_axis_flux_compact=True,
        known_axis_flux_factor_truth_only=True,
        saturated_state_reversible=False,
        factor_free_overflow_state_polylogarithmic=False,
        production_source_extractor_available=False,
        status="UNKNOWN",
        missing_operation=(
            "a factor-free source map that resolves equal-valuation leading-residue "
            "cancellation for 1+C*m, or an aggregate equally sensitive to those hidden "
            "valuation axes, in polylogarithmic total work; exact divisor-state "
            "composition after those source observations is already closed"
        ),
    )


__all__ = [
    "EnrichedTropicalPhaseCompressionAudit",
    "TropicalAdditionNonclosureAudit",
    "TropicalAxisFluxRow",
    "TropicalAxisReconstructionAudit",
    "TropicalBlockCompositionAudit",
    "TropicalDivisorSemiringAudit",
    "TropicalDivisorState",
    "TropicalGhostFluxFrontier",
    "TropicalMultiplicityLiftScalingAudit",
    "TropicalSaturationDeletionAudit",
    "TropicalTieCancellationAudit",
    "enriched_tropical_phase_compression_audit",
    "tropical_addition_nonclosure_audit",
    "tropical_axis_reconstruction_audit",
    "tropical_block_composition_audit",
    "tropical_divisor_semiring_audit",
    "tropical_ghost_flux_frontier",
    "tropical_multiplicity_lift_scaling_audit",
    "tropical_saturation_deletion_audit",
    "tropical_tie_cancellation_audit",
]

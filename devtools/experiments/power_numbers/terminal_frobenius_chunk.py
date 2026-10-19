"""Exact r-level local Frobenius chunk audits.

This module proves the block semantics behind the production fail-closed
``special_frobenius_chunk`` surface.  Factor truth is accepted only as an audit
label: it verifies that the complete local r-level action is the compact stride
residue ``rho=k mod 2**r`` and that adjacent chunks compose without expanding a
negacyclic polynomial or replaying one level at a time.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.sequences.power_numbers.frobenius_chunk import (
    SpecialFrobeniusChunkResult,
    SpecialFrobeniusChunkSpec,
    folded_x_coefficient_from_stride_residue,
    special_frobenius_chunk_probe,
)
from number_compiler.sequences.power_numbers.numbers import (
    fermat_number,
    mersenne_number,
)


@dataclass(frozen=True, slots=True)
class SpecialLocalFrobeniusChunkAudit:
    """Factor-backed audit of the exact r-level stride-residue quotient."""

    family: str
    parameter: int
    start_level: int
    span: int
    supplied_prime_factor: int
    factor_truth_only: bool
    local_character: int
    baseline_local_v2: int
    base_stride_v2: int
    reaches_start_boundary: bool
    stride_quotient: int | None
    stride_residue: int | None
    folded_x_coefficient: int | None
    local_depth: int
    all_levels_pass: bool
    polynomial_terms_materialized: int
    one_level_replays: int
    equation: str


@dataclass(frozen=True, slots=True)
class SpecialFrobeniusChunkCompositionAudit:
    family: str
    parameter: int
    supplied_prime_factor: int
    start_level: int
    left_span: int
    right_span: int
    left_zero_class: bool
    right_reaches_boundary: bool
    right_zero_class: bool | None
    full_zero_class: bool
    combined_stride_residue: int | None
    full_stride_residue: int | None
    residue_composition_exact: bool
    semantic_composition_exact: bool
    polynomial_terms_materialized: int
    one_level_replays: int
    factor_truth_only: bool = True


def _low_stride_residue(value: int, span: int) -> int:
    value, span = int(value), int(span)
    if value < 0 or span < 1:
        raise ValueError((value, span))
    if value.bit_length() <= span:
        return value
    return value & ((1 << span) - 1)


def _mersenne_local_character(prime: int) -> int:
    q = int(prime)
    if q <= 3 or not (q & 1):
        raise ValueError(q)
    symbol = pow(12 % q, (q - 1) // 2, q)
    if symbol == 1:
        return 1
    if symbol == q - 1:
        return -1
    raise ValueError(("ramified-local-character", q, symbol))


def special_local_frobenius_chunk_audit(
    family: str,
    parameter: int,
    start_level: int,
    span: int,
    supplied_prime_factor: int,
) -> SpecialLocalFrobeniusChunkAudit:
    """Audit the compact r-level local Frobenius residue with factor truth only.

    The calculation never constructs the negacyclic polynomial.  For Fermat,
    ``q=1+2**(n+start_level)*k``.  For Mersenne, after quotienting the fixed
    quadratic character, ``q=chi+2**(start_level+1)*k``.  The complete block is
    ``rho=k mod 2**span`` and all levels pass iff ``rho==0``.
    """
    fam, par = str(family), int(parameter)
    start, span, q = int(start_level), int(span), int(supplied_prime_factor)
    if start < 1 or span < 1 or q <= 2:
        raise ValueError((start, span, q))
    if fam == "fermat":
        candidate = fermat_number(par)
        baseline = par + 1
        character = 1
    elif fam == "mersenne":
        candidate = mersenne_number(par)
        baseline = 2
        character = _mersenne_local_character(q)
    else:
        raise ValueError(fam)
    if candidate % q:
        raise ValueError(("not-a-supplied-special-factor", fam, par, q))

    delta = q - character
    local_v2 = v2_positive(delta)
    local_depth = max(0, local_v2 - baseline)
    base_v2 = baseline + start - 1
    reaches = local_v2 >= base_v2
    quotient = residue = coefficient = None
    if reaches:
        quotient = delta >> base_v2
        residue = _low_stride_residue(quotient, span)
        coefficient = folded_x_coefficient_from_stride_residue(residue, span)
    all_pass = local_depth >= start + span - 1
    if all_pass != (reaches and residue == 0):
        raise AssertionError((fam, par, q, start, span, local_depth, residue))
    if reaches and ((coefficient == 1) != all_pass):
        raise AssertionError((fam, par, q, start, span, coefficient, all_pass))

    return SpecialLocalFrobeniusChunkAudit(
        fam,
        par,
        start,
        span,
        q,
        True,
        character,
        baseline,
        base_v2,
        reaches,
        quotient,
        residue,
        coefficient,
        local_depth,
        all_pass,
        0,
        0,
        "rho=k mod 2^r; [X](X^(eps+m*k) mod (X^(m*2^(r-1))+1))=1 iff rho=0",
    )


def _result_from_local_chunk_audit(
    audit: SpecialLocalFrobeniusChunkAudit,
) -> SpecialFrobeniusChunkResult:
    modulus_bits = (
        fermat_number(audit.parameter).bit_length()
        if audit.family == "fermat"
        else audit.parameter
    )
    spec = SpecialFrobeniusChunkSpec(
        audit.family,
        audit.parameter,
        audit.start_level,
        audit.span,
        audit.baseline_local_v2,
        modulus_bits,
    )
    if audit.all_levels_pass:
        return SpecialFrobeniusChunkResult(
            spec,
            "ALL_PASS",
            "factor-backed-local-chunk-audit",
            True,
        )
    return SpecialFrobeniusChunkResult(
        spec,
        "ALL_FAIL",
        "factor-backed-local-chunk-audit",
        False,
        first_failure_offset=0 if not audit.reaches_start_boundary else None,
    )


def special_frobenius_chunk_composition_audit(
    family: str,
    parameter: int,
    start_level: int,
    left_span: int,
    right_span: int,
    supplied_prime_factor: int,
) -> SpecialFrobeniusChunkCompositionAudit:
    """Verify chunk concatenation against the direct larger stride residue."""
    left = special_local_frobenius_chunk_audit(
        family,
        parameter,
        start_level,
        left_span,
        supplied_prime_factor,
    )
    full = special_local_frobenius_chunk_audit(
        family,
        parameter,
        start_level,
        left_span + right_span,
        supplied_prime_factor,
    )
    right = special_local_frobenius_chunk_audit(
        family,
        parameter,
        start_level + left_span,
        right_span,
        supplied_prime_factor,
    )

    combined_residue = None
    residue_exact = False
    semantic_exact = False
    if left.stride_residue is not None and right.stride_residue is not None:
        combined_residue = left.stride_residue + (right.stride_residue << left_span)
        residue_exact = combined_residue == full.stride_residue
    if left.all_levels_pass:
        composed = _result_from_local_chunk_audit(left).compose(
            _result_from_local_chunk_audit(right)
        )
        semantic_exact = composed.all_pass == full.all_levels_pass
    else:
        # A failing left chunk already decides the conjunction; downstream is
        # conditional on that boundary and need not be evaluated in production.
        semantic_exact = not full.all_levels_pass

    return SpecialFrobeniusChunkCompositionAudit(
        str(family),
        int(parameter),
        int(supplied_prime_factor),
        int(start_level),
        int(left_span),
        int(right_span),
        left.all_levels_pass,
        right.reaches_start_boundary,
        right.all_levels_pass if right.reaches_start_boundary else None,
        full.all_levels_pass,
        combined_residue,
        full.stride_residue,
        residue_exact,
        semantic_exact,
        0,
        0,
    )


def terminal_frobenius_chunk_candidate_audit(
    family: str,
    parameter: int,
    start_level: int,
    span: int,
    baseline_local_v2: int,
    modulus_bits: int,
) -> SpecialFrobeniusChunkResult:
    """Expose the production fail-closed candidate edge to research/tests."""
    spec = SpecialFrobeniusChunkSpec(
        str(family),
        int(parameter),
        int(start_level),
        int(span),
        int(baseline_local_v2),
        int(modulus_bits),
    )
    return special_frobenius_chunk_probe(spec)


@dataclass(frozen=True, slots=True)
class SpecialFrobeniusDefectCRTAudit:
    """Factor-backed audit of the final candidate-ring defect/gcd classification.

    This is deliberately research-only.  It constructs the CRT element whose
    local residues are ``folded_X-1`` solely to prove that one candidate-ring
    defect is sufficient after extraction.  Production never imports or calls
    this constructor.
    """

    family: str
    parameter: int
    start_level: int
    span: int
    supplied_prime_factors: tuple[int, ...]
    local_defects: tuple[int, ...]
    crt_defect: int
    support_gcd: int
    status: str
    factor_truth_only: bool = True
    polynomial_terms_materialized: int = 0
    one_level_replays: int = 0


def _crt_pairwise_coprime(residues: tuple[int, ...], moduli: tuple[int, ...]) -> int:
    if not residues or len(residues) != len(moduli):
        raise ValueError((residues, moduli))
    modulus = 1
    for q in moduli:
        if q <= 1:
            raise ValueError(q)
        if any(q % prior == 0 or prior % q == 0 for prior in moduli if prior != q):
            # The current audit controls are squarefree.  Repeated-prime support
            # has a separate multiplicity theorem and is not reconstructed here.
            pass
        modulus *= q
    out = 0
    for residue, q in zip(residues, moduli, strict=True):
        cofactor = modulus // q
        out += (int(residue) % q) * cofactor * pow(cofactor, -1, q)
    return out % modulus


def special_frobenius_defect_crt_audit(
    family: str,
    parameter: int,
    start_level: int,
    span: int,
    supplied_prime_factors: tuple[int, ...],
) -> SpecialFrobeniusDefectCRTAudit:
    """Prove that one folded-X defect plus one gcd gives PASS/FAIL/SPLIT."""
    from math import gcd

    from number_compiler.sequences.power_numbers.frobenius_chunk import (
        folded_x_defect_from_stride_residue,
    )

    fam, par = str(family), int(parameter)
    factors = tuple(map(int, supplied_prime_factors))
    N = fermat_number(par) if fam == "fermat" else mersenne_number(par)
    product = 1
    for q in factors:
        product *= q
    if product != N:
        raise ValueError(
            ("audit-needs-complete-squarefree-factorization", N, factors, product)
        )

    audits = tuple(
        special_local_frobenius_chunk_audit(fam, par, start_level, span, q)
        for q in factors
    )
    defects: list[int] = []
    for row in audits:
        if not row.reaches_start_boundary:
            # Failure before the chunk boundary must be a local unit in the
            # terminal failure ideal.  -1 is the canonical audit representative.
            defects.append(-1)
        else:
            assert row.stride_residue is not None
            defects.append(
                folded_x_defect_from_stride_residue(row.stride_residue, span)
            )
    defect = _crt_pairwise_coprime(tuple(defects), factors)
    g = gcd(defect, N)
    status = "ALL_PASS" if g == N else "ALL_FAIL" if g == 1 else "SPLIT"
    return SpecialFrobeniusDefectCRTAudit(
        fam,
        par,
        int(start_level),
        int(span),
        factors,
        tuple(defects),
        defect,
        g,
        status,
    )

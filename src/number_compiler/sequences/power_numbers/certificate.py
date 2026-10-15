"""Scalable Fermat/Mersenne theorem certificates.

Production consumes only the constrained terminal étale threshold.  A proved
PASS/FAIL/SPLIT is used immediately; an incomplete shadow-cylinder recovery is
reported as ``UNKNOWN``.  Reference special-form recurrences live outside the
production package and cannot complete this certificate path.
"""

from __future__ import annotations

from number_compiler.api.observation_types import FamilyId
from number_compiler.api.sequence_types import SpecialDepthCertificateSummary
from number_compiler.arithmetic.polynomials.two_primary_filtration import (
    PureTwoPrimaryClockShape,
    pure_two_primary_clock_shape,
)
from number_compiler.sequences.power_numbers.admission import (
    require_special_candidate_budget,
)
from number_compiler.sequences.power_numbers.numbers import mersenne_exponent_is_prime
from number_compiler.sequences.power_numbers.terminal_threshold import (
    SpecialTerminalThresholdResult,
    terminal_threshold_probe,
)


def _proved_pure_clock_shape(family: str, parameter: int) -> PureTwoPrimaryClockShape:
    """Build compact clock metadata only after the caller proved PASS."""
    shape = pure_two_primary_clock_shape(family, parameter)
    clock_steps = shape.target_horizon - shape.observer_offset
    if clock_steps < 0 or not shape.target_after_clock_steps(clock_steps):
        raise AssertionError((family, parameter, "pure-clock-terminal"))
    return shape


def _summary_from_terminal_pass(
    probe: SpecialTerminalThresholdResult,
) -> SpecialDepthCertificateSummary:
    """Promote a proved all-local terminal PASS into the closed pure theorem."""
    shape = _proved_pure_clock_shape(probe.family, probe.parameter)
    return SpecialDepthCertificateSummary(
        FamilyId(probe.family),
        probe.parameter,
        shape.modulus_bits,
        "prime",
        f"terminal-threshold:{probe.method}",
        shape.quotient_classes,
        max(1, (shape.quotient_classes - 1).bit_length()),
        0,
        0,
        0,
        shape.target_depth,
        True,
        0,
        probe.character_queries,
        probe.reciprocity_descents,
        0,
        shape.stable_image_states,
        shape.image_depth_classes,
        True,
    )


def _summary_from_terminal_composite(
    probe: SpecialTerminalThresholdResult,
) -> SpecialDepthCertificateSummary:
    if not probe.proves_composite:
        raise ValueError(probe.status)
    return SpecialDepthCertificateSummary(
        FamilyId(probe.family),
        probe.parameter,
        probe.modulus_bits,
        "composite",
        f"terminal-threshold:{probe.method}",
        scalable_construction=True,
        carrier_states_enumerated=0,
        specialization_raw_squarings=0,
        character_queries=probe.character_queries,
        reciprocity_descents=probe.reciprocity_descents,
        gcd_witnesses=int(probe.status == "SPLIT"),
        factor_witness=probe.gcd_packet,
    )


def _summary_from_terminal_unknown(
    probe: SpecialTerminalThresholdResult,
) -> SpecialDepthCertificateSummary:
    if probe.decided:
        raise ValueError(probe.status)
    return SpecialDepthCertificateSummary(
        FamilyId(probe.family),
        probe.parameter,
        probe.modulus_bits,
        "unknown",
        (
            f"terminal-threshold:{probe.method}:{probe.source_demand.missing_proofs[0]}"
            if probe.source_demand is not None
            else f"terminal-threshold:{probe.method}"
        ),
        scalable_construction=False,
        carrier_states_enumerated=0,
        character_queries=probe.character_queries,
        reciprocity_descents=probe.reciprocity_descents,
    )


def _certificate_flags(collect_gcd_packet: bool, allow_classical_ceiling: bool) -> None:
    if type(collect_gcd_packet) is not bool:
        raise TypeError("collect_gcd_packet must be a Boolean")
    if type(allow_classical_ceiling) is not bool:
        raise TypeError("allow_classical_ceiling must be a Boolean")
    if allow_classical_ceiling:
        raise ValueError("classical primality recurrences are not production paths")


def fermat_depth_certificate(
    index: int,
    *,
    max_exact_width: int | None = None,
    max_candidate_bits: int = 1_000_000,
    allow_classical_ceiling: bool = False,
    collect_gcd_packet: bool = False,
) -> SpecialDepthCertificateSummary:
    """Classify ``F_index`` from the constrained terminal étale threshold.

    ``max_exact_width`` is retained as a compatibility keyword but is
    intentionally ignored.  Production never re-enters the old exhaustive
    bounded carrier or factor-slot tropical scan.

    ``allow_classical_ceiling`` remains only as a compatibility keyword.  True
    is rejected because special-form recurrence completion is not a production
    theorem source.
    """
    n = int(index)
    if n < 0:
        raise ValueError(n)
    if max_exact_width is not None and int(max_exact_width) < 1:
        raise ValueError(max_exact_width)
    _certificate_flags(collect_gcd_packet, allow_classical_ceiling)
    require_special_candidate_budget("fermat", n, max_candidate_bits)
    width = 1 << n
    modulus_bits = width + 1
    if n in (0, 1):
        return SpecialDepthCertificateSummary(
            FamilyId.FERMAT,
            n,
            modulus_bits,
            "prime",
            "exact-small-special-form",
            scalable_construction=True,
        )

    threshold = terminal_threshold_probe(
        "fermat", n, max_candidate_bits=max_candidate_bits
    )
    if threshold.all_pass:
        return _summary_from_terminal_pass(threshold)
    if threshold.proves_composite:
        return _summary_from_terminal_composite(threshold)
    return _summary_from_terminal_unknown(threshold)


def mersenne_depth_certificate(
    exponent: int,
    *,
    max_exact_exponent: int | None = None,
    max_candidate_bits: int = 1_000_000,
    allow_classical_ceiling: bool = False,
    collect_gcd_packet: bool = False,
) -> SpecialDepthCertificateSummary:
    """Classify ``M_exponent`` from exponent gates and the étale threshold.

    ``max_exact_exponent`` is retained for source compatibility but never
    enables the historical exhaustive carrier or factor-slot fallback.
    The compatibility ceiling keyword rejects true.  Unresolved terminal bits
    remain ``unknown`` while exact small cases and exponent rejection survive.
    """
    p = int(exponent)
    if p < 2:
        raise ValueError(p)
    if max_exact_exponent is not None and int(max_exact_exponent) < 3:
        raise ValueError(max_exact_exponent)
    _certificate_flags(collect_gcd_packet, allow_classical_ceiling)
    require_special_candidate_budget("mersenne", p, max_candidate_bits)
    if p == 2:
        return SpecialDepthCertificateSummary(
            FamilyId.MERSENNE,
            p,
            p,
            "prime",
            "exact-small-special-form",
            scalable_construction=True,
        )

    # The exact exponent predicate is deliberately machine-word bounded.
    # Preserve the immediate 2/3 divisor cases, but do not let this direct
    # certificate entry point reach the historical unbounded factor search.
    if p >= 1 << 64:
        if not (p & 1) or p % 3 == 0:
            return SpecialDepthCertificateSummary(
                FamilyId.MERSENNE,
                p,
                p,
                "composite",
                "composite-exponent-small-factor",
                scalable_construction=True,
            )
        return SpecialDepthCertificateSummary(
            FamilyId.MERSENNE,
            p,
            p,
            "unknown",
            "exponent-gate-budget",
            scalable_construction=False,
        )

    if not mersenne_exponent_is_prime(p):
        return SpecialDepthCertificateSummary(
            FamilyId.MERSENNE,
            p,
            p,
            "composite",
            "composite-exponent-factor",
            scalable_construction=True,
        )
    if not (p & 1):
        raise AssertionError((p, "even exponent escaped factor rejection"))

    threshold = terminal_threshold_probe(
        "mersenne", p, max_candidate_bits=max_candidate_bits
    )
    if threshold.all_pass:
        return _summary_from_terminal_pass(threshold)
    if threshold.proves_composite:
        return _summary_from_terminal_composite(threshold)
    return _summary_from_terminal_unknown(threshold)


__all__ = ["fermat_depth_certificate", "mersenne_depth_certificate"]

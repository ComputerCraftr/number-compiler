"""Scalable Fermat/Mersenne theorem certificates.

Production first consumes the logarithmic constrained terminal germ.  A proved
PASS/FAIL/SPLIT is used immediately.  If that compact quotient remains
``UNKNOWN``, the demanded theorem query falls back to the exact classical
special-form recurrence with an explicit linear squaring budget.  This is the
hard production ceiling: no factor-slot/tropical scan, exhaustive carrier, CRT
factorization, or saved itinerary is permitted.

The recurrence implementation lives in :mod:`special_classical_ceiling`, not
the oracle package, because it is now an intentional production fallback rather
than a hidden research escape.
"""

from __future__ import annotations

from number_compiler.api.sequence_types import SpecialDepthCertificateSummary
from number_compiler.arithmetic.polynomials.two_primary_filtration import (
    PureTwoPrimaryClockShape,
    pure_two_primary_clock_shape,
)
from number_compiler.sequences.power_numbers.classical_ceiling import (
    SpecialClassicalCeilingResult,
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
        probe.family,
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
        probe.family,
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
    )


def _summary_from_terminal_unknown(
    probe: SpecialTerminalThresholdResult,
) -> SpecialDepthCertificateSummary:
    if probe.decided:
        raise ValueError(probe.status)
    return SpecialDepthCertificateSummary(
        probe.family,
        probe.parameter,
        probe.modulus_bits,
        "unknown",
        f"terminal-threshold:{probe.method}",
        scalable_construction=True,
        carrier_states_enumerated=0,
        character_queries=probe.character_queries,
        reciprocity_descents=probe.reciprocity_descents,
    )


def _summary_from_classical_ceiling(
    row: SpecialClassicalCeilingResult,
) -> SpecialDepthCertificateSummary:
    """Promote an exact classical target pullback into the certificate lattice."""
    if row.passes:
        shape = _proved_pure_clock_shape(row.family, row.parameter)
        return SpecialDepthCertificateSummary(
            row.family,
            row.parameter,
            row.modulus_bits,
            "prime",
            row.method,
            shape.quotient_classes,
            max(1, (shape.quotient_classes - 1).bit_length()),
            0,
            0,
            row.raw_specialization_squarings,
            shape.target_depth,
            True,
            0,
            0,
            0,
            0,
            shape.stable_image_states,
            shape.image_depth_classes,
            True,
        )
    return SpecialDepthCertificateSummary(
        row.family,
        row.parameter,
        row.modulus_bits,
        "composite",
        row.method,
        specialization_raw_squarings=row.raw_specialization_squarings,
        scalable_construction=True,
        carrier_states_enumerated=0,
        gcd_witnesses=int(row.gcd_packet is not None),
    )


def fermat_depth_certificate(
    index: int,
    *,
    max_exact_width: int | None = None,
    allow_classical_ceiling: bool = True,
) -> SpecialDepthCertificateSummary:
    """Classify ``F_index`` with constrained terminal proof then optional ceiling.

    ``max_exact_width`` is retained as a compatibility keyword but is
    intentionally ignored.  Production never re-enters the old exhaustive
    bounded carrier or factor-slot tropical scan.

    When ``allow_classical_ceiling`` is false, an unresolved compact terminal
    probe returns ``unknown`` without executing the recurrence.
    """
    n = int(index)
    if n < 0:
        raise ValueError(n)
    if max_exact_width is not None and int(max_exact_width) < 1:
        raise ValueError(max_exact_width)
    if type(allow_classical_ceiling) is not bool:
        raise TypeError("allow_classical_ceiling must be a Boolean")
    width = 1 << n
    modulus_bits = width + 1
    if n in (0, 1):
        return SpecialDepthCertificateSummary(
            "fermat",
            n,
            modulus_bits,
            "prime",
            "exact-small-special-form",
            scalable_construction=True,
        )

    threshold = terminal_threshold_probe("fermat", n)
    if threshold.all_pass:
        return _summary_from_terminal_pass(threshold)
    if threshold.proves_composite:
        return _summary_from_terminal_composite(threshold)
    if not allow_classical_ceiling:
        return _summary_from_terminal_unknown(threshold)
    from number_compiler.sequences.power_numbers.classical_ceiling import (
        fermat_classical_ceiling,
    )

    return _summary_from_classical_ceiling(fermat_classical_ceiling(n))


def mersenne_depth_certificate(
    exponent: int,
    *,
    max_exact_exponent: int | None = None,
    allow_classical_ceiling: bool = True,
) -> SpecialDepthCertificateSummary:
    """Classify ``M_exponent`` with exponent/constraint gates and optional ceiling.

    ``max_exact_exponent`` is retained for source compatibility but never
    enables the historical exhaustive carrier or factor-slot fallback.
    Disabling the ceiling leaves an unresolved terminal probe ``unknown`` while
    preserving exact small cases and composite-exponent rejection.
    """
    p = int(exponent)
    if p < 2:
        raise ValueError(p)
    if max_exact_exponent is not None and int(max_exact_exponent) < 3:
        raise ValueError(max_exact_exponent)
    if type(allow_classical_ceiling) is not bool:
        raise TypeError("allow_classical_ceiling must be a Boolean")
    if p == 2:
        return SpecialDepthCertificateSummary(
            "mersenne",
            p,
            p,
            "prime",
            "exact-small-special-form",
            scalable_construction=True,
        )

    if not mersenne_exponent_is_prime(p):
        return SpecialDepthCertificateSummary(
            "mersenne",
            p,
            p,
            "composite",
            "composite-exponent-factor",
            scalable_construction=True,
        )
    if not (p & 1):
        raise AssertionError((p, "even exponent escaped factor rejection"))

    threshold = terminal_threshold_probe("mersenne", p)
    if threshold.all_pass:
        return _summary_from_terminal_pass(threshold)
    if threshold.proves_composite:
        return _summary_from_terminal_composite(threshold)
    if not allow_classical_ceiling:
        return _summary_from_terminal_unknown(threshold)
    from number_compiler.sequences.power_numbers.classical_ceiling import (
        mersenne_classical_ceiling,
    )

    return _summary_from_classical_ceiling(mersenne_classical_ceiling(p))


__all__ = ["fermat_depth_certificate", "mersenne_depth_certificate"]

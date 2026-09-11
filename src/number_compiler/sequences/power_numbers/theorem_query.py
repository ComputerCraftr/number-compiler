"""Demand-driven theorem resolution for Fermat and Mersenne sources.

Raw special-number compilation knows the source digits exactly and therefore
must never pay for primality classification.  This module owns theorem work behind an explicit query boundary.  Small-factor
projection is opt-in; the default exact path tries the compact constrained germ
and then the classical linear-work ceiling.  Imports remain local so merely
importing the canonical compiler does not construct theorem machinery.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.automata.program_word import from_runs
from number_compiler.projection.output_quotient import SpecialSourceGuard
from number_compiler.sequences.power_numbers.numbers import (
    FermatNumberSpec,
    MersenneNumberSpec,
)

if TYPE_CHECKING:
    from number_compiler.api.sequence_types import (
        FactoredRadixProjection,
        SpecialDepthCertificateSummary,
    )


@dataclass(frozen=True, slots=True)
class SpecialTheoremResolution:
    """Result of one explicitly demanded source-theorem query."""

    family: str
    parameter: int
    source_guard: SpecialSourceGuard
    primality: "SpecialDepthCertificateSummary | None" = None
    projection_method: str = "deferred"
    factor_witness: int | None = None
    composite_exponent_factor: MersenneNumberSpec | None = None
    factored_projection: "FactoredRadixProjection | None" = None

    @property
    def decided(self) -> bool:
        return self.source_guard.resolved


def _factored_projection(
    family: str,
    parameter: int,
    factor_limit: int,
) -> "FactoredRadixProjection | None":
    factor_limit = int(factor_limit)
    if factor_limit < 2:
        return None
    from number_compiler.api.sequence_terms import factored_word_projection
    from number_compiler.arithmetic.fields.congruence_automaton import (
        FactoredPrimeAutomaton,
    )

    automaton = FactoredPrimeAutomaton.build(factor_limit)
    if family == "fermat":
        number = FermatNumberSpec(parameter)
        word = (
            from_runs(((1, 2),))
            if parameter == 0
            else from_runs(((1, 1), (0, number.exponent - 1), (1, 1)))
        )
    else:
        word = from_runs(((1, parameter),))
    return factored_word_projection(word, 2, automaton)


def resolve_special_theorem(
    family: str,
    parameter: int,
    *,
    factor_limit: int = 1000,
    use_factor_projection: bool = False,
    use_terminal_certificate: bool = True,
    allow_classical_ceiling: bool = True,
) -> SpecialTheoremResolution:
    """Resolve only when a theorem-sensitive consumer explicitly asks.

    The ordering is cheap exponent rejection first, optional explicitly requested
    small-factor projection, then exact theorem resolution.  Exact resolution
    first consumes compact pulled-back germ constraints and, if still unresolved,
    uses the classical recurrence ceiling when that policy is enabled.  With
    ``allow_classical_ceiling=False``, an unresolved compact probe is returned
    as a guarded ``unknown`` result.  Nothing here is called by raw source compilation.
    """
    family = str(family)
    parameter = int(parameter)
    if family not in ("fermat", "mersenne"):
        raise ValueError(family)
    if parameter < 0 or (family == "mersenne" and parameter < 2):
        raise ValueError(parameter)
    if type(allow_classical_ceiling) is not bool:
        raise TypeError("allow_classical_ceiling must be a Boolean")

    exponent_factor = None
    if family == "mersenne":
        # The theorem gate needs only the prime/composite bit.  Use the exact
        # deterministic u64 predicate first; produce an actual factor only on
        # the composite branch because that witness is part of this API result.
        from number_compiler.sequences.power_numbers.numbers import (
            mersenne_composite_exponent_factor,
            mersenne_exponent_is_prime,
        )

        if not mersenne_exponent_is_prime(parameter):
            exponent_factor = mersenne_composite_exponent_factor(parameter)
            if exponent_factor is None:
                raise AssertionError(
                    (parameter, "composite exponent lost factor witness")
                )
            guard = SpecialSourceGuard(
                "mersenne",
                parameter,
                True,
                "composite_exponent_factor",
            )
            return SpecialTheoremResolution(
                family,
                parameter,
                guard,
                projection_method="exponent_factor",
                composite_exponent_factor=exponent_factor,
            )

    projection = None
    witness = None
    proper_witness = None
    if use_factor_projection:
        projection = _factored_projection(family, parameter, factor_limit)
        if projection is not None:
            witness = projection.small_factor_witness
            number_bits = (
                FermatNumberSpec(parameter).bit_length_extent
                if family == "fermat"
                else MersenneNumberSpec(parameter).bit_length
            )
            # If N has more bits than the complete search limit, a witnessed
            # factor <= limit is necessarily proper.  For small N, defer to the
            # exact terminal certificate rather than labelling N itself a factor.
            if witness is not None and number_bits > max(
                1, int(factor_limit).bit_length()
            ):
                proper_witness = int(witness)
                guard = SpecialSourceGuard(
                    family,
                    parameter,
                    True,
                    "factored_digit_witness",
                )
                return SpecialTheoremResolution(
                    family,
                    parameter,
                    guard,
                    projection_method="factored_digit_witness",
                    factor_witness=proper_witness,
                    factored_projection=projection,
                )

    if not use_terminal_certificate:
        guard = SpecialSourceGuard(family, parameter, None, "deferred")
        return SpecialTheoremResolution(
            family,
            parameter,
            guard,
            projection_method="deferred",
            factor_witness=proper_witness,
            composite_exponent_factor=exponent_factor,
            factored_projection=projection,
        )

    from number_compiler.sequences.power_numbers.certificate import (
        fermat_depth_certificate,
        mersenne_depth_certificate,
    )

    certificate = (
        fermat_depth_certificate(
            parameter, allow_classical_ceiling=allow_classical_ceiling
        )
        if family == "fermat"
        else mersenne_depth_certificate(
            parameter, allow_classical_ceiling=allow_classical_ceiling
        )
    )
    guard = SpecialSourceGuard.from_certificate_status(
        family,
        parameter,
        certificate.status,
        certificate.method,
    )
    return SpecialTheoremResolution(
        family,
        parameter,
        guard,
        primality=certificate,
        projection_method=certificate.method,
        factor_witness=proper_witness,
        composite_exponent_factor=exponent_factor,
        factored_projection=projection,
    )


__all__ = ["SpecialTheoremResolution", "resolve_special_theorem"]

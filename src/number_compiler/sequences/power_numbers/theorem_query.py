"""Demand-driven theorem resolution for Fermat and Mersenne sources.

Raw special-number compilation knows the source digits exactly and therefore
must never pay for primality classification.  This module owns theorem work
behind an explicit query boundary.  Small-factor projection is opt-in; the
exact path uses the compact constrained étale germ.  An unresolved recovery
stays guarded rather than being completed by a special-form recurrence.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import TYPE_CHECKING

from number_compiler.arithmetic.automata.program_word import from_runs
from number_compiler.arithmetic.contracts.family_identity import family_id
from number_compiler.projection.output_quotient import SpecialSourceGuard
from number_compiler.sequences.power_numbers.admission import (
    require_special_candidate_budget,
)
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
    primality: SpecialDepthCertificateSummary | None = None
    projection_method: str = "deferred"
    factor_witness: int | None = None
    composite_exponent_factor: MersenneNumberSpec | None = None
    factored_projection: FactoredRadixProjection | None = None
    etale_ring_multiplications: int = 0
    factor_query_status: str = "not-requested"

    @property
    def decided(self) -> bool:
        return self.source_guard.resolved


def _factored_projection(
    family: str,
    parameter: int,
    factor_limit: int,
) -> FactoredRadixProjection | None:
    factor_limit = int(factor_limit)
    if factor_limit < 2:
        return None
    from number_compiler.api.sequence_terms import factored_word_projection
    from number_compiler.sequences.prime.congruence import (
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
    allow_classical_ceiling: bool = False,
    collect_etale_factor: bool = False,
    max_factor_products: int = 4096,
    max_candidate_bits: int = 1_000_000,
) -> SpecialTheoremResolution:
    """Resolve only when a theorem-sensitive consumer explicitly asks.

    The ordering is cheap exponent rejection first, optional explicitly
    requested small-factor projection, then compact pulled-back germ
    constraints.  An unresolved compact probe returns a guarded ``unknown``.
    ``allow_classical_ceiling`` is a rejected compatibility keyword; reference
    recurrences cannot decide a production theorem query.
    """
    if type(collect_etale_factor) is not bool:
        raise TypeError("collect_etale_factor must be a Boolean")
    if type(max_factor_products) is not int or max_factor_products < 0:
        raise ValueError("max_factor_products must be a nonnegative integer")
    family = str(family)
    parameter = int(parameter)
    if family not in ("fermat", "mersenne"):
        raise ValueError(family)
    if parameter < 0 or (family == "mersenne" and parameter < 2):
        raise ValueError(parameter)
    if type(allow_classical_ceiling) is not bool:
        raise TypeError("allow_classical_ceiling must be a Boolean")
    if allow_classical_ceiling:
        raise ValueError("classical primality recurrences are not production paths")
    require_special_candidate_budget(family, parameter, max_candidate_bits)

    if (
        family == "mersenne"
        and parameter >= 1 << 64
        and parameter % 2
        and parameter % 3
    ):
        return SpecialTheoremResolution(
            family,
            parameter,
            SpecialSourceGuard(family, parameter, None, "exponent-gate-budget"),
            projection_method="exponent-gate-budget",
        )

    exponent_factor = None
    if family == "mersenne":
        # The theorem gate needs only the prime/composite bit.  Use the exact
        # deterministic u64 predicate first; produce an actual factor only on
        # the composite branch because that witness is part of this API result.
        from number_compiler.sequences.power_numbers.numbers import (
            mersenne_composite_exponent_factor,
            mersenne_exponent_is_prime,
        )

        if parameter >= 1 << 64 or not mersenne_exponent_is_prime(parameter):
            exponent_factor = mersenne_composite_exponent_factor(
                parameter, max_divisor=1000
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
                factor_query_status=(
                    ("available" if exponent_factor is not None else "no-split")
                    if collect_etale_factor
                    else "not-requested"
                ),
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
            parameter,
            max_candidate_bits=max_candidate_bits,
            allow_classical_ceiling=allow_classical_ceiling,
            collect_gcd_packet=collect_etale_factor,
        )
        if family == "fermat"
        else mersenne_depth_certificate(
            parameter,
            max_candidate_bits=max_candidate_bits,
            allow_classical_ceiling=allow_classical_ceiling,
            collect_gcd_packet=collect_etale_factor,
        )
    )
    guard = SpecialSourceGuard.from_certificate_status(
        family,
        parameter,
        certificate.status,
        certificate.method,
    )
    result = SpecialTheoremResolution(
        family,
        parameter,
        guard,
        primality=certificate,
        projection_method=certificate.method,
        factor_witness=certificate.factor_witness or proper_witness,
        composite_exponent_factor=exponent_factor,
        factored_projection=projection,
    )
    return (
        with_etale_factor(result, max_products=max_factor_products)
        if collect_etale_factor
        else result
    )


def with_etale_factor(
    result: SpecialTheoremResolution, *, max_products: int = 4096
) -> SpecialTheoremResolution:
    """Demand a separate, budgeted coefficient-gcd witness.

    This never reruns a primality recurrence or scans factors.  A proper divisor
    recovered from an unresolved candidate is itself exact composite evidence;
    a zero/non-splitting probe leaves the primality status unchanged.
    """
    if type(max_products) is not int or max_products < 0:
        raise ValueError("max_products must be a nonnegative integer")
    if result.factor_witness is not None:
        return replace(result, factor_query_status="available")
    if result.source_guard.failure_bit is False:
        return replace(result, factor_query_status="not-applicable")
    if result.composite_exponent_factor is not None:
        return replace(result, factor_query_status="available")
    if result.family == "mersenne":
        from number_compiler.sequences.power_numbers.numbers import (
            mersenne_composite_exponent_factor,
            mersenne_exponent_is_prime,
        )

        if result.parameter >= 1 << 64 or not mersenne_exponent_is_prime(
            result.parameter
        ):
            exponent_factor = mersenne_composite_exponent_factor(
                result.parameter, max_divisor=1000
            )
            return replace(
                result,
                composite_exponent_factor=exponent_factor,
                factor_query_status="available"
                if exponent_factor is not None
                else "no-split",
            )
    from number_compiler.sequences.power_numbers.etale_factor import (
        factor_probe_product_count,
        fermat_additive_etale_frobenius_probe,
        mersenne_additive_etale_frobenius_probe,
    )

    if result.family == "fermat" and result.parameter >= max_products.bit_length():
        return replace(result, factor_query_status="product-budget-exceeded")
    required = factor_probe_product_count(result.family, result.parameter)
    if required > max_products:
        return replace(result, factor_query_status="product-budget-exceeded")
    probe = (
        fermat_additive_etale_frobenius_probe(result.parameter)
        if result.family == "fermat"
        else mersenne_additive_etale_frobenius_probe(result.parameter)
    )
    factor = next(iter(probe.nontrivial_gcds), None)
    if factor is None:
        return replace(
            result,
            etale_ring_multiplications=probe.ring_multiplications,
            factor_query_status="no-split",
        )

    from number_compiler.api.sequence_types import SpecialDepthCertificateSummary

    method = "additive-etale-coefficient-gcd"
    certificate = SpecialDepthCertificateSummary(
        family_id(result.family),
        result.parameter,
        probe.candidate_modulus.bit_length(),
        "composite",
        method,
        scalable_construction=False,
        gcd_witnesses=1,
        factor_witness=factor,
    )
    return replace(
        result,
        source_guard=SpecialSourceGuard(
            result.family,
            result.parameter,
            True,
            method,
        ),
        primality=certificate,
        projection_method=method,
        factor_witness=factor,
        etale_ring_multiplications=probe.ring_multiplications,
        factor_query_status="available",
    )


__all__ = ["SpecialTheoremResolution", "resolve_special_theorem"]

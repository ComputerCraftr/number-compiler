"""Purity cost with one canonical implementation owner."""

from __future__ import annotations

from math import gcd

from devtools.experiments.power_numbers.special_successor_factor import (
    bounded_special_factor_short_circuit,
)
from devtools.experiments.power_numbers.special_successor_models import (
    PurityCandidateAudit,
    PurityWorkCost,
    TwoPrimaryPurityProbe,
)
from number_compiler.arithmetic.number_theory import normalize_jacobi_inputs


def _jacobi_counted(a: int, n: int) -> tuple[int, int]:
    a, n = normalize_jacobi_inputs(a, n)
    a %= n
    result = 1
    steps = 0
    while a:
        while not (a & 1):
            a >>= 1
            steps += 1
            if n & 7 in (3, 5):
                result = -result
        a, n = n, a
        steps += 1
        if (a & 3) == 3 and (n & 3) == 3:
            result = -result
        a %= n
    return (result if n == 1 else 0), steps


def cheap_two_primary_purity_probe(
    family: str, parameter: int
) -> TwoPrimaryPurityProbe:
    """Run only Euclidean/Jacobi/gcd evidence; never infer purity from +1/-1."""
    family = str(family)
    parameter = int(parameter)
    if family == "fermat":
        modulus = (1 << (1 << parameter)) + 1
        witness = gcd(3, modulus)
        proper = witness if 1 < witness < modulus else None
        symbol, steps = _jacobi_counted(3, modulus)
        signature: tuple[int, ...] = (symbol,)
    elif family == "mersenne":
        modulus = (1 << parameter) - 1
        witness = gcd(6, modulus)
        proper = witness if 1 < witness < modulus else None
        first, s1 = _jacobi_counted(6, modulus)
        second, s2 = _jacobi_counted(-2, modulus)
        signature = tuple(sorted((first, second)))
        steps = s1 + s2
    else:
        raise ValueError(family)
    status = "composite-witness" if proper is not None else "unknown"
    return TwoPrimaryPurityProbe(family, parameter, signature, proper, status, steps)


def cheap_purity_probe_audits() -> tuple[TwoPrimaryPurityProbe, ...]:
    return tuple(
        cheap_two_primary_purity_probe(family, parameter)
        for family, parameter in (
            ("fermat", 4),
            ("fermat", 5),
            ("mersenne", 13),
            ("mersenne", 11),
        )
    )


def _purity_cost_gate(
    parameter: int, cost: PurityWorkCost
) -> tuple[bool, tuple[str, ...]]:
    """Reject hidden recurrence/factor/CRT/discrete-log work deterministically."""
    parameter = int(parameter)
    reasons: list[str] = []
    if cost.uses_factorization:
        reasons.append("factorization")
    if cost.uses_discrete_log:
        reasons.append("discrete-log")
    if cost.reconstructs_crt:
        reasons.append("crt-reconstruction")
    if cost.sequential_image_height_work:
        reasons.append("sequential-image-height-work")
    if cost.max_extension_degree > 4:
        reasons.append("extension-degree-growth")
    # A genuinely recursive parameter-level constructor may spend O(log p)
    # sequential big-ring squarings, but not one per successor-image level.
    limit = 2 * max(1, parameter.bit_length()) + 2
    if cost.big_ring_squarings > limit:
        reasons.append(f"big-ring-squarings>{limit}")
    return not reasons, tuple(reasons)


def purity_candidate_audits() -> tuple[PurityCandidateAudit, ...]:
    from devtools.experiments.power_numbers.special_successor_purity import (
        crt_purity_audits,
    )

    rows: list[PurityCandidateAudit] = []
    fixtures = (("fermat", 4, 5), ("mersenne", 13, 11))
    probes = {(p.family, p.parameter): p for p in cheap_purity_probe_audits()}
    crt = {(r.family, r.parameter): r for r in crt_purity_audits()}
    for family, prime_parameter, composite_parameter in fixtures:
        prime_probe = probes[(family, prime_parameter)]
        composite_probe = probes[(family, composite_parameter)]
        jacobi_cost = PurityWorkCost(
            gcd_calls=1,
            reciprocity_steps=max(
                prime_probe.reciprocity_steps, composite_probe.reciprocity_steps
            ),
        )
        accepted, reasons = _purity_cost_gate(prime_parameter, jacobi_cost)
        rows.append(
            PurityCandidateAudit(
                family,
                "outer-jacobi-boundary",
                prime_parameter,
                composite_parameter,
                repr(prime_probe.outer_signature),
                repr(composite_probe.outer_signature),
                prime_probe.outer_signature != composite_probe.outer_signature,
                False,
                True,
                jacobi_cost,
                accepted,
                reasons,
            )
        )

        factor_cost = PurityWorkCost(
            gcd_calls=1,
            uses_factorization=True,
            reconstructs_crt=True,
        )
        accepted, reasons = _purity_cost_gate(prime_parameter, factor_cost)
        rows.append(
            PurityCandidateAudit(
                family,
                "factor-backed-crt-truth-audit",
                prime_parameter,
                composite_parameter,
                "pure"
                if crt[(family, prime_parameter)].pure_prime_domain_shape
                else "impure",
                "pure"
                if crt[(family, composite_parameter)].pure_prime_domain_shape
                else "impure",
                True,
                True,
                True,
                factor_cost,
                accepted,
                reasons,
            )
        )

        if family == "fermat":
            height = 1 << prime_parameter
            recurrence_cost = PurityWorkCost(
                big_ring_squarings=height - 1,
                sequential_image_height_work=True,
            )
            recurrence_name = "pepin-full-order-congruence"
        else:
            recurrence_cost = PurityWorkCost(
                big_ring_squarings=prime_parameter,
                max_extension_degree=2,
                sequential_image_height_work=True,
            )
            recurrence_name = "torus-frobenius/full-lucas-lehmer-order"
        accepted, reasons = _purity_cost_gate(prime_parameter, recurrence_cost)
        rows.append(
            PurityCandidateAudit(
                family,
                recurrence_name,
                prime_parameter,
                composite_parameter,
                "passes",
                "fails",
                True,
                True,
                True,
                recurrence_cost,
                accepted,
                reasons,
            )
        )

        short_prime = bounded_special_factor_short_circuit(family, prime_parameter)
        short_composite = bounded_special_factor_short_circuit(
            family, composite_parameter
        )
        short_cost = PurityWorkCost(
            small_ring_powered_compositions=max(
                short_prime.batched_powered_compositions,
                short_composite.batched_powered_compositions,
            ),
            candidate_product_multiplications=max(
                short_prime.product_multiplications,
                short_composite.product_multiplications,
            ),
            candidate_product_bits=max(
                short_prime.candidate_product_bits,
                short_composite.candidate_product_bits,
            ),
            gcd_calls=max(
                short_prime.product_gcd_calls, short_composite.product_gcd_calls
            ),
        )
        accepted, reasons = _purity_cost_gate(prime_parameter, short_cost)
        rows.append(
            PurityCandidateAudit(
                family,
                "sqrt-height-special-factor-product-short-circuit",
                prime_parameter,
                composite_parameter,
                short_prime.status,
                short_composite.status,
                short_prime.status != short_composite.status,
                False,
                True,
                short_cost,
                accepted,
                reasons,
            )
        )

        target_cost = PurityWorkCost(
            gcd_calls=1, reciprocity_steps=1, max_extension_degree=4
        )
        accepted, reasons = _purity_cost_gate(prime_parameter, target_cost)
        rows.append(
            PurityCandidateAudit(
                family,
                "higher-2^k-euclidean-reciprocity-target",
                prime_parameter,
                composite_parameter,
                "not-implemented",
                "not-implemented",
                False,
                False,
                False,
                target_cost,
                accepted,
                reasons,
            )
        )
    return tuple(rows)

"""Bounded exact special-form factor short-circuits used by purity audits."""

from __future__ import annotations

from math import isqrt
from typing import TYPE_CHECKING

from devtools.experiments.power_numbers.special_successor_models import (
    SpecialFactorShortCircuitAudit,
)
from devtools.verification.special_factor_reference import (
    batched_special_factor_witness,
    fermat_factor_witness,
    mersenne_factor_witness,
)
from number_compiler.arithmetic.fields.radix import bit_width

if TYPE_CHECKING:
    from devtools.verification.special_factor_reference import (
        ModularPowerWitness,
    )


def bounded_special_factor_short_circuit(
    family: str,
    parameter: int,
    *,
    candidate_budget: int | None = None,
) -> SpecialFactorShortCircuitAudit:
    """Search only the first O(sqrt(image-height)) special-form factor slots.

    Every hit is an exact composite witness.  Exhausting the bounded window is
    deliberately only ``unknown``; this is a sublinear short-circuit, not a
    primality test and not hidden factorization.
    """
    family = str(family)
    parameter = int(parameter)
    if family == "fermat":
        height = 1 << parameter
        modulus = (1 << height) + 1
        stride = 1 << (parameter + 2)

        def make_candidate(k: int) -> int:
            return stride * k + 1

        def witness_fn(
            q: int,
        ) -> ModularPowerWitness:
            return fermat_factor_witness(parameter, q)
    elif family == "mersenne":
        height = parameter
        modulus = (1 << parameter) - 1
        stride = 2 * parameter

        def make_candidate(k: int) -> int:
            return stride * k + 1

        def witness_fn(
            q: int,
        ) -> ModularPowerWitness:
            return mersenne_factor_witness(parameter, q)
    else:
        raise ValueError(family)
    budget = (
        (isqrt(height - 1) + 1) if candidate_budget is None else int(candidate_budget)
    )
    if budget < 0:
        raise ValueError(budget)
    tested = compositions = max_bits = 0
    witness_k = witness_factor = None
    for k in range(1, budget + 1):
        candidate = int(make_candidate(k))
        if candidate >= modulus:
            break
        result = witness_fn(candidate)
        tested += 1
        compositions += int(result.compositions)
        max_bits = max(max_bits, bit_width(candidate))
        if result.stride_compatible and result.divides:
            witness_k = k
            witness_factor = candidate
            break
    batch = batched_special_factor_witness(family, parameter, budget)
    batch_status = "composite-witness" if batch.composite_witness else "unknown"
    if batch_status != (
        "composite-witness" if witness_factor is not None else "unknown"
    ):
        raise AssertionError((family, parameter, witness_factor, batch))
    return SpecialFactorShortCircuitAudit(
        family,
        parameter,
        height,
        budget,
        tested,
        compositions,
        witness_k,
        witness_factor,
        "composite-witness" if witness_factor is not None else "unknown",
        False,
        max_bits,
        batch.powered_compositions,
        batch.product_multiplications,
        batch.product_depth,
        batch.gcd_calls,
        batch.candidate_product_bits,
        (batch.proper_factor == witness_factor)
        if witness_factor is not None
        else batch.proper_factor is None,
    )


def special_factor_short_circuit_audits() -> tuple[SpecialFactorShortCircuitAudit, ...]:
    return tuple(
        bounded_special_factor_short_circuit(family, parameter)
        for family, parameter in (
            ("fermat", 4),
            ("fermat", 5),
            ("mersenne", 13),
            ("mersenne", 11),
        )
    )

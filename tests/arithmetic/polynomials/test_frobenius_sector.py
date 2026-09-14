"""Certified source bounds for the reverse/add Frobenius sector product."""

from __future__ import annotations

from typing import cast

import pytest

from number_compiler.arithmetic.polynomials.cyclotomic_transport import (
    power_two_cyclotomic_transport,
)
from number_compiler.arithmetic.polynomials.frobenius_sector import (
    DECIMAL_REVERSE_GROWTH_CERTIFICATE,
    FrobeniusSectorSourceBound,
    ReverseFrobeniusPlan,
    ReverseGrowthRunCertificate,
)


def test_sector_lower_bound_is_sound_for_every_growth_split() -> None:
    bits = 5
    for classes in (1, 2, 4, 8):
        for steps in range(65):
            bound = FrobeniusSectorSourceBound.for_steps(classes, bits, steps)
            for growth in range(steps + 1):
                transport = power_two_cyclotomic_transport(
                    classes,
                    steps - growth,
                    growth,
                )
                effective_valuation = (
                    bits if transport.annihilated(bits) else transport.scalar_v2
                )
                assert effective_valuation >= bound.valuation_lower_bound


def test_plan_composition_is_canonical_associative_and_fixed_arity() -> None:
    plans = tuple(
        ReverseFrobeniusPlan.for_steps(
            maximum_classes=8,
            bits=5,
            steps=steps,
        )
        for steps in (3, 7, 11)
    )
    left = plans[0].then(plans[1]).then(plans[2])
    right = plans[0].then(plans[1].then(plans[2]))
    direct = ReverseFrobeniusPlan.for_steps(
        maximum_classes=8,
        bits=5,
        steps=21,
    )
    assert left == right == direct
    assert tuple(sector.classes for sector in direct.sectors) == (1, 2, 4, 8)
    assert len(left.sectors) == len(plans[0].sectors)


def test_plan_proves_source_death_per_sector_without_output_claims() -> None:
    plan = ReverseFrobeniusPlan.for_steps(
        maximum_classes=8,
        bits=5,
        steps=20,
        growth_certificate=DECIMAL_REVERSE_GROWTH_CERTIFICATE,
    )
    assert plan.annihilated_sectors == (True, True, True, True)
    assert plan.all_source_sectors_annihilated
    assert not hasattr(plan, "innovation")
    assert not hasattr(plan, "output")
    assert not hasattr(plan, "source")
    assert not hasattr(plan, "digits")


def test_outer_growth_certificate_is_the_exact_finite_kernel_proof_graph() -> None:
    certificate = ReverseGrowthRunCertificate.for_base(10)
    assert certificate is not DECIMAL_REVERSE_GROWTH_CERTIFICATE
    assert certificate == DECIMAL_REVERSE_GROWTH_CERTIFICATE
    assert certificate.outer_successors == tuple(
        (symbol, 1 + symbol - 10 * int(symbol >= 10)) for symbol in range(9, 19)
    )
    assert dict(certificate.outer_successors)[18] == 9
    assert dict(certificate.outer_successors)[9] == 10
    assert dict(certificate.outer_successors)[10] == 1
    with pytest.raises(ValueError, match="base>=3"):
        ReverseGrowthRunCertificate.for_base(2)


def test_certified_uniform_bound_is_distinct_from_generic_growth_words() -> None:
    generic = ReverseFrobeniusPlan.for_steps(maximum_classes=8, bits=5, steps=20)
    certified = ReverseFrobeniusPlan.for_steps(
        maximum_classes=8,
        bits=5,
        steps=20,
        growth_certificate=DECIMAL_REVERSE_GROWTH_CERTIFICATE,
    )
    assert not generic.all_source_sectors_annihilated
    assert certified.all_source_sectors_annihilated
    assert all(
        sector.uniform_no_growth_lower_bound == 5 for sector in certified.sectors
    )


def test_certified_sector_bound_is_sound_for_every_permitted_growth_split() -> None:
    bits = 5
    for steps in range(65):
        plan = ReverseFrobeniusPlan.for_steps(
            maximum_classes=8,
            bits=bits,
            steps=steps,
            growth_certificate=DECIMAL_REVERSE_GROWTH_CERTIFICATE,
        )
        minimum_no_growth = steps // 4
        for sector in plan.sectors:
            for no_growth in range(minimum_no_growth, steps + 1):
                transport = power_two_cyclotomic_transport(
                    sector.classes,
                    no_growth,
                    steps - no_growth,
                )
                effective_valuation = (
                    bits if transport.annihilated(bits) else transport.scalar_v2
                )
                assert effective_valuation >= sector.valuation_lower_bound


@pytest.mark.parametrize(
    "invalid",
    (True, 1.5),
)
def test_plan_rejects_numeric_aliases_before_construction(invalid: object) -> None:
    with pytest.raises(TypeError):
        ReverseFrobeniusPlan.for_steps(
            maximum_classes=8,
            bits=5,
            steps=cast(int, invalid),
        )


def test_plan_rejects_noncanonical_sector_payloads() -> None:
    valid = ReverseFrobeniusPlan.for_steps(
        maximum_classes=4,
        bits=5,
        steps=9,
    )
    with pytest.raises(ValueError, match="sector count"):
        ReverseFrobeniusPlan(4, 5, 9, valid.sectors[:-1])
    with pytest.raises(ValueError, match="invalid reverse Frobenius plan"):
        ReverseFrobeniusPlan.for_steps(
            maximum_classes=16,
            bits=5,
            steps=9,
        )

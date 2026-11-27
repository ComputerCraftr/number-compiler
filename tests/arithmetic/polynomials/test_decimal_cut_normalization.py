from __future__ import annotations

import pytest

from number_compiler.arithmetic.carry.carry_normalization import (
    NormalizationDefect,
    linear_normalization_defect,
)
from number_compiler.arithmetic.polynomials.cyclotomic_family import (
    normalization_component,
)
from number_compiler.arithmetic.polynomials.cyclotomic_ring import CyclotomicRing
from number_compiler.arithmetic.polynomials.digit_cyclotomic import CyclotomicDigitBlock


@pytest.mark.parametrize("order,power", [(1, 1), (1, 3), (3, 2), (11, 1), (31, 1)])
@pytest.mark.parametrize("incoming", [-5, 0, 7])
def test_signed_decimal_cut_and_direct_division_match_literal(
    order: int, power: int, incoming: int
) -> None:
    raw = (-14, 0, 17, 99, -3, 8, 29)
    defect = linear_normalization_defect(raw, base=10, boundary_in=incoming)
    component = normalization_component(defect, order=order, modulus=32, power=power)
    expected = CyclotomicDigitBlock.from_coefficients(
        defect.boundary_term_lsf,
        order=order,
        modulus=32,
        power=power,
        length=defect.length + 1,
    )
    assert component.boundary == expected
    assert component.identity_holds
    assert component.carry_recovered_exactly


def test_direct_division_preserves_identity_and_refuses_nonunits() -> None:
    identity = CyclotomicDigitBlock.from_coefficients(
        (7, 14), order=1, modulus=32, factor=(-9, 1)
    )
    assert identity.divide_linear_factor(10) is identity
    singular = CyclotomicDigitBlock.from_coefficients(
        (3,), order=1, modulus=32, factor=(2, 1)
    )
    with pytest.raises(ValueError, match="nonunit-linear-normalization"):
        singular.divide_linear_factor(10)


@pytest.mark.parametrize("order,power", [(1, 1), (3, 2), (11, 1), (31, 1)])
def test_direct_division_matches_inverse_without_dense_multiplication(
    order: int, power: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    block = CyclotomicDigitBlock.from_coefficients(
        (-3, 42, 0, 9, -11, 27), order=order, modulus=32, power=power
    )
    expected = block.ring.multiply(
        block.residue, block.linear_factor_inverse_residue(10)
    )

    def refuse_dense(*_args: object, **_kwargs: object) -> tuple[int, ...]:
        raise AssertionError("direct division multiplied the dense inverse")

    monkeypatch.setattr(CyclotomicRing, "multiply", refuse_dense)
    result = block.divide_linear_factor(10)
    assert result.residue == expected


def test_decimal_cut_rejects_unrelated_width() -> None:
    source = CyclotomicDigitBlock.identity(order=3, modulus=32)
    with pytest.raises(ValueError, match="invalid decimal mod-32 cut"):
        source.decimal_cut_boundary(width=3, incoming=1, outgoing=2)


def test_decimal_component_does_not_expand_the_cut_boundary(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    defect = linear_normalization_defect((9, 31, 8, -2), base=10, boundary_in=-4)

    def forbid_boundary(_defect: NormalizationDefect) -> tuple[int, ...]:
        raise AssertionError("projected decimal cut expanded the boundary")

    monkeypatch.setattr(
        NormalizationDefect, "boundary_term_lsf", property(forbid_boundary)
    )
    component = normalization_component(defect, order=11, modulus=32)
    assert component.identity_holds
    assert component.carry_recovered_exactly


def test_large_cyclotomic_cut_uses_exact_monomial_without_ring_power(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    defect = linear_normalization_defect(
        tuple((index * index + 7 * index) % 123 - 61 for index in range(512)),
        base=10,
        boundary_in=-4,
    )

    def refuse_power(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("canonical monomial invoked general ring powering")

    monkeypatch.setattr(CyclotomicRing, "power_residue", refuse_power)
    component = normalization_component(defect, order=257, modulus=32)
    assert component.identity_holds
    assert component.carry_recovered_exactly
    assert component.boundary.residue[255] == defect.boundary_out % 32


@pytest.mark.parametrize("factor,power", [(None, 2), ((1, 1), 1)])
def test_jet_and_custom_factor_retain_exact_z_power(
    factor: tuple[int, ...] | None, power: int
) -> None:
    block = CyclotomicDigitBlock.identity(
        order=3, modulus=32, factor=factor, power=power
    )
    expected = block.ring.power_residue(block.ring.reduce((0, 1)), 3).value
    assert expected != block.ring.one
    assert block.z_power_residue(3) == expected

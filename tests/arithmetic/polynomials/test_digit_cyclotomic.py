from __future__ import annotations

from typing import TypedDict

import pytest

from number_compiler.arithmetic.carry.carry_normalization import (
    linear_normalization_defect,
)
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.arithmetic.polynomials.cyclotomic_carry import (
    CarryCyclotomicTransducer,
)
from number_compiler.arithmetic.polynomials.cyclotomic_factor import (
    cyclotomic_factors_mod_prime,
    multiplicative_order_mod,
)
from number_compiler.arithmetic.polynomials.cyclotomic_family import (
    collatz_cyclotomic_step,
    collatz_piecewise_cyclotomic_step,
    fermat_cyclotomic_step,
    mersenne_cyclotomic_step,
    normalization_component,
    reverse_add_cyclotomic_step,
)
from number_compiler.arithmetic.polynomials.digit_cyclotomic import CyclotomicDigitBlock
from number_compiler.arithmetic.polynomials.polynomial import (
    polynomial_multiply,
    polynomial_remainder_monic,
)


class _CarryArguments(TypedDict):
    base: int
    incoming_min: int
    incoming_max: int
    order: int
    modulus: int


def test_projection_and_source_digit_cyclotomic_blocks_have_one_canonical_class() -> (
    None
):
    import number_compiler

    assert not hasattr(number_compiler, "CyclotomicJetBlock")
    assert not hasattr(number_compiler, "CyclotomicProjectionBlock")
    assert not hasattr(number_compiler, "cyclotomic_projection_from_runs")
    assert not hasattr(number_compiler, "cyclotomic_projection_from_values")


def test_carry_cyclotomic_transducer_composes_without_retaining_carry_vector() -> None:
    coefficients = (3, 5, -1, 7, 2, -3, 4)
    left, right = coefficients[:4], coefficients[4:]
    kwargs: _CarryArguments = {
        "base": 3,
        "incoming_min": -3,
        "incoming_max": 5,
        "order": 4,
        "modulus": 8,
    }
    a = CarryCyclotomicTransducer.from_coefficients(left, **kwargs)
    b = CarryCyclotomicTransducer.from_coefficients(right, **kwargs)
    composed = a.then(b)
    direct = CarryCyclotomicTransducer.from_coefficients(coefficients, **kwargs)
    assert composed.action.outgoing == direct.action.outgoing
    assert composed.emissions == direct.emissions
    # No coefficient field or materialized boundary itinerary is retained.
    assert all(
        "coefficient" not in name and "boundaries" not in name
        for name in composed.__dataclass_fields__
    )


def test_carry_cyclotomic_transducer_binary_power_is_exact() -> None:
    coefficients = (1, 0, 0)
    kwargs: _CarryArguments = {
        "base": 2,
        "incoming_min": 0,
        "incoming_max": 1,
        "order": 4,
        "modulus": 8,
    }
    one = CarryCyclotomicTransducer.from_coefficients(coefficients, **kwargs)
    powered = one.power_block(7)
    direct = CarryCyclotomicTransducer.from_coefficients(coefficients * 7, **kwargs)
    assert powered.action.outgoing == direct.action.outgoing
    assert powered.emissions == direct.emissions
    assert powered.compositions <= 2 * (7).bit_length()


def test_finite_field_cyclotomic_factorization_exposes_deeper_primary_components() -> (
    None
):
    assert multiplicative_order_mod(2, 31) == 5
    factors = cyclotomic_factors_mod_prime(31, 2)
    assert len(factors) == 6
    assert {len(factor) - 1 for factor in factors} == {5}
    assert cyclotomic_factors_mod_prime(7, 2) == (
        (1, 0, 1, 1),
        (1, 1, 0, 1),
    )
    whole = CyclotomicDigitBlock.from_coefficients(
        digits_lsd(93, 2, 7),
        order=7,
        modulus=2,
        length=7,
    )
    components = whole.finite_field_components()
    assert [component.degree for component in components] == [3, 3]
    assert CyclotomicDigitBlock.from_finite_field_components(
        tuple(reversed(components))
    ).equivalent(whole)


def test_reverse_pair_and_collatz_radix_affine_are_exact_in_same_digit_module() -> None:
    reverse = reverse_add_cyclotomic_step(196, base=10, order=7, modulus=16)
    assert reverse.exact
    assert reverse.normalization.carry_recovered_exactly

    binary = collatz_cyclotomic_step(27, base=2, order=7, modulus=16)
    ternary = collatz_cyclotomic_step(27, base=3, order=7, modulus=16)
    assert binary.exact and ternary.exact
    assert binary.normalization.carry_recovered_exactly
    assert ternary.normalization.carry_recovered_exactly
    # 3 has radix polynomial 1+z in base 2, but z in base 3.
    source2 = CyclotomicDigitBlock.from_coefficients(
        digits_lsd(27, 2),
        order=7,
        modulus=16,
    )
    assert source2.radix_affine(multiplier=3, addend=1, base=2).equivalent(binary.raw)
    source3 = CyclotomicDigitBlock.from_coefficients(
        digits_lsd(27, 3),
        order=7,
        modulus=16,
    )
    assert source3.radix_affine(multiplier=3, addend=1, base=3).equivalent(ternary.raw)
    assert binary.accelerated is not None


def test_collatz_piecewise_cyclotomic_successor_selects_its_own_branch() -> None:
    for value in range(1, 257):
        step = collatz_piecewise_cyclotomic_step(value, order=8, modulus=32)
        expected = value // 2 if value % 2 == 0 else 3 * value + 1
        assert step.target_value == expected
        assert step.branch == ("divide_2" if value % 2 == 0 else "multiply_3_add_1")
        assert step.exact
        if value % 2 == 0:
            assert step.odd_detail is None
        else:
            assert (
                step.odd_detail is not None
                and step.odd_detail.normalization.identity_holds
            )


def test_base_minus_z_unit_recovers_carry_component_without_retaining_carry_state() -> (
    None
):
    raw = (7, 12, 8, 15, 3, 0)
    defect = linear_normalization_defect(raw, base=10)
    for order in range(1, 13):
        component = normalization_component(defect, order=order, modulus=32)
        assert component.normalization_factor_is_unit
        assert component.carry_recovered_exactly


def test_reverse_add_linear_binomial_transport_powers_inside_component() -> None:
    block = CyclotomicDigitBlock.from_coefficients(
        (2, 7, 11, 4, 1),
        order=8,
        modulus=32,
    )
    q, r = 5, 13
    powered = block.reverse_add_linear_transport(no_growth=q, growth=r)
    kernel: tuple[int, ...] = (1,)
    for _ in range(r):
        kernel = polynomial_multiply(kernel, (1, 1))
    expanded = polynomial_multiply(block.residue, tuple((1 << q) * x for x in kernel))
    expected = polynomial_remainder_monic(
        expanded, block.divisor, modulus=block.modulus
    )
    assert powered.residue == expected
    assert powered.length == block.length + r


def test_special_number_raw_squares_use_the_same_cyclotomic_module() -> None:
    for state in range(31):
        step = mersenne_cyclotomic_step(state, 5, coefficient_modulus=2)
        assert step.exact
        assert step.normalization.carry_recovered_exactly
    for state in range(17):
        step = fermat_cyclotomic_step(state, 2, coefficient_modulus=3, factor_index=0)
        assert step.exact


def test_m7_finite_factors_are_smaller_but_normalization_couples_them() -> None:
    p = 7
    modulus = (1 << p) - 1
    factors = cyclotomic_factors_mod_prime(p, 2)
    assert len(factors) == 2

    def key(state: int, selected: tuple[int, ...]) -> tuple[tuple[int, ...], ...]:
        digits = digits_lsd(state, 2, p)
        return tuple(
            CyclotomicDigitBlock.from_coefficients(
                digits,
                order=p,
                modulus=2,
                factor=factors[index],
                length=p,
            ).residue
            for index in selected
        )

    def closure(selected: tuple[int, ...]) -> tuple[int, int, bool]:
        transitions: dict[tuple[tuple[int, ...], ...], tuple[tuple[int, ...], ...]] = {}
        outputs: dict[tuple[tuple[int, ...], ...], bool] = {}
        conflicts = 0
        target_ok = True
        for state in range(modulus):
            current = key(state, selected)
            nxt = key((state * state - 2) % modulus, selected)
            old = transitions.setdefault(current, nxt)
            conflicts += int(old != nxt)
            output = state == 0
            if current in outputs:
                target_ok &= outputs[current] == output
            else:
                outputs[current] = output
        return len(transitions), conflicts, target_ok

    left = closure((0,))
    right = closure((1,))
    whole = closure((0, 1))
    assert left[0] == right[0] == 8
    assert left[1] > 0 and right[1] > 0
    assert not left[2] and not right[2]
    # Together they recover the known Phi_7/sign quotient: 127 -> 64 classes.
    assert whole == (64, 0, True)


@pytest.mark.validation  # Full cross-family cyclotomic research report.
def test_unified_research_metrics_lock_cross_family_nonduplication_and_factor_closure() -> (
    None
):
    from devtools.experiments.algebra.digit_cyclotomic_unification import (
        unified_digit_cyclotomic_metrics,
    )

    metrics = unified_digit_cyclotomic_metrics()
    assert metrics.single_canonical_digit_block
    assert metrics.all_exact
    dependencies = {(row.family, row.base): row for row in metrics.carry_dependency}
    assert dependencies[("reverse-add", 10)].recovered_components == 4096
    assert dependencies[("reverse-add", 10)].components == 4096
    assert dependencies[("collatz", 2)].recovered_components == 656
    assert dependencies[("collatz", 2)].components == 656
    assert dependencies[("collatz", 3)].recovered_components == 451
    assert metrics.mersenne31_factor_count == 6
    assert metrics.mersenne31_factor_degree == 5
    m7 = [row for row in metrics.factor_closure if row.family == "mersenne"]
    assert [
        (row.selected_factors, row.classes, row.conflicts, row.target_separating)
        for row in m7
    ] == [
        ((0,), 8, 108, False),
        ((1,), 8, 106, False),
        ((0, 1), 64, 0, True),
    ]


def test_canonical_affine_morphism_unifies_powered_family_linear_maps() -> None:
    from number_compiler.arithmetic.polynomials.cyclotomic_affine import (
        CyclotomicAffineMorphism,
    )
    from number_compiler.arithmetic.polynomials.digit_cyclotomic import (
        CyclotomicDigitBlock,
    )

    block = CyclotomicDigitBlock.from_coefficients((1, 0, 1, 1), order=8, modulus=32)
    # Binary Collatz raw map 3*x+1 == (1+z)x+1.
    collatz = CyclotomicAffineMorphism.from_polynomials(block, (1, 1), (1,))
    assert collatz.apply(block, result_length=block.length + 1).equivalent(
        block.radix_affine(multiplier=3, addend=1, base=2)
    )
    # Repeated reverse-add growth multiplier is one powered map rather than r ad-hoc products.
    growth = CyclotomicAffineMorphism.from_polynomials(block, (1, 1), (0,)).power_map(7)
    via_ir = growth.apply(block, result_length=block.length + 7)
    direct = block.multiply_polynomial_power((1, 1), 7, length_growth=1)
    assert via_ir.equivalent(direct) and via_ir.length == direct.length
    assert growth.compositions <= 2 * (7).bit_length()
    # Identity powers do not add fake charged work.
    assert CyclotomicAffineMorphism.identity_for(block).apply(block) is block

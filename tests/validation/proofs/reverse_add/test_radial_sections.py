"""Finite Laurent checks for the formal modular radial-section rewrite."""

from __future__ import annotations

from collections.abc import Mapping
from math import comb
from typing import cast

import pytest

from devtools.experiments.reverse_add.radial_sections import (
    MAX_RADIAL_SECTION_BITS,
    RadialSectionContribution,
    RadialSectionOperator,
    construct_radial_section,
)
from number_compiler.arithmetic.fields.radial_innovation import (
    InnovationID,
    RadialMultiplier,
)
from number_compiler.arithmetic.fields.symbolic_innovation import (
    SymbolicInnovationArena,
)
from number_compiler.resources.ledger import ResourceLedger

Laurent = dict[int, int]


def _add(first: Mapping[int, int], second: Mapping[int, int], modulus: int) -> Laurent:
    result = {
        exponent: coefficient % modulus for exponent, coefficient in first.items()
    }
    for exponent, coefficient in second.items():
        result[exponent] = (result.get(exponent, 0) + coefficient) % modulus
    return {
        exponent: coefficient for exponent, coefficient in result.items() if coefficient
    }


def _multiply(
    first: Mapping[int, int], second: Mapping[int, int], modulus: int
) -> Laurent:
    result: Laurent = {}
    for left_exponent, left_coefficient in first.items():
        for right_exponent, right_coefficient in second.items():
            exponent = left_exponent + right_exponent
            result[exponent] = (
                result.get(exponent, 0) + left_coefficient * right_coefficient
            ) % modulus
    return {
        exponent: coefficient for exponent, coefficient in result.items() if coefficient
    }


def _power_h(exponent: int, modulus: int) -> Laurent:
    result: Laurent = {0: 1}
    factor: Laurent = {0: 1, 1: 1}
    power = exponent
    while power:
        if power & 1:
            result = _multiply(result, factor, modulus)
        power >>= 1
        if power:
            factor = _multiply(factor, factor, modulus)
    return result


def _section(value: Mapping[int, int], lane: int, modulus: int) -> Laurent:
    return {
        (exponent - lane) // 2: coefficient % modulus
        for exponent, coefficient in value.items()
        if exponent % 2 == lane and coefficient % modulus
    }


def _evaluate(operator: RadialSectionOperator, source: Mapping[int, int]) -> Laurent:
    modulus = operator.modulus
    children = (_section(source, 0, modulus), _section(source, 1, modulus))
    result: Laurent = {}
    for term in operator.contributions:
        radial = _power_h(term.growth, modulus)
        child = {
            exponent + term.shift: coefficient
            for exponent, coefficient in children[term.child_lane].items()
        }
        contribution = _multiply(radial, child, modulus)
        scale = term.coefficient * (1 << term.no_growth)
        contribution = {
            exponent: coefficient * scale % modulus
            for exponent, coefficient in contribution.items()
        }
        result = _add(result, contribution, modulus)
    return result


@pytest.mark.parametrize("bits", [1, 2, 5, 8])
@pytest.mark.parametrize("q,r", [(0, 0), (0, 1), (1, 4), (2, 5), (3, 9)])
@pytest.mark.parametrize("lane", [0, 1])
def test_radial_sections_match_bounded_laurent_reference(
    bits: int, q: int, r: int, lane: int
) -> None:
    source = {-4: 7, -3: -5, -1: 11, 0: 2, 2: -9, 5: 3}
    modulus = 1 << bits
    operator = construct_radial_section(bits=bits, q=q, r=r, lane=lane)
    exact = _multiply(_power_h(r, modulus), source, modulus)
    exact = {
        exponent: coefficient * (1 << q) % modulus
        for exponent, coefficient in exact.items()
    }
    assert _evaluate(operator, source) == _section(exact, lane, modulus)
    assert operator.term_visits <= 2 * bits
    assert len(operator.contributions) <= operator.term_visits
    assert operator.modular_product_calls == 2 * operator.binomial_factor_steps
    assert operator.modular_inverse_calls == operator.binomial_factor_steps
    assert not operator.is_source_authority


def test_huge_exponent_retains_only_bounded_formal_terms() -> None:
    exponent = 1 << 512
    for lane in (0, 1):
        operator = construct_radial_section(bits=5, q=0, r=exponent, lane=lane)
        assert operator.r == exponent
        assert operator.term_visits == 5
        assert len(operator.contributions) <= 5
        assert operator.binomial_factor_steps <= sum(range(5))
        assert operator.inspected_operand_bits < 20_000


def test_odd_exponent_uses_at_most_two_terms_per_precision_level() -> None:
    operator = construct_radial_section(bits=5, q=0, r=(1 << 512) + 1, lane=1)
    assert operator.term_visits == 10
    assert len(operator.contributions) <= 10
    assert {term.child_lane for term in operator.contributions} == {0, 1}


def test_power_of_two_factor_annihilates_the_modular_operator() -> None:
    operator = construct_radial_section(bits=5, q=5, r=1 << 4096, lane=0)
    assert operator.is_zero
    assert operator.term_visits == 0
    assert operator.inspected_operand_bits == 0


@pytest.mark.parametrize("bits", [1, 5, 16])
@pytest.mark.parametrize("half", [0, 1, 15, 127, (1 << 257) - 17, (1 << 512) + 1001])
def test_normalized_terms_agree_with_exact_small_index_binomials(
    bits: int, half: int
) -> None:
    # The reference constructs only <=16 integer binomials. It does not
    # expand a polynomial of degree half and does not reuse the valuation
    # or odd-denominator inverse algorithm from the implementation.
    for q in (0, 1, 4, 15, 16):
        for odd in (0, 1):
            for lane in (0, 1):
                operator = construct_radial_section(
                    bits=bits, q=q, r=2 * half + odd, lane=lane
                )
                expected: list[RadialSectionContribution] = []
                for j in range(min(max(bits - q, 0), half + 1)):
                    coefficient = (comb(half, j) * (1 << (q + j))) % (1 << bits)
                    if coefficient == 0:
                        continue
                    valuation = 0
                    while coefficient % 2 == 0:
                        valuation += 1
                        coefficient //= 2
                    for t in range(odd + 1):
                        for child in (0, 1):
                            exponent = j + t + child
                            if exponent % 2 == lane:
                                expected.append(
                                    RadialSectionContribution(
                                        coefficient,
                                        (exponent - lane) // 2,
                                        valuation,
                                        half - j,
                                        child,
                                    )
                                )
                assert operator.contributions == tuple(expected)


def test_constant_term_count_does_not_claim_constant_integer_work() -> None:
    small = construct_radial_section(bits=5, q=0, r=1 << 32, lane=0)
    large = construct_radial_section(bits=5, q=0, r=1 << 512, lane=0)
    assert small.term_visits == large.term_visits == 5
    assert small.inspected_operand_bits < large.inspected_operand_bits


@pytest.mark.parametrize(
    "arguments,exception",
    [
        ({"bits": True, "q": 0, "r": 0, "lane": 0}, TypeError),
        ({"bits": 0, "q": 0, "r": 0, "lane": 0}, ValueError),
        (
            {"bits": MAX_RADIAL_SECTION_BITS + 1, "q": 0, "r": 0, "lane": 0},
            ValueError,
        ),
        ({"bits": 5, "q": -1, "r": 0, "lane": 0}, ValueError),
        ({"bits": 5, "q": 0, "r": -1, "lane": 0}, ValueError),
        ({"bits": 5, "q": 0, "r": 0, "lane": 2}, ValueError),
    ],
)
def test_invalid_operator_inputs_fail_closed(
    arguments: dict[str, int], exception: type[Exception]
) -> None:
    with pytest.raises(exception):
        construct_radial_section(**arguments)


def test_descriptor_rejects_even_unabsorbed_coefficient() -> None:
    contribution = RadialSectionContribution(2, 0, 0, 0, 0)
    with pytest.raises(ValueError, match="absorbed"):
        RadialSectionOperator(5, 0, 0, 0, (contribution,), 1, 0, 0)


def test_modular_annihilation_cannot_publish_an_exact_integer_innovation() -> None:
    operator = construct_radial_section(bits=5, q=5, r=0, lane=0)
    assert operator.is_zero
    arena = SymbolicInnovationArena(ResourceLedger())
    with pytest.raises(TypeError, match="symbolic innovation ID"):
        arena.action(RadialMultiplier(), cast(InnovationID, operator))

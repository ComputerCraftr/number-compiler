"""Exact source-root duration-doubling is not a guessed carry-driver repeat."""

import builtins
from dataclasses import replace
from typing import TypedDict
from unittest.mock import patch

import pytest

from number_compiler.sequences.power_numbers.numbers import FermatNumberSpec
from number_compiler.sequences.power_numbers.three_power_temporal_source_morphism import (
    certify_phase_square_carries,
    cyclic_square_coefficients,
    demand_fermat_source_temporal_morphism,
)
from tests.support.exact_integer_power import exact_integer_power


def _full_bit_square_histograms(
    number: int, fold_width: int
) -> tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]]:
    """Independent *small reference* all-position convolution/carry witness."""
    length = number.bit_length()
    bits = [(number >> j) & 1 for j in range(length)]
    raw = [0] * (2 * length + 4)
    for i, b in enumerate(bits):
        if b:
            for j, c in enumerate(bits):
                if c:
                    raw[i + j] += 1
    period = 2 * fold_width
    source = [0] * period
    out = [0] * period
    ingress = [0] * period
    for j, b in enumerate(bits):
        source[j % period] += b
    carry = 0
    for j, coefficient in enumerate(raw):
        ingress[j % period] += carry
        summand = coefficient + carry
        out[j % period] += summand & 1
        carry = summand >> 1
    assert carry == 0
    return tuple(source), tuple(out), tuple(ingress)


class _SourceWindowOptions(TypedDict):
    phase_binary_places: int
    phase_decimal_places: int
    low_binary_places: int
    low_decimal_places: int
    high_binary_places: int
    high_decimal_places: int


def _small_source_window_options() -> _SourceWindowOptions:
    return {
        "phase_binary_places": 4,
        "phase_decimal_places": 1,
        "low_binary_places": 3,
        "low_decimal_places": 1,
        "high_binary_places": 2,
        "high_decimal_places": 1,
    }


def test_true_endpoint_root_temporal_square_f5() -> None:
    spec = FermatNumberSpec(5)
    first = spec.demand_three_power_temporal_source_morphism(27)
    assert first.producer_verified
    squared = first.square(spec)
    again = squared.square(spec)
    direct = first.power_of_two(spec, 2)
    assert (first.source_level, first.target_level) == (27, 28)
    assert (squared.source_level, squared.target_level) == (27, 29)
    assert (again.source_level, again.target_level) == (27, 31)
    assert (direct.source_level, direct.target_level) == (27, 31)
    assert again.producer_verified and direct.producer_verified
    assert again.first is first.first
    assert again.last.outer_inner.clock.level == 31
    assert again.last.outer_inner.clock.residue9900 == 6561
    forced_block = again.last.outer_inner.forced_single_block
    assert forced_block is not None and forced_block.residue == 781
    assert again.signed_phase_status == "OPEN_CARRY_HISTOGRAM"
    assert not again.all_inner_carries_certified
    assert again.exact_signed_root is None
    assert again.terminal_status == "UNKNOWN"
    assert again.last.outer_inner.unknown_blocks


def test_adjacent_temporal_action_needs_same_actual_issued_endpoint() -> None:
    spec = FermatNumberSpec(4)
    a = spec.demand_three_power_temporal_source_morphism(13)
    second = demand_fermat_source_temporal_morphism(spec, 14, known_first=a.last)
    assert a.then(second).producer_verified
    independent = spec.demand_three_power_temporal_source_morphism(14)
    assert independent.producer_verified
    with pytest.raises(ValueError, match="actual previous endpoint"):
        a.then(independent)
    with pytest.raises(ValueError, match="foreign"):
        a.square(FermatNumberSpec(5))
    with pytest.raises(ValueError, match="unissued"):
        replace(a).square(spec)
    with pytest.raises(ValueError, match="unissued"):
        replace(a, dyadic_steps=2).then(second)
    with pytest.raises(ValueError, match="unissued/foreign"):
        demand_fermat_source_temporal_morphism(spec, 14, known_first=a.first)
    with pytest.raises(ValueError, match="exceeds"):
        spec.demand_three_power_temporal_source_morphism(15)


def test_normalized_histogram_square_requires_full_carry_emissions() -> None:
    w = 4
    for x in (3, 3**8, 3**16, 3**32, 513):
        source, target, carries = _full_bit_square_histograms(x, w)
        certify_phase_square_carries(source, target, carries)
        raw = cyclic_square_coefficients(source)
        assert sum(raw[r] * pow(2, r, 17) for r in range(8)) % 17 == (x * x) % 17
        wrong = list(carries)
        wrong[0] += 1
        with pytest.raises(ArithmeticError, match="phase"):
            certify_phase_square_carries(source, target, tuple(wrong))
    a, a2, ac = _full_bit_square_histograms(3, w)
    b, b2, bc = _full_bit_square_histograms(513, w)
    # Exact same 2w source histogram but different NORMALIZED output histogram.
    assert a == b and a2 != b2 and ac != bc
    assert (3 - 513) % 17 == 0
    assert (9 - (513 * 513)) % 17 == 0
    assert a2 == (1, 0, 0, 1, 0, 0, 0, 0)
    assert b2 == (1, 0, 2, 0, 0, 0, 0, 0)


def test_issued_one_step_root_consumes_exact_normalized_square_response() -> None:
    spec = FermatNumberSpec(3)
    action = demand_fermat_source_temporal_morphism(
        spec, 3, 1, **_small_source_window_options()
    )
    source = 3**8
    response = action.normalized_square_response(source)
    expected = _full_bit_square_histograms(source, response.fold_width)

    assert response.producer_verified
    assert response.source == source
    assert response.target == source * source == 3**16
    assert (
        response.source_counts,
        response.target_counts,
        response.ingress_counts,
    ) == expected
    assert response.next_source_admitted
    assert response.scalar_products == response.convolution.scalar_multiplications


def test_normalized_square_response_refuses_unadmitted_or_over_budget_work() -> None:
    spec = FermatNumberSpec(3)
    options = _small_source_window_options()
    action = demand_fermat_source_temporal_morphism(spec, 3, 1, **options)
    with pytest.raises(ValueError, match="outside"):
        action.normalized_square_response(3**8 + 1)
    with pytest.raises(ValueError, match="source square"):
        action.normalized_square_response(3**8, max_source_bits=8)
    with pytest.raises(ValueError, match="cross-term"):
        action.normalized_square_response(3**8, max_products=1)
    multi_step = demand_fermat_source_temporal_morphism(spec, 3, 2, **options)
    with pytest.raises(ValueError, match="one temporal step"):
        multi_step.normalized_square_response(3**8)


def test_normalized_square_response_is_bound_to_its_source_and_result() -> None:
    spec = FermatNumberSpec(3)
    action = demand_fermat_source_temporal_morphism(
        spec, 3, 1, **_small_source_window_options()
    )
    response = action.normalized_square_response(3**8)
    assert not replace(response, target=response.target + 1).producer_verified
    assert not replace(
        response, source_level=response.source_level + 1
    ).producer_verified


def test_candidate_modulus_squaring_not_used_to_issue_temporal_square() -> None:
    spec = FermatNumberSpec(5)
    forbidden_modulus = (1 << 32) + 1
    original_pow = exact_integer_power

    def forbidden(base: int, exponent: int, modulus: int | None = None) -> int:
        if modulus == forbidden_modulus and (base != 2 or exponent >= 64):
            raise AssertionError("candidate-modulus exponentiation forbidden")
        if modulus is None:
            return original_pow(base, exponent)
        return original_pow(base, exponent, modulus)

    with patch.object(builtins, "pow", forbidden):
        action = spec.demand_three_power_temporal_source_morphism(29)
        squared = action.square(spec)
        assert squared.target_level == 31
        assert squared.terminal_status == "UNKNOWN"


def test_reject_invalid_full_phase_carry_certificates() -> None:
    with pytest.raises(ValueError):
        cyclic_square_coefficients((1,))
    with pytest.raises(ValueError):
        cyclic_square_coefficients((1, -1))
    with pytest.raises(ValueError):
        certify_phase_square_carries((0, 0), (1, 0), (0,))
    with pytest.raises(ValueError):
        certify_phase_square_carries((0, 0), (1, 0), (-1, 0))

"""Exact non-oracle radial rotation proofs against bounded integer arithmetic."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.homogeneous_growth import (
    GrowthArithmeticEvaluator,
    HomogeneousGrowthScale,
)
from number_compiler.arithmetic.fields.radial_sturmian import RadialSturmianClock
from number_compiler.resources.ledger import ResourceLedger


@pytest.mark.validation
def test_rotation_prefix_matches_integer_itinerary_and_dyadic_shifts() -> None:
    ledger = ResourceLedger()
    with GrowthArithmeticEvaluator(ledger, max_work_units=5_000_000_000) as evaluator:
        for k in range(130):
            n = 3**k
            for width in (1, 2, 4, 8, 16):
                expected = int(bin(n)[2:][:width].ljust(width, "0"), 2)
                for halvings in (0, k, 3 * k):
                    packet = RadialSturmianClock(
                        HomogeneousGrowthScale(k, halvings)
                    ).leading_binary(evaluator, width)
                    assert packet.prefix_value == expected
                    assert packet.binary_order == n.bit_length() - 1 - halvings
                    assert packet.prefix_binary == format(expected, f"0{width}b")
        assert ledger.nodes >= 0
    assert ledger.nodes == 0


@pytest.mark.validation
def test_sturmian_cocycle_complements_the_next_second_leading_bit() -> None:
    with GrowthArithmeticEvaluator(
        ResourceLedger(), max_work_units=150_000_000
    ) as evaluator:
        unit = RadialSturmianClock(HomogeneousGrowthScale(1, 1))
        for k in range(300):
            bit = unit.width_increment(evaluator, k, 1)
            assert bit in (0, 1)
            assert bit == (3 ** (k + 1)).bit_length() - (3**k).bit_length() - 1
            assert unit.power(k).next_tripling_width_bit(evaluator) == bit
            top_two = int(bin(3 ** (k + 1))[2:][:2], 2)
            assert (top_two & 1) == 1 - bit
        for start, count in ((0, 1024), (10, 300), (777, 4096)):
            assert unit.width_increment(evaluator, start, count) == (
                (3 ** (start + count)).bit_length() - (3**start).bit_length() - count
            )


def test_radial_powering_is_constant_description_and_source_neutral() -> None:
    k = 10**100 + 17
    unit = RadialSturmianClock(HomogeneousGrowthScale(1, 1))
    clock = unit.power(k)
    assert unit.power(k // 2).then(unit.power(k - k // 2)) == clock
    with GrowthArithmeticEvaluator(
        ResourceLedger(), max_work_units=20_000_000
    ) as evaluator:
        packet = clock.leading_binary(evaluator, 8)
        assert packet.growths == k
        assert packet.halvings == k
        assert len(packet.prefix_binary) == 8
        assert packet.precision_bits <= 1024
        assert evaluator.work_used < 20_000_000
    # k was never used to construct 3**k or enumerate k clock symbols.


def test_radial_prefix_refuses_precision_instead_of_guessing() -> None:
    with (
        GrowthArithmeticEvaluator(
            ResourceLedger(), max_precision_bits=7, max_work_units=50_000
        ) as evaluator,
        pytest.raises(BlockContextBudgetExceeded),
    ):
        RadialSturmianClock(HomogeneousGrowthScale(100, 100)).leading_binary(
            evaluator, 8
        )


def test_same_low_bits_do_not_merge_distinct_radial_phases() -> None:
    assert pow(3, 10, 256) == pow(3, 74, 256)
    with GrowthArithmeticEvaluator(ResourceLedger(), max_work_units=3_000_000) as e:
        a = RadialSturmianClock(HomogeneousGrowthScale(10, 10)).leading_binary(e)
        b = RadialSturmianClock(HomogeneousGrowthScale(74, 74)).leading_binary(e)
    assert a.prefix_binary == "11100110"
    assert b.prefix_binary == "10011100"
    assert a != b


@pytest.mark.parametrize("growths,halvings,width", ((0, 9, 8), (5, 3, 8), (74, 80, 16)))
def test_radial_readout_matches_bounded_integer_source(
    growths: int, halvings: int, width: int
) -> None:
    source = 3**growths
    ledger = ResourceLedger()
    with GrowthArithmeticEvaluator(ledger, max_work_units=5_000_000) as evaluator:
        clock = RadialSturmianClock(HomogeneousGrowthScale(growths, halvings))
        packet = clock.leading_binary(evaluator, width)
        expected = source >> max(0, source.bit_length() - width)
        expected <<= max(0, width - source.bit_length())
        assert packet.prefix_value == expected
        assert packet.binary_order == source.bit_length() - 1 - halvings
        assert evaluator.work_used > 0
    assert ledger.nodes == 0


def test_exact_thresholds_charge_work_and_refusals_before_readout() -> None:
    ledger = ResourceLedger()
    with GrowthArithmeticEvaluator(ledger, max_work_units=1) as evaluator:
        with pytest.raises(BlockContextBudgetExceeded):
            evaluator.binary_log_ratio_bounds(1 << 100, 1 << 100)
        assert ledger.counters["growth_arithmetic_budget_refusals"] == 1
        assert ledger.counters["growth_arithmetic_operand_bits"] >= 200
    assert ledger.nodes == 0


def test_radial_precision_refusal_is_measured() -> None:
    ledger = ResourceLedger()
    with GrowthArithmeticEvaluator(ledger, max_precision_bits=4) as evaluator:
        with pytest.raises(BlockContextBudgetExceeded):
            RadialSturmianClock().leading_binary(evaluator, 5)
        assert ledger.counters["growth_arithmetic_budget_refusals"] == 1
    assert ledger.nodes == 0

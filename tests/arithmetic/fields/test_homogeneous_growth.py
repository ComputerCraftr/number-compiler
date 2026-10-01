from __future__ import annotations

from fractions import Fraction

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.homogeneous_growth import (
    GrowthArithmeticEvaluator,
    HomogeneousGrowthScale,
)
from number_compiler.arithmetic.fields.mechanical_readout import (
    MechanicalBlock,
    homogeneous_growth_packet,
    interval,
    point,
    select_weighted,
)
from number_compiler.resources.ledger import ResourceLedger


def _small_power(base: int, exponent: int) -> int:
    value = 1
    for _ in range(exponent):
        value *= base
    return value


def _compare_scale_to_radix_power(
    scale: HomogeneousGrowthScale, radix: int, power: int
) -> int:
    numerator = _small_power(3, scale.growths)
    denominator = _small_power(2, scale.halvings)
    if power >= 0:
        other = denominator * _small_power(radix, power)
        return (numerator > other) - (numerator < other)
    numerator *= _small_power(radix, -power)
    return (numerator > denominator) - (numerator < denominator)


def _oracle_radix_order(scale: HomogeneousGrowthScale, radix: int) -> int:
    for power in range(-80, 81):
        if (
            _compare_scale_to_radix_power(scale, radix, power) >= 0
            and _compare_scale_to_radix_power(scale, radix, power + 1) < 0
        ):
            return power
    raise AssertionError("oracle search range was too small")


def test_scale_composition_power_and_identity_are_exact() -> None:
    identity = HomogeneousGrowthScale.identity()
    first = HomogeneousGrowthScale(2, 3)
    second = HomogeneousGrowthScale(5, 1)

    assert first.then(identity) == first
    assert identity.then(first) == first
    assert first.then(second) == HomogeneousGrowthScale(7, 4)
    assert first.power(0) == identity
    assert first.power(4) == HomogeneousGrowthScale(8, 12)
    assert first.canonical_key == ("homogeneous-growth-scale", 2, 3)
    with pytest.raises(TypeError):
        HomogeneousGrowthScale(True, 0)


def test_radix_order_matches_independent_bounded_integer_oracle() -> None:
    evaluator = GrowthArithmeticEvaluator(ResourceLedger())
    for growths in range(5):
        for halvings in range(5):
            scale = HomogeneousGrowthScale(growths, halvings)
            for radix in range(2, 11):
                assert evaluator.radix_order(scale, radix) == _oracle_radix_order(
                    scale, radix
                )


def test_bounded_exact_ratio_shortcut_fits_small_ledger() -> None:
    ledger = ResourceLedger(max_nodes=70, max_cache_entries=8)
    evaluator = GrowthArithmeticEvaluator(ledger)
    cases = (
        (HomogeneousGrowthScale(1, 1), 10),
        (HomogeneousGrowthScale(0, 1), 10),
        (HomogeneousGrowthScale(3, 1), 10),
        (HomogeneousGrowthScale(20, 20), 10),
        (HomogeneousGrowthScale(1, 1), 2**80 + 1),
    )

    for scale, radix in cases:
        assert evaluator.radix_order(scale, radix) == _oracle_radix_order(scale, radix)

    assert ledger.counters["growth_order_bounded_exact_ratio_cases"] == len(cases)
    assert ledger.counters["growth_log_constant_lookups"] == 0
    assert ledger.peak_nodes <= 70


def test_logarithm_bounds_are_rational_and_certified() -> None:
    evaluator = GrowthArithmeticEvaluator(ResourceLedger())
    lower, upper = evaluator.order_bounds(
        HomogeneousGrowthScale(1, 0), 2, precision_bits=64
    )

    assert isinstance(lower, Fraction)
    assert isinstance(upper, Fraction)
    assert Fraction(19, 12) < lower < upper < Fraction(8, 5)
    evaluator.order_bounds(HomogeneousGrowthScale(2, 1), 2, precision_bits=64)
    assert evaluator.ledger.counters["growth_log_constant_cache_hits"] == 1


def test_evaluator_initializes_order_metrics_and_defers_cf_metrics() -> None:
    ledger = ResourceLedger()
    evaluator = GrowthArithmeticEvaluator(ledger)

    assert ledger.counters["growth_arithmetic_work"] == 0
    assert ledger.counters["growth_order_exact_rational_cases"] == 0
    assert "growth_cf_key_lookups" not in ledger.counters
    assert "growth_cf_budget_refusals" not in ledger.counters

    evaluator.continued_fraction_prefix(HomogeneousGrowthScale.identity(), max_terms=0)

    assert ledger.counters["growth_cf_key_lookups"] == 0
    assert ledger.counters["growth_cf_budget_refusals"] == 0


def test_mechanical_points_and_intervals_telescope_without_symbol_replay() -> None:
    evaluator = GrowthArithmeticEvaluator(ResourceLedger())
    mahler = MechanicalBlock(HomogeneousGrowthScale(1, 1), 0, 10)
    collatz = MechanicalBlock(HomogeneousGrowthScale(0, 1), 0, 4)

    assert point(evaluator, mahler, 0) == 0
    assert interval(evaluator, mahler, 0, 10) == 1
    assert point(evaluator, collatz, 0) == -1
    assert interval(evaluator, collatz, 1, 4) == sum(
        point(evaluator, collatz, index) for index in range(1, 4)
    )
    with pytest.raises(IndexError):
        point(evaluator, mahler, 10)
    with pytest.raises(ValueError):
        interval(evaluator, mahler, 0, 11)


def test_weighted_selection_uses_compact_interval_bisection() -> None:
    evaluator = GrowthArithmeticEvaluator(ResourceLedger())
    increasing = MechanicalBlock(HomogeneousGrowthScale(1, 0), 0, 20)
    decreasing = MechanicalBlock(HomogeneousGrowthScale(0, 1), 0, 12)

    for rank in range(1, 10):
        expected = next(
            index
            for index in range(increasing.length)
            if _oracle_radix_order(increasing.scale.power(index + 1), 10)
            - _oracle_radix_order(increasing.scale.power(increasing.start), 10)
            >= rank
        )
        assert select_weighted(evaluator, increasing, rank) == expected
    for rank in range(1, 4):
        expected = next(
            index
            for index in range(decreasing.length)
            if _oracle_radix_order(decreasing.scale.power(index + 1), 10)
            - _oracle_radix_order(decreasing.scale.power(decreasing.start), 10)
            <= -rank
        )
        assert select_weighted(evaluator, decreasing, rank) == expected

    huge_length = 10**80
    unit_block = MechanicalBlock(HomogeneousGrowthScale(1, 0), 0, huge_length)
    assert select_weighted(evaluator, unit_block, 10**40, radix=3) == 10**40 - 1


def test_continued_fraction_prefixes_are_certified_and_rational_cases_terminate() -> (
    None
):
    evaluator = GrowthArithmeticEvaluator(ResourceLedger())
    irrational = evaluator.continued_fraction_prefix(
        HomogeneousGrowthScale(1, 1), 10, max_terms=5
    )
    rational = evaluator.continued_fraction_prefix(
        HomogeneousGrowthScale(1, 0), 9, max_terms=8
    )

    assert irrational.terms[:2] == (0, 5)
    assert irrational.exact_value is None
    assert not irrational.complete
    assert not irrational.budget_limited
    assert rational.terms == (0, 2)
    assert rational.exact_value == Fraction(1, 2)
    assert rational.complete
    assert evaluator.radix_order(HomogeneousGrowthScale(1, 0), 9) == 0


def test_cf_refinement_replays_certified_prefix_before_extending() -> None:
    evaluator = GrowthArithmeticEvaluator(ResourceLedger())
    scale = HomogeneousGrowthScale(1, 1)
    prefix = evaluator.continued_fraction_prefix(scale, 10, max_terms=20)

    assert prefix.precision_bits >= 128
    assert len(prefix.terms) == 20
    lower, upper = evaluator.order_bounds(scale, 10, precision_bits=128)
    expected: list[int] = []
    for _ in range(20):
        partial_quotient = lower.numerator // lower.denominator
        assert upper.numerator // upper.denominator == partial_quotient
        assert lower > partial_quotient
        assert upper < partial_quotient + 1
        expected.append(partial_quotient)
        lower, upper = 1 / (upper - partial_quotient), 1 / (lower - partial_quotient)
    assert prefix.terms == tuple(expected)


def test_continued_fraction_prefix_reports_budget_limited_suffix() -> None:
    evaluator = GrowthArithmeticEvaluator(
        ResourceLedger(), max_precision_bits=1, max_work_units=100
    )

    prefix = evaluator.continued_fraction_prefix(
        HomogeneousGrowthScale(1, 1), 10, max_terms=4
    )
    assert prefix.budget_limited
    assert not prefix.complete
    assert evaluator.ledger.counters["growth_cf_budget_refusals"] == 1


def test_empty_interval_and_identity_packet_do_no_growth_work() -> None:
    ledger = ResourceLedger(max_nodes=4, max_cache_entries=0)
    evaluator = GrowthArithmeticEvaluator(ledger)
    huge_start = 10**80
    block = MechanicalBlock(HomogeneousGrowthScale(1, 0), huge_start, 3)

    assert interval(evaluator, block, 1, 1) == 0
    assert evaluator.work_used == 0
    with pytest.raises(ValueError):
        interval(evaluator, block, 1, 1, radix=1)
    owners_before = ledger.owner_count
    packet = homogeneous_growth_packet(HomogeneousGrowthScale.identity(), ledger)
    assert packet.homogeneous_radix_order == 0
    assert ledger.owner_count == owners_before
    assert ledger.counters["growth_order_identity_shortcuts"] == 1
    assert ledger.counters["growth_arithmetic_work"] == 0
    assert "homogeneous_growth_packet_identity_shortcuts" not in ledger.counters


def test_packet_validates_context_and_limits_before_identity_shortcut() -> None:
    ledger = ResourceLedger()
    foreign_ledger = ResourceLedger()
    foreign_evaluator = GrowthArithmeticEvaluator(foreign_ledger)
    with pytest.raises(ValueError):
        homogeneous_growth_packet(
            HomogeneousGrowthScale.identity(), ledger, evaluator=foreign_evaluator
        )
    with pytest.raises(ValueError):
        homogeneous_growth_packet(
            HomogeneousGrowthScale.identity(), ledger, max_precision_bits=0
        )

    foreign_evaluator.close()
    with pytest.raises(RuntimeError):
        homogeneous_growth_packet(
            HomogeneousGrowthScale.identity(),
            foreign_ledger,
            evaluator=foreign_evaluator,
        )


def test_symbolic_huge_extent_uses_no_exponential_materialization() -> None:
    ledger = ResourceLedger()
    evaluator = GrowthArithmeticEvaluator(ledger)
    length = 10**80
    block = MechanicalBlock(HomogeneousGrowthScale(1, 0), 0, length)

    assert interval(evaluator, block, 0, length, radix=3) == length
    assert ledger.counters["growth_order_exact_rational_cases"] == 1
    assert ledger.counters.get("growth_log_constant_lookups", 0) == 0


def test_identity_order_survives_a_saturated_ledger_without_cache_allocation() -> None:
    ledger = ResourceLedger(max_nodes=4, max_cache_entries=0)
    evaluator = GrowthArithmeticEvaluator(ledger)

    assert evaluator.radix_order(HomogeneousGrowthScale.identity()) == 0
    assert ledger.entries == 0
    assert ledger.nodes == 0
    assert ledger.counters["growth_order_identity_shortcuts"] == 1


def test_huge_exponent_composition_stays_symbolic() -> None:
    ledger = ResourceLedger()
    scale = (
        HomogeneousGrowthScale(10**80, 10**70)
        .power(10**60)
        .then(HomogeneousGrowthScale(10**55, 10**65))
    )

    assert scale.growths == 10**140 + 10**55
    assert scale.halvings == 10**130 + 10**65
    assert ledger.entries == 0
    assert ledger.nodes == 0


def test_order_readout_refuses_when_work_or_precision_budget_is_exhausted() -> None:
    work_limited = GrowthArithmeticEvaluator(ResourceLedger(), max_work_units=0)
    with pytest.raises(BlockContextBudgetExceeded):
        work_limited.radix_order(HomogeneousGrowthScale(1, 0), 10)
    assert work_limited.work_used == 0

    precision_limited = GrowthArithmeticEvaluator(
        ResourceLedger(), max_precision_bits=1, max_work_units=100_000
    )
    with pytest.raises(BlockContextBudgetExceeded):
        precision_limited.radix_order(HomogeneousGrowthScale(100, 1), 10)
    assert precision_limited.work_used > 0


def test_ledger_capacity_refusal_precedes_radix_series_work() -> None:
    ledger = ResourceLedger(max_nodes=0, max_cache_entries=0)
    evaluator = GrowthArithmeticEvaluator(ledger)

    with pytest.raises(BlockContextBudgetExceeded):
        evaluator.radix_order(HomogeneousGrowthScale(1, 0), 10)
    assert evaluator.work_used == 0
    assert ledger.counters.get("growth_arithmetic_work", 0) == 0


def test_demanded_packet_names_homogeneous_order_and_releases_owners() -> None:
    ledger = ResourceLedger()
    packet = homogeneous_growth_packet(HomogeneousGrowthScale(0, 1), ledger)

    assert packet.growths == 0
    assert packet.halvings == 1
    assert packet.radix == 10
    assert packet.homogeneous_radix_order == -1
    assert packet.canonical_key[0] == "homogeneous-growth-packet"
    assert ledger.entries == 0
    assert ledger.nodes == 0

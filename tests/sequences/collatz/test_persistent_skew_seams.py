"""Source-certified skew actions can re-enter at later seams."""

from __future__ import annotations

from unittest.mock import patch

from number_compiler.arithmetic.fields.homogeneous_growth import (
    GrowthArithmeticEvaluator,
    HomogeneousGrowthScale,
)
from number_compiler.arithmetic.fields.radial_sturmian import RadialSturmianClock
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.temporal_run_quotient import (
    compile_collatz_temporal_run_quotient,
)
from tests.support.collatz_finite_trace import physical_values


def test_later_certified_seam_reenters_and_keeps_run_global_clocks() -> None:
    for observers in (False, True):
        ledger = ResourceLedger()
        seed = (1 << 256) + 10089
        result = compile_collatz_temporal_run_quotient(
            seed,
            256,
            ledger=ledger,
            include_f5=True,
            include_joint_cocycle=observers,
            include_innovation_tape=observers,
            innovation_modulus=49 if observers else None,
        )
        assert result.endpoint == physical_values(seed, 256)[-1]
        action_metrics = {
            key: ledger.counters.get(key, 0)
            for key in (
                "collatz_physical_unified_skew_attempts",
                "collatz_physical_unified_skew_applied_actions",
                "collatz_physical_unified_skew_rejected_prefixes",
                "collatz_physical_unified_skew_budget_refusals",
                "collatz_physical_temporal_dyadic_d8_pumps",
            )
        }
        assert result.run_actions <= 17, action_metrics
        assert (
            ledger.counters.get("collatz_physical_unified_skew_applied_actions", 0) >= 2
        )
        assert result.odd_ticks + result.division_ticks == 256
        assert result.physical_f5 is not None
        assert result.physical_f5.apply(seed) == result.endpoint % 5
        if result.unified_skew_chain is not None:
            assert result.unified_skew_chain.source == seed
        with GrowthArithmeticEvaluator(
            ResourceLedger(), max_work_units=10_000_000
        ) as evaluator:
            observed = result.radial_leading_binary(evaluator, 8)
            expected = RadialSturmianClock(
                HomogeneousGrowthScale(result.odd_ticks, result.division_ticks)
            ).leading_binary(evaluator, 8)
            assert observed == expected


def test_small_misses_keep_cheap_selector_fallback_and_lazy_sturmian_readout() -> None:
    ledger = ResourceLedger()
    with patch.object(
        RadialSturmianClock,
        "leading_binary",
        side_effect=AssertionError("eager radial leading-bit evaluation"),
    ):
        result = compile_collatz_temporal_run_quotient(
            27, 300, ledger=ledger, include_f5=True
        )
    assert result.endpoint == physical_values(27, 300)[-1]
    assert result.run_actions == 11
    assert ledger.counters.get("collatz_physical_temporal_dyadic_d8_pumps") == 6
    assert ledger.counters.get("collatz_physical_unified_skew_applied_actions", 0) == 0
    assert ledger.counters.get("collatz_physical_unified_skew_selector_checks", 0) < 10
    assert result.physical_f5 is not None
    assert result.physical_f5.apply(27) == result.endpoint % 5

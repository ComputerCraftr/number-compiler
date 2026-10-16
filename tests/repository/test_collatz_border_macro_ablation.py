from __future__ import annotations

import pytest

from devtools.benchmarks import collatz_border_macro_ablation as benchmark
from devtools.benchmarks.collatz_border_macro_ablation import Sample
from devtools.verification.oracles.sequence_arithmetic import collatz_literal
from number_compiler.sequences.collatz.border_harmonic_ring import PeriodicTail6305Ring


def test_packet_reads_consumed_macro_counters_from_execution_metrics() -> None:
    observed, _execution = benchmark._packets(
        {
            "info": {
                "temporal.macro": {
                    "executed_macro_actions": {"6305R": 1},
                },
                "metrics": {
                    "execution_metrics": {
                        "family_work": [
                            {
                                "counter_prefix": "collatz_physical",
                                "mixed_clock_work": [
                                    ["actions", 1],
                                    ["physical_ticks", 132],
                                    ["repetitions", 12],
                                ],
                                "border_return_work": [
                                    ["3_reentries", 3],
                                    ["zero_tail_symbols", 7],
                                ],
                            }
                        ]
                    }
                },
            }
        }
    )

    assert observed == {
        "macro": {"executed_macro_actions": {"6305R": 1}},
        "border_actions": 1,
        "border_macro_physical_ticks": 19,
        "mixed_macro_actions": 1,
        "mixed_macro_repetitions": 12,
        "mixed_macro_physical_ticks": 132,
    }


def test_all_selector_ablation_disables_named_and_mixed_selector() -> None:
    from importlib import import_module

    execution = import_module(
        "number_compiler.sequences.collatz.temporal_border_return_execution"
    )
    unified = import_module("number_compiler.sequences.collatz.unified_skew_admission")
    mixed = import_module("number_compiler.sequences.collatz.temporal_mixed_execution")
    original = (
        execution.select_border_return_macro,
        unified.select_border_return_macro,
        mixed.select_mixed_clock_macro,
    )
    with benchmark._selector_ablation(include_mixed=True):
        assert execution.select_border_return_macro() is None
        assert unified.select_border_return_macro() is None
        assert mixed.select_mixed_clock_macro() is None
    assert (
        execution.select_border_return_macro,
        unified.select_border_return_macro,
        mixed.select_mixed_clock_macro,
    ) == original


def test_missing_6305_action_retains_raw_cli_samples(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    motif = (1, 2)
    groups = 12
    source = benchmark._source_for(motif, groups)
    ring = PeriodicTail6305Ring.from_source(source, motif)
    ticks = groups * ring.physical_ticks
    endpoint = collatz_literal(source, ticks)

    def no_macro(
        _arguments: list[str], *, fresh: bool
    ) -> tuple[float, dict[str, object]]:
        assert fresh is False
        return 0.01, {
            "value": str(endpoint),
            "info": {
                "temporal.macro": {
                    "executed_macro_actions": {"6305R": 0},
                    "first_executed_macro": None,
                },
                "metrics": {
                    "execution_metrics": {
                        "family_work": [
                            {
                                "counter_prefix": "collatz_physical",
                                "border_return_work": None,
                                "mixed_clock_work": None,
                            }
                        ]
                    }
                },
            },
        }

    monkeypatch.setattr(benchmark, "cli_sample", no_macro)
    retained: list[Sample] = []
    with pytest.raises(
        AssertionError, match="did not consume a complete powered action"
    ):
        benchmark.compare(motif, groups, 1, on_sample=retained.append)

    assert [sample["mode"] for sample in retained] == [
        "enabled",
        "selector_disabled",
        "all_selectors_disabled",
    ]
    assert all(sample["macro"] == retained[0]["macro"] for sample in retained)
    assert all(sample["border_actions"] == 0 for sample in retained)
    assert all(sample["mixed_macro_actions"] is None for sample in retained)

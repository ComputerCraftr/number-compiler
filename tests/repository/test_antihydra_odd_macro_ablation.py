"""The odd-macro benchmark treats missing work counters as no observed hit."""

from __future__ import annotations

import pytest

from devtools.benchmarks import antihydra_odd_macro_ablation as benchmark


def test_fixed_seed_cli_reports_no_macro_hits_without_failing(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    queries: list[list[str]] = []

    def no_macro_cli(
        arguments: list[str], *, fresh: bool
    ) -> tuple[float, dict[str, object]]:
        assert fresh is False
        assert arguments[0] == "antihydra"
        assert "--seed" not in arguments
        queries.append(arguments)
        mahler = "arithmetic.mahler" in arguments
        if mahler:
            assert "--no-value" in arguments
        return 0.01, {
            "value": None if mahler else "123",
            "info": {
                **({"arithmetic.mahler": {"status": "available"}} if mahler else {}),
                "metrics": {
                    "execution_metrics": {
                        "family_work": [
                            {
                                "counter_prefix": "antihydra_arithmetic",
                                "odd_macro_work": None,
                            }
                        ]
                    }
                },
            },
        }

    monkeypatch.setattr(benchmark, "cli_sample", no_macro_cli)
    payload = benchmark.compare(horizons=(65,), trials=1)

    # Each of two consumers warms and measures all three ablation modes.
    assert len(queries) == 12
    samples = payload["samples"]
    assert isinstance(samples, list)
    assert len(samples) == 6
    assert {row["mode"] for row in samples} == {
        "enabled",
        "odd_macro_disabled",
        "prefilter_disabled",
    }
    summaries = payload["summaries"]
    assert isinstance(summaries, list)
    assert [row["consumer"] for row in summaries] == ["antihydra", "mahler"]
    assert all(row["enabled_macro_hit"] is False for row in summaries)
    assert all(row["enabled_macro_evaluations"] == [None] for row in summaries)
    assert all(row["disabled_macro_evaluations"] == [None] for row in summaries)
    assert all(row["enabled_odd_macro_work"] == [None] for row in summaries)
    assert all(row["disabled_odd_macro_work"] == [None] for row in summaries)


def test_route_comparison_rejects_inconsistent_enabled_endpoints(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    rendered = 0

    def changing_cli(
        _arguments: list[str], *, fresh: bool
    ) -> tuple[float, dict[str, object]]:
        nonlocal rendered
        assert fresh is False
        rendered += 1
        return 0.01, {
            "value": str(rendered),
            "info": {
                "metrics": {
                    "execution_metrics": {
                        "family_work": [
                            {
                                "counter_prefix": "antihydra_arithmetic",
                                "odd_macro_work": None,
                            }
                        ]
                    }
                }
            },
        }

    monkeypatch.setattr(benchmark, "cli_sample", changing_cli)
    with pytest.raises(AssertionError, match="value or observation changed"):
        benchmark.compare(horizons=(65,), consumers=("antihydra",), trials=1)

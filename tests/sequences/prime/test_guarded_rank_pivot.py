"""Exact rank brackets authorize every guarded pivot proposal."""

from __future__ import annotations

import json
from math import isqrt

import pytest

from number_compiler.api import cli
from number_compiler.resources.metric_keys import prime as prime_metrics
from number_compiler.sequences.prime import select
from number_compiler.sequences.prime.select import (
    PrimeRankSelectMetrics,
    RankPivotMode,
    RankPivotReason,
    guarded_rank_offset,
)


def test_pivot_bounds_and_forced_midpoint() -> None:
    for width in range(2, 100):
        for round_index in range(10):
            pivot, reason = guarded_rank_offset(3, 3 + width, 0, 8, 3, 100, round_index)
            assert 3 < pivot < 3 + width
            if width <= 4:
                assert reason is RankPivotReason.SMALL_MIDPOINT
            elif round_index % 5 == 4:
                assert reason is RankPivotReason.FORCED_MIDPOINT
                assert pivot == 3 + width // 2


def test_invalid_rank_brackets_rejected() -> None:
    with pytest.raises(ValueError, match="certified rank bracket"):
        guarded_rank_offset(0, 1, 0, 1, 0, 3, 0)
    with pytest.raises(ValueError, match="certified rank bracket"):
        guarded_rank_offset(0, 10, 0, 3, 3, 3, 0)


def test_large_rank_avoids_float_conversion() -> None:
    huge = 1 << 2000
    pivot, reason = guarded_rank_offset(0, 100, 0, huge + 1, huge, 3, 0)
    assert pivot == 50
    assert reason is RankPivotReason.LARGE_MIDPOINT


def test_guarded_descent_with_independent_literal_counts() -> None:
    for source in (3, 23, 101, 1231):
        values = list(range(source | 1, (source | 1) + 2 * 80, 2))
        prime = [n >= 2 and all(n % d for d in range(2, isqrt(n) + 1)) for n in values]
        prefix = [0]
        for admitted in prime:
            prefix.append(prefix[-1] + int(admitted))
        for target in range(prefix[-1]):
            left, right, rounds = 0, len(values), 0
            while right - left > 1:
                pivot, _ = guarded_rank_offset(
                    left,
                    right,
                    prefix[left],
                    prefix[right],
                    target,
                    values[left],
                    rounds,
                )
                if target < prefix[pivot]:
                    right = pivot
                else:
                    left = pivot
                rounds += 1
            assert prime[left]
            assert prefix[left] == target


@pytest.mark.parametrize(
    "start,index,expected", ((0, 1000, 7927), (150000, 200, 152293))
)
def test_automatic_route_preserves_exact_outputs(
    start: int, index: int, expected: int
) -> None:
    result, metrics = select.nth_prime_at_or_after(start, index)
    assert result == expected
    counters = dict(metrics.scheduler_counters)
    assert counters[prime_metrics.PRIME_WEIGHTED_FACTOR_PROBES] > 0
    assert any(name.startswith("prime_pivot_") for name in counters)


@pytest.mark.parametrize("max_work,leaf_length", ((999999, 8), (1000000, 9)))
def test_nondefault_budgets_keep_existing_path(max_work: int, leaf_length: int) -> None:
    result, metrics = select.nth_prime_at_or_after(
        0, 200, max_work=max_work, leaf_length=leaf_length
    )
    assert result == 1229
    assert not any(
        name.startswith("prime_weighted_") for name, _ in metrics.scheduler_counters
    )


@pytest.mark.parametrize(
    "start,index,weighted,fused,pivot",
    (
        (131071, 200, True, False, RankPivotMode.GUARDED),
        (131072, 200, True, True, RankPivotMode.GUARDED),
        (2097151, 200, True, True, RankPivotMode.GUARDED),
        (2097152, 200, True, False, RankPivotMode.BISECTION),
        (9948560, 200, True, False, RankPivotMode.BISECTION),
        (16777215, 200, True, False, RankPivotMode.BISECTION),
        (16777216, 200, False, False, RankPivotMode.BISECTION),
        (0, 199, False, False, RankPivotMode.BISECTION),
        (0, 4096, True, False, RankPivotMode.GUARDED),
        (0, 4097, False, False, RankPivotMode.BISECTION),
    ),
)
def test_automatic_dispatch_boundaries(
    monkeypatch: pytest.MonkeyPatch,
    start: int,
    index: int,
    weighted: bool,
    fused: bool,
    pivot: RankPivotMode,
) -> None:
    seen: list[dict[str, object]] = []

    def capture(
        _start: int, _index: int, **options: object
    ) -> tuple[int, PrimeRankSelectMetrics]:
        seen.append(options)
        return 2, PrimeRankSelectMetrics(0, 0, 0, 0, 0, 0)

    monkeypatch.setattr(select, "_nth_prime_at_or_after", capture)
    select.nth_prime_at_or_after(start, index)
    assert seen[0]["_weighted"] is weighted
    assert seen[0]["_fused_masks"] is fused
    assert seen[0]["_pivot"] is pivot


def test_automatic_route_reports_cli_metrics(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(["prime", "--nth", "1000", "--info", "metrics", "--format", "json"])
        == 0
    )
    row = json.loads(capsys.readouterr().out)
    assert row["value"] == "7927"
    counters = row["info"]["metrics"]["prime_scheduler_counters"]
    assert counters[prime_metrics.PRIME_WEIGHTED_FACTOR_PROBES] > 0
    assert counters[prime_metrics.PRIME_PIVOT_DENSITY] > 0

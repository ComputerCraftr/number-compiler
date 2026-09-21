"""Exact bounded oracles for sparse integer signs, not temporal admission."""

from itertools import pairwise
from math import comb
from random import Random

import pytest

from devtools.experiments.reverse_add.radial_modular_sign import ModularSignOracle
from devtools.experiments.reverse_add.radial_sign_runs import (
    ShiftTerm,
    SignLimits,
    SignRun,
    SignWork,
    isolate_common_growth_signs,
    isolate_common_growth_signs_assuming_bound,
)


def _literal(row: int, terms: tuple[ShiftTerm, ...], k: int) -> int:
    value = sum(
        t.coefficient * comb(row, k - t.shift) for t in terms if 0 <= k - t.shift <= row
    )
    return (value > 0) - (value < 0)


def test_integer_sign_runs_match_independent_complete_small_rows() -> None:
    random = Random(1962026)
    for _ in range(1200):
        row = random.randrange(25)
        terms = tuple(
            ShiftTerm(random.randrange(-8, 12), random.randrange(-5, 6))
            for _ in range(random.randrange(9))
        )
        work = SignWork()
        runs = isolate_common_growth_signs(row, terms, -10, 40, work=work)
        assert runs[0].start == -10 and runs[-1].stop == 40
        assert all(a.stop == b.start and a.sign != b.sign for a, b in pairwise(runs))
        actual = [run.sign for run in runs for _ in range(run.start, run.stop)]
        assert actual == [_literal(row, terms, k) for k in range(-10, 40)]
        assert work.retained_items == 0


def test_huge_binary_row_and_span_use_symmetry_not_binomial_expansion() -> None:
    row = 10**200
    gap = row // 3
    work = SignWork()
    runs = isolate_common_growth_signs(
        row,
        (ShiftTerm(0, 1), ShiftTerm(gap, -1)),
        0,
        row + gap + 1,
        work=work,
        limits=SignLimits(max_factor_steps=1, max_sign_queries=5000),
    )
    # Compare binomial distances from the common row's center exactly.
    midpoint = (row + gap) // 2
    assert runs == (
        SignRun(0, midpoint + 1, 1),
        SignRun(midpoint + 1, row + gap + 1, -1),
    )
    assert work.ratio_factors == 0
    assert work.sign_queries < 2000
    assert work.operator_terms == 1
    assert work.support_cells == 3
    assert work.retained_items == 0


def test_middle_zero_and_support_boundaries_are_retained() -> None:
    assert isolate_common_growth_signs(
        10, (ShiftTerm(0, 1), ShiftTerm(2, -1)), -1, 14, work=SignWork()
    ) == (
        SignRun(-1, 0, 0),
        SignRun(0, 6, 1),
        SignRun(6, 7, 0),
        SignRun(7, 13, -1),
        SignRun(13, 14, 0),
    )


def test_neutral_span_and_zero_derivative_do_not_force_scanning() -> None:
    n = 10**200
    work = SignWork()
    assert isolate_common_growth_signs(
        n, (ShiftTerm(7, 3), ShiftTerm(7, -3)), -n, n, work=work
    ) == (SignRun(-n, n, 0),)
    assert work.sign_queries == 1
    assert work.ratio_factors == work.operator_terms == 0


def test_unequal_weights_have_exact_small_gap_oracle_even_on_huge_rows() -> None:
    n = 10**100
    work = SignWork()
    runs = isolate_common_growth_signs(
        n, (ShiftTerm(0, 1), ShiftTerm(1, -2)), 0, n + 2, work=work
    )
    # h_1/h_0 = k/(n-k+1), so sign is sign(n+1-3k).
    boundary = (n + 1) // 3 + 1
    assert runs == (SignRun(0, boundary, 1), SignRun(boundary, n + 2, -1))
    assert work.ratio_factors < 1000
    assert work.sign_queries < 1000


def test_wide_factorial_ratio_refuses_before_hidden_span_expansion() -> None:
    work = SignWork()
    with pytest.raises(ValueError, match="ratio-factor"):
        isolate_common_growth_signs(
            10**100,
            (ShiftTerm(0, 1), ShiftTerm(10**50, -2)),
            10**50,
            10**100,
            work=work,
            limits=SignLimits(max_factor_steps=10),
        )
    assert work.ratio_factors == 0
    assert work.retained_items == 0


def test_crt_replaces_wide_factorial_ratios_under_a_proved_small_bound(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from devtools.experiments.reverse_add import radial_sign_runs

    def forbidden(*args: object) -> int:
        raise AssertionError("factorial-ratio arithmetic is forbidden in CRT mode")

    monkeypatch.setattr(radial_sign_runs, "_fraction_add", forbidden)
    row = 10**18
    work = SignWork()
    oracle = ModularSignOracle()
    # On these three integer positions the values are n(n-1)/2-2,
    # -n, and 1-n(n-1). Their absolute values are <=n^2.
    runs = isolate_common_growth_signs_assuming_bound(
        row,
        (ShiftTerm(0, 1), ShiftTerm(row - 2, -2)),
        row - 2,
        row + 1,
        assumed_bound=row * row,
        modular=oracle,
        work=work,
        limits=SignLimits(max_factor_steps=1),
    )
    assert runs == (SignRun(row - 2, row - 1, 1), SignRun(row - 1, row + 1, -1))
    assert work.ratio_factors == 0
    assert oracle.work.crt_merges > 0
    assert oracle.work.lucas_digits < 10_000


def test_crt_elimination_transports_magnitude_bounds_at_every_level() -> None:
    class IntervalOracle(ModularSignOracle):
        def sign(
            self, row: int, terms: tuple[tuple[int, int], ...], k: int, *, bound: int
        ) -> int:
            # Derivative endpoints are inclusive *parent* coordinates; the
            # original half-open interval needs no unadmitted endpoint halo.
            assert -4 <= k < 24
            return super().sign(row, terms, k, bound=bound)

    random = Random(19619)
    oracle = IntervalOracle()
    for _ in range(160):
        row = random.randrange(1, 16)
        terms = tuple(
            ShiftTerm(random.randrange(-3, 6), random.randrange(-5, 6))
            for _ in range(random.randrange(2, 7))
        )
        start, stop = -4, 24
        # Full expansion here is an independent bounded test oracle only.
        values = [
            sum(
                t.coefficient * comb(row, k - t.shift)
                for t in terms
                if 0 <= k - t.shift <= row
            )
            for k in range(start, stop)
        ]
        bound = max(map(abs, values))
        actual = isolate_common_growth_signs_assuming_bound(
            row,
            terms,
            start,
            stop,
            assumed_bound=bound,
            modular=oracle,
            work=SignWork(),
        )
        assert [run.sign for run in actual for _ in range(run.start, run.stop)] == [
            (value > 0) - (value < 0) for value in values
        ]


@pytest.mark.parametrize(
    "limits",
    [
        SignLimits(max_integer_bits=2),
        SignLimits(max_integer_work_bits=1),
        SignLimits(max_sign_queries=1),
        SignLimits(max_retained_items=1),
        SignLimits(max_operator_terms=1),
    ],
)
def test_failed_isolation_cleans_temporary_storage(limits: SignLimits) -> None:
    work = SignWork()
    with pytest.raises(ValueError, match="budget"):
        isolate_common_growth_signs(
            30,
            (ShiftTerm(0, 2), ShiftTerm(2, -3), ShiftTerm(4, 1)),
            -1,
            40,
            work=work,
            limits=limits,
        )
    assert work.retained_items == 0


def test_exact_types_and_empty_interval() -> None:
    with pytest.raises(TypeError, match="exact integers"):
        ShiftTerm(True, 1)
    with pytest.raises(TypeError, match="exact integers"):
        isolate_common_growth_signs(True, (), 0, 1, work=SignWork())
    assert isolate_common_growth_signs(10, (), 5, 5, work=SignWork()) == ()

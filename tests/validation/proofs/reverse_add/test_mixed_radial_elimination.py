"""Differential checks for research-only mixed radial elimination."""

from __future__ import annotations

from fractions import Fraction
from random import Random

import pytest

import devtools.experiments.reverse_add.mixed_radial_elimination as mixed
from devtools.experiments.reverse_add.mixed_radial_elimination import (
    EliminationLimits,
    EliminationWork,
    WeightedBinomial,
    eliminate_chain,
    eliminate_pivot,
    evaluate_polynomial,
    evaluate_weighted_binomial,
)


def _operator(
    pivot: WeightedBinomial, terms: tuple[WeightedBinomial, ...], k: int
) -> Fraction:
    value = sum((evaluate_weighted_binomial(term, k) for term in terms), Fraction())
    following = sum(
        (evaluate_weighted_binomial(term, k + 1) for term in terms), Fraction()
    )
    return (
        evaluate_polynomial(pivot.polynomial, k) * (k + 1 - pivot.shift) * following
        - evaluate_polynomial(pivot.polynomial, k + 1) * (pivot.terminal - k) * value
    )


def _evaluate(terms: tuple[WeightedBinomial, ...], k: int) -> Fraction:
    return sum((evaluate_weighted_binomial(term, k) for term in terms), Fraction())


def test_mixed_tp_witness_is_eliminated_with_the_linear_turning_factor() -> None:
    pivot = WeightedBinomial((Fraction(1),), 2, 1)
    other = WeightedBinomial((Fraction(1),), 4, 0)
    work = EliminationWork()
    result = eliminate_pivot(pivot, (pivot, other), work=work)
    assert result == (WeightedBinomial((Fraction(-3, 5), Fraction(2, 5)), 5, -1),)
    for k in range(-1, 6):
        assert _evaluate(result, k) == _operator(pivot, (pivot, other), k)
    assert [
        24 * evaluate_weighted_binomial(pivot, k)
        - 7 * evaluate_weighted_binomial(other, k)
        for k in range(5)
    ] == [
        -7,
        -4,
        6,
        -4,
        -7,
    ]


def test_random_polynomial_weights_match_direct_operator_at_support_edges() -> None:
    random = Random(196)
    for _ in range(250):
        pivot = WeightedBinomial(
            (Fraction(random.choice((-4, -3, -2, -1, 1, 2, 3, 4))),)
            + tuple(Fraction(random.randrange(-4, 5)) for _ in range(2)),
            random.randrange(6),
            random.randrange(-2, 4),
        )
        other = WeightedBinomial(
            (Fraction(random.choice((-4, -3, -2, -1, 1, 2, 3, 4))),)
            + tuple(Fraction(random.randrange(-4, 5)) for _ in range(2)),
            random.randrange(6),
            random.randrange(-2, 4),
        )
        result = eliminate_pivot(pivot, (other,), work=EliminationWork())
        start = min(pivot.shift, other.shift) - 2
        stop = max(pivot.terminal, other.terminal) + 2
        for k in range(start, stop + 1):
            assert _evaluate(result, k) == _operator(pivot, (other,), k)


def test_operator_preserves_exact_birth_and_death_boundary_values() -> None:
    pivot = WeightedBinomial((Fraction(2), Fraction(1)), 3, 2)
    other = WeightedBinomial((Fraction(-1), Fraction(2)), 2, 5)
    result = eliminate_pivot(pivot, (other,), work=EliminationWork())
    assert result[0].shift == other.shift - 1
    assert result[0].terminal == other.terminal
    for k in (other.shift - 2, other.shift - 1, other.shift, other.terminal):
        assert _evaluate(result, k) == _operator(pivot, (other,), k)
    assert _evaluate(result, other.shift - 2) == 0


def test_degree_bound_and_iterative_chain_are_explicit() -> None:
    terms = (
        WeightedBinomial((Fraction(1), Fraction(2)), 3, 0),
        WeightedBinomial((Fraction(-2), Fraction(1), Fraction(1)), 5, 1),
        WeightedBinomial((Fraction(3), Fraction(-1)), 7, -2),
    )
    first = eliminate_pivot(terms[0], terms[1:], work=EliminationWork())
    assert all(
        term.degree <= terms[0].degree + source.degree + 1
        for term, source in zip(first, terms[1:], strict=True)
    )
    work = EliminationWork()
    final = eliminate_chain(terms, work=work)
    assert len(final) == 1
    assert work.steps == 2
    assert final[0].degree <= 8
    # Products are charged before their degree-nine leading terms cancel.
    assert work.peak_polynomial_degree <= 9


def test_huge_encoded_growth_uses_only_operator_polynomials() -> None:
    huge = 10**200
    pivot = WeightedBinomial((Fraction(1),), huge, 17)
    other = WeightedBinomial((Fraction(-3),), huge + 9, -11)
    work = EliminationWork()
    result = eliminate_pivot(pivot, (other,), work=work)
    assert len(result) == 1
    assert result[0].growth == huge + 10
    assert result[0].shift == -12
    assert result[0].degree <= 1
    assert work.polynomial_coefficients < 100
    assert work.peak_coefficient_bits < 2048


def test_degree_and_integer_budgets_refuse_without_partial_claims() -> None:
    pivot = WeightedBinomial((Fraction(1), Fraction(1)), 5, 0)
    other = WeightedBinomial((Fraction(1), Fraction(1)), 7, 1)
    with pytest.raises(ValueError, match="degree budget"):
        eliminate_pivot(
            pivot,
            (other,),
            work=EliminationWork(),
            limits=EliminationLimits(max_polynomial_degree=1),
        )
    with pytest.raises(ValueError, match="coefficient size budget"):
        eliminate_pivot(
            WeightedBinomial((Fraction(1),), 10**20, 0),
            (other,),
            work=EliminationWork(),
            limits=EliminationLimits(max_coefficient_bits=8),
        )


def test_invalid_packets_and_step_budget_fail_closed() -> None:
    with pytest.raises(ValueError, match="nonzero"):
        WeightedBinomial((Fraction(0),), 1, 0)
    with pytest.raises(TypeError, match="exact rationals"):
        WeightedBinomial((0.5,), 1, 0)  # type: ignore[arg-type]
    terms = tuple(
        WeightedBinomial((Fraction(index + 1),), index + 1, index) for index in range(3)
    )
    with pytest.raises(ValueError, match="step budget"):
        eliminate_chain(
            terms,
            work=EliminationWork(),
            limits=EliminationLimits(max_steps=1),
        )


def test_over_degree_input_refuses_before_shift_arithmetic(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def poisoned_shift(_: object) -> object:
        raise AssertionError("shift arithmetic ran before input admission")

    monkeypatch.setattr(mixed, "_shift_values", poisoned_shift)
    with pytest.raises(ValueError, match="degree budget"):
        eliminate_pivot(
            WeightedBinomial((Fraction(1), Fraction(1), Fraction(1)), 3, 0),
            (WeightedBinomial((Fraction(1),), 4, 1),),
            work=EliminationWork(),
            limits=EliminationLimits(max_polynomial_degree=1),
        )


def test_operation_preflight_refuses_before_product_and_fraction_addition(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def poisoned_product(_: object, __: object) -> object:
        raise AssertionError("convolution ran before degree admission")

    monkeypatch.setattr(mixed, "_convolve", poisoned_product)
    with pytest.raises(ValueError, match="degree budget"):
        eliminate_pivot(
            WeightedBinomial((Fraction(1), Fraction(1)), 3, 0),
            (WeightedBinomial((Fraction(1), Fraction(1)), 4, 1),),
            work=EliminationWork(),
            limits=EliminationLimits(max_polynomial_degree=1),
        )

    calls = 0

    def poisoned_add(
        left: mixed.Polynomial, right: mixed.Polynomial, size: int
    ) -> tuple[Fraction, ...]:
        nonlocal calls
        calls += 1
        raise AssertionError("fraction addition ran before height admission")

    monkeypatch.setattr(mixed, "_add_values", poisoned_add)
    duplicate = WeightedBinomial((Fraction(127, 128),), 3, 0)
    with pytest.raises(ValueError, match="coefficient size budget"):
        eliminate_chain(
            (duplicate, duplicate),
            work=EliminationWork(),
            limits=EliminationLimits(max_coefficient_bits=8),
        )
    assert calls == 0

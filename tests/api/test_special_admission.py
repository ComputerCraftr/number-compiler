"""Theorem budgets are admitted before state construction or cache lookup."""

from typing import Never

import pytest

from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler


def _forbidden(*args: object, **kwargs: object) -> Never:
    raise AssertionError("candidate reached constraint construction before admission")


@pytest.mark.parametrize(
    "family,parameter", [("fermat", 10**100), ("mersenne", 1_000_001)]
)
def test_candidate_budget_precedes_constraint_state(
    family: str,
    parameter: int,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        CanonicalSequenceCompiler, "_special_constraint_state", _forbidden
    )
    with pytest.raises(ValueError, match="candidate exceeds max_candidate_bits"):
        CanonicalSequenceCompiler().resolve_special_theorem(family, parameter)


def test_candidate_budget_is_checked_even_for_cached_answer() -> None:
    compiler = CanonicalSequenceCompiler()
    assert compiler.resolve_special_theorem("fermat", 3).decided
    with pytest.raises(ValueError, match="candidate exceeds max_candidate_bits"):
        compiler.resolve_special_theorem("fermat", 3, max_candidate_bits=8)
    assert compiler.resolve_special_theorem("fermat", 3, max_candidate_bits=9).decided


def test_explicit_budget_preserves_bounded_large_exponent_gate() -> None:
    exponent = (1 << 64) + 13
    result = CanonicalSequenceCompiler().resolve_special_theorem(
        "mersenne",
        exponent,
        max_candidate_bits=exponent,
    )
    assert not result.decided
    assert result.projection_method == "exponent-gate-budget"

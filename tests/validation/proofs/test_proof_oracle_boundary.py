"""Exact reference state cannot be used implicitly by production observers."""

from __future__ import annotations

import pytest

from devtools.proofs import ExactOracleAccessForbidden, exact_oracle
from devtools.proofs.carry_action_quotient import CarryActionQuotientArena
from devtools.proofs.reverse_spacetime import (
    ReverseAddCausalSpacetimeEngine,
    ReverseAddPairField,
)
from number_compiler.arithmetic.contracts.exact_tree_context import (
    ExactTreeConstructionForbidden,
    source_reads_only,
)


def test_exact_oracle_requires_explicit_scope_before_cold_or_warm_access() -> None:
    with pytest.raises(ExactOracleAccessForbidden):
        ReverseAddCausalSpacetimeEngine()
    with pytest.raises(ExactOracleAccessForbidden):
        CarryActionQuotientArena()
    with pytest.raises(ExactOracleAccessForbidden):
        ReverseAddPairField.from_value(196)
    with exact_oracle():
        engine = ReverseAddCausalSpacetimeEngine()
        source = ReverseAddPairField.from_value(196)
        expected, _ = engine.advance_power(source, 1)
    for steps in (0, 1, 2):
        with pytest.raises(ExactOracleAccessForbidden):
            engine.advance_power(source, steps)
    with pytest.raises(ExactOracleAccessForbidden):
        source.values()
    with exact_oracle():
        actual, _ = engine.advance_power(source, 1)
        assert actual == expected


def test_point_scope_rejects_oracle_even_with_preexisting_authority() -> None:
    with exact_oracle():
        engine = ReverseAddCausalSpacetimeEngine()
        source = ReverseAddPairField.from_value(196)
        engine.advance_power(source, 1)

        @source_reads_only
        def read(steps: int) -> None:
            engine.advance_power(source, steps)

        for steps in (0, 1, 2):
            with pytest.raises(ExactTreeConstructionForbidden):
                read(steps)

    @source_reads_only
    def mint() -> None:
        with exact_oracle():
            pass

    with pytest.raises(ExactTreeConstructionForbidden):
        mint()


def test_exact_oracle_scope_nests_and_restores_on_failure() -> None:
    with exact_oracle():
        with pytest.raises(ValueError), exact_oracle():
            raise ValueError("reference failure")
        source = ReverseAddPairField.from_value(196)
        assert source.values() == (7, 18, 7)
    with pytest.raises(ExactOracleAccessForbidden):
        source.values()

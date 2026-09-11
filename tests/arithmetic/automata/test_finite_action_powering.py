from __future__ import annotations

from number_compiler.arithmetic.automata.symmetry_powering import BinaryLiftEngine


def test_binary_lift_is_iterative_exact_and_bounded() -> None:
    engine = BinaryLiftEngine(
        step=lambda state: ((state + 1) % 7, 1),
        key=int,
        identity_weight=0,
        combine_weight=lambda a, b: int(a) + int(b),
        jump_cache_limit=8,
    )
    target, weight = engine.advance(0, 1_000_003)
    assert target == 1_000_003 % 7
    assert weight == 1_000_003
    metrics = engine.metrics()
    assert metrics.jump_entries <= 8
    assert metrics.jump_evictions > 0


def test_binary_lift_reuses_a_fixed_semantic_state_at_huge_power() -> None:
    engine = BinaryLiftEngine(
        step=lambda state: (state, 3),
        key=lambda state: state,
        identity_weight=0,
        combine_weight=lambda a, b: int(a) + int(b),
        jump_cache_limit=128,
    )
    target, weight = engine.advance("fixed", 1 << 40)
    assert target == "fixed"
    assert weight == 3 * (1 << 40)
    metrics = engine.metrics()
    assert metrics.step_evaluations == 1
    assert metrics.jump_entries <= 41


def test_finite_quotient_lift_powers_complete_map_without_path_discovery() -> None:
    from number_compiler.arithmetic.automata.symmetry_powering import (
        FiniteQuotientLiftEngine,
    )

    engine = FiniteQuotientLiftEngine(
        states=range(7),
        step=lambda state: ((state + 1) % 7, 1),
        key=int,
        identity_weight=0,
        combine_weight=lambda a, b: int(a) + int(b),
    )
    target, weight = engine.advance(0, 1_000_003)
    assert target == 1_000_003 % 7
    assert weight == 1_000_003
    metrics = engine.metrics()
    # The primitive transition is evaluated once over the complete carrier,
    # independent of the requested horizon.  Query execution only consumes
    # binary table levels.
    assert metrics.primitive_step_evaluations == 7
    assert metrics.built_levels <= (1_000_003).bit_length()
    assert metrics.squaring_operations == 7 * (metrics.built_levels - 1)


def test_finite_quotient_lift_rejects_nonclosed_adapter() -> None:
    import pytest

    from number_compiler.arithmetic.automata.symmetry_powering import (
        FiniteQuotientLiftEngine,
    )

    with pytest.raises(ValueError, match="successor outside finite quotient"):
        FiniteQuotientLiftEngine(
            states=(0, 1),
            step=lambda state: (state + 1, None),
            key=int,
            identity_weight=None,
            combine_weight=lambda _a, _b: None,
        )

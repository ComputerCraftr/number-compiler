"""Exact oracle regression; these objects are not production carriers."""

from __future__ import annotations

import random

import pytest

from devtools.verification.reverse_spacetime import (
    ReverseAddCausalSpacetimeEngine,
    ReverseAddPairField,
)
from number_compiler.arithmetic.carry.event_memory import pair_step
from number_compiler.arithmetic.fields.dyadic_tile import iter_symbols


def test_reverse_pair_spacetime_step_matches_reference_over_random_symmetric_fields() -> (
    None
):
    rng = random.Random(0x196)
    for base in (3, 4, 7, 10):
        engine = ReverseAddCausalSpacetimeEngine(base=base)
        for width in range(1, 18):
            for _ in range(4):
                half = [rng.randrange(2 * base - 1) for _ in range((width + 1) // 2)]
                pair = (
                    tuple(half + half[-2::-1])
                    if width & 1
                    else tuple(half + half[::-1])
                )
                field = ReverseAddPairField.from_pair(pair, base=base)
                step = engine.advance(field)
                expected, growth = pair_step(pair, base)
                assert step.growth == growth
                assert step.target.values() == expected
        metrics = engine.metrics()
        assert metrics.carry_direction == "lsd-to-msd"
        assert metrics.finite_cell_alphabet == 2 * base
        assert metrics.carry_unique_actions <= 4
        assert metrics.carry_action_alias_hits > 0
        assert metrics.carry_mirror_alias_hits > 0
        assert metrics.carry_conjugate_alias_hits > 0


def test_reverse_spacetime_terms_match_scalar_and_do_not_use_blockeffect_residuals(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # The causal field engine has no dependency on the old BlockEffect evaluator.
    import number_compiler.hashlife.observation.hashlife_projection as old_hashlife

    # The retired BlockEffect point interpreter has been deleted outright; the
    # reference causal engine remains independent of the direct production
    # HashLife index.
    assert not hasattr(old_hashlife.HashLifeBlockIndex, "point")
    engine = ReverseAddCausalSpacetimeEngine(base=10)
    scalar = 196
    field = ReverseAddPairField.from_value(196, base=10)
    for generation in range(1, 80):
        scalar += int(str(scalar)[::-1])
        digits = engine.terminal_digits(field)
        got = sum(digit * (10**i) for i, digit in enumerate(iter_symbols(digits)))
        assert got == scalar
        field = engine.advance(field).target
    metrics = engine.metrics()
    assert metrics.primitive_field_steps == 79
    assert metrics.carry_direction == "lsd-to-msd"


def test_reverse_bounded_memory_slab_forgets_pre_window_pair_exactly() -> None:
    engine = ReverseAddCausalSpacetimeEngine(base=10)
    initial = ReverseAddPairField.from_value(196, base=10)
    slab, endpoint = engine.bootstrap_slab(initial)
    assert slab.current_pair().values() == endpoint.values()
    assert len(slab.carries) == 20
    advanced, weight = engine.advance_slab_power(slab, 32)
    assert weight == 32
    reference = endpoint
    for _ in range(32):
        reference = engine.advance(reference).target
    assert advanced.current_pair().values() == reference.values()
    metrics = engine.metrics()
    assert metrics.primitive_slab_steps == 20
    assert metrics.nonlinear_branch_evaluations == 12
    assert metrics.slab_jump_entries > 0

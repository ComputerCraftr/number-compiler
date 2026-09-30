from __future__ import annotations

from typing import TYPE_CHECKING

from devtools.verification.reverse_spacetime import (
    ReverseAddCausalSpacetimeEngine,
    ReverseAddPairField,
)

if TYPE_CHECKING:
    from devtools.verification.reverse_spacetime import ReverseAddCarrySlab


def _boot(seed: int) -> ReverseAddCarrySlab:
    engine = ReverseAddCausalSpacetimeEngine(base=10)
    return engine.bootstrap_slab(ReverseAddPairField.from_value(seed, base=10))[0]


def test_distinct_carry_histories_alias_through_exact_occurrence_not_provenance() -> (
    None
):
    # These two valid H=20 certificates are different but reconstruct the same
    # exact current pair occurrence.  Raw history provenance must not survive.
    left = _boot(95)
    right = _boot(104)
    assert left.canonical_key != right.canonical_key
    assert left.current_pair().values() == right.current_pair().values()
    assert left.current_pair().values() == (17, 4, 15, 8, 12, 12, 8, 15, 4, 17)

    engine = ReverseAddCausalSpacetimeEngine(base=10)
    a = engine.forcing_image(left)
    b = engine.forcing_image(right)
    assert a is b
    assert a.occurrence_key == b.occurrence_key
    metrics = engine.forcing.metrics()
    assert metrics.forcing_occurrences == 1
    assert metrics.source_entries == 2
    assert metrics.history_aliases == 1


def test_affine_action_class_aliases_distinct_exact_pair_payloads_safely() -> None:
    # Pair 2 and pair 4 have the same one-step event/growth operator S' = 2S,
    # but they are not the same exact state.  They must share ActionID while
    # retaining distinct occurrence payloads and exact targets.
    engine = ReverseAddCausalSpacetimeEngine(base=10)
    two = engine.forcing_image(ReverseAddPairField.from_pair((2,), base=10))
    four = engine.forcing_image(ReverseAddPairField.from_pair((4,), base=10))

    assert two.forcing is four.forcing
    assert two.occurrence_key != four.occurrence_key
    assert engine.forcing.metrics().action_aliases >= 1

    two_target, weight_two = engine.advance_forcing_power(two, 1)
    four_target, weight_four = engine.advance_forcing_power(four, 1)
    assert weight_two == weight_four == 1
    assert engine.forcing.pair_values(two_target) == (4,)
    assert engine.forcing.pair_values(four_target) == (8,)


def test_forcing_history_morphism_commutes_with_one_reverse_add_successor() -> None:
    engine = ReverseAddCausalSpacetimeEngine(base=10)
    for seed in (95, 104, 196, 4994):
        slab, endpoint = engine.bootstrap_slab(
            ReverseAddPairField.from_value(seed, base=10)
        )
        image = engine.forcing_image(slab)
        assert engine.forcing.pair_values(image) == endpoint.values()

        successor_slab, weight = engine.advance_slab_power(slab, 1)
        assert weight == 1
        successor_image = engine.forcing_image(successor_slab)
        exact = engine.advance(endpoint).target
        assert engine.forcing.pair_values(successor_image) == exact.values()


def test_slab_endpoint_memo_preserves_distinct_histories_under_equal_pair_images() -> (
    None
):
    left = _boot(95)
    right = _boot(104)
    engine = ReverseAddCausalSpacetimeEngine(base=10)

    a, _ = engine.advance_slab_power(left, 1)
    after_first = engine.metrics()
    b, _ = engine.advance_slab_power(right, 1)
    after_second = engine.metrics()

    assert a.current_pair().values() == b.current_pair().values()
    assert a.canonical_key != b.canonical_key
    assert a.carries[:-1] == left.carries[1:]
    assert b.carries[:-1] == right.carries[1:]
    # Old rows remain part of the exact requested certificate until H steps.
    # Only the nonlinear and affine actions may alias these pair-equivalent inputs.
    assert after_second.primitive_slab_steps == after_first.primitive_slab_steps + 1
    assert after_second.slab_jump_entries == after_first.slab_jump_entries + 1
    assert after_second.forcing_history_aliases > after_first.forcing_history_aliases
    again, _ = engine.advance_slab_power(left, 1)
    assert again is a
    assert engine.metrics().primitive_slab_steps == after_second.primitive_slab_steps


def test_carry_behavior_is_interned_without_claiming_temporal_state_identity() -> None:
    engine = ReverseAddCausalSpacetimeEngine(base=10)
    slab, _ = engine.bootstrap_slab(ReverseAddPairField.from_value(196, base=10))
    current = slab
    for _ in range(24):
        engine.forcing_image(current)
        current, _ = engine.advance_slab_power(current, 1)
    metrics = engine.metrics()
    assert metrics.forcing_carry_behavior_classes > 0
    assert metrics.forcing_carry_behavior_aliases > 0
    assert metrics.forcing_classes <= metrics.forcing_occurrences
    assert metrics.carry_direction == "lsd-to-msd"


def test_slab_endpoint_memo_discards_history_rows_erased_before_endpoint() -> None:
    left, right = _boot(95), _boot(104)
    engine = ReverseAddCausalSpacetimeEngine(base=10)
    a, _ = engine.advance_slab_power(left, 8)
    after_first = engine.metrics()
    b, _ = engine.advance_slab_power(right, 8)
    assert a is b
    assert engine.metrics().primitive_slab_steps == after_first.primitive_slab_steps
    assert engine.metrics().slab_jump_entries == after_first.slab_jump_entries

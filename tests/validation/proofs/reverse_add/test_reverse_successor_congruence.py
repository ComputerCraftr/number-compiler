"""Exact oracle regression; these objects are not production carriers."""

from devtools.proofs.reverse_spacetime import (
    ReverseAddCausalSpacetimeEngine,
    ReverseAddPairField,
)


def test_reverse_affine_action_alias_is_not_an_exact_temporal_state_quotient() -> None:
    engine = ReverseAddCausalSpacetimeEngine(base=10)
    states = [
        engine.forcing_image(ReverseAddPairField.from_pair((value,), base=10))
        for value in (2, 4, 8)
    ]
    assert len({state.forcing.class_id for state in states}) == 1
    assert len({state.occurrence_key for state in states}) == 3
    assert all(
        state.cache_identity.exact_cache_key[0] == "exact-occurrence"
        for state in states
    )

    for state in states:
        engine.advance_forcing_power(state, 1)
    metrics = engine.metrics()
    # 2->4 and 4->8 still share the next affine class, but 8->16 does not.
    assert metrics.forcing_successor_conflicts >= 1
    assert metrics.forcing_exact_target_conflicts >= 1

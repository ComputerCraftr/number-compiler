from typing import cast

import pytest

from devtools.verification.collatz_spacetime import (
    CollatzCausalSpacetimeEngine,
    CollatzRadixField,
)


def test_low_fixed_point_frames_alias_before_accelerated_cache_lookup() -> None:
    # 11=(23)_4, 45=(231)_4 and 181=(2311)_4 share normalized tail
    # (3,2) in LSD-first order.  Only the removable low 1**q frame differs.
    engine = CollatzCausalSpacetimeEngine()
    images = [
        engine.forcing_image_with_valuation(CollatzRadixField.from_value(value))
        for value in (11, 45, 181)
    ]
    occurrences = [item[0] for item in images]
    assert [item[1] for item in images] == [1, 3, 5]
    # q is gauge/cocycle weight, so all three sources are literally the same
    # normalized occurrence rather than three states with aliased actions.
    assert occurrences[0] is occurrences[1] is occurrences[2]
    assert len({item.forcing.canonical_key for item in occurrences}) == 1
    metrics = engine.forcing.metrics()
    assert metrics.forcing_classes == 1
    assert metrics.source_entries == 3
    assert metrics.normalized_occurrences == 1
    assert metrics.frame_aliases == 2


def test_collatz_frame_morphism_preserves_target_and_valuation_cocycle() -> None:
    for value, valuation in ((11, 1), (45, 3), (181, 5)):
        engine = CollatzCausalSpacetimeEngine()
        target, event = engine.advance_event_power(
            CollatzRadixField.from_value(value),
            1,
        )
        assert target.value() == 17
        assert event.effect.events == 1
        assert event.effect.shift == valuation


def test_collatz_lazy_power_preserves_frame_alias_outputs_without_exact_tail_cache() -> (
    None
):
    engine = CollatzCausalSpacetimeEngine()
    target_a, event_a = engine.advance_event_power(
        CollatzRadixField.from_value(11),
        8,
    )
    after_a = engine.metrics()
    target_b, event_b = engine.advance_event_power(
        CollatzRadixField.from_value(45),
        8,
    )
    after_b = engine.metrics()

    assert target_a.value() == target_b.value()
    # The only path difference is the first source frame: q=0 versus q=1.
    assert event_b.effect.shift == event_a.effect.shift + 2
    assert after_b.primitive_forcing_steps == after_a.primitive_forcing_steps
    assert after_b.forcing_jump_entries == after_a.forcing_jump_entries
    # The powered path retains original sources and lazy programs, not
    # normalized future-tail payloads. Explicit morphism diagnostics above
    # independently verify the original-source gauge equivalence.
    assert after_b.forcing_occurrences == after_a.forcing_occurrences == 0
    assert after_b.symbolic_maximum_port_bits <= 2


def test_crop_alignment_provenance_is_removed_before_interning() -> None:
    # q=0 begins with one level-1 tail tile; q=1 initially crops into two
    # inherited leaves.  The morphism must repack both to the same aligned tile.
    engine = CollatzCausalSpacetimeEngine()
    a = engine.forcing_image(CollatzRadixField.from_value(11))
    b = engine.forcing_image(CollatzRadixField.from_value(45))
    assert a is b
    assert a.forcing is b.forcing
    a_tail = engine.forcing.tail_span(a)
    b_tail = engine.forcing.tail_span(b)
    assert a_tail is not None
    assert b_tail is not None
    assert tuple(chunk.tile for chunk in a_tail.chunks) == tuple(
        chunk.tile for chunk in b_tail.chunks
    )
    assert len(a_tail.chunks) == 1
    assert a_tail.chunks[0].tile.level == 1
    assert a.residue3 == b.residue3


@pytest.mark.parametrize("alias", (True, 1.0))
def test_forcing_morphism_rejects_frame_numeric_alias_before_accounting(
    alias: bool | float,
) -> None:
    engine = CollatzCausalSpacetimeEngine()
    before = engine.forcing.metrics()
    with pytest.raises(TypeError):
        engine.forcing.intern(
            ("invalid-frame",), frame_depth=cast("int", alias), tail=None
        )
    assert engine.forcing.metrics() == before


def test_extensional_action_aliases_different_normalized_tails_without_state_alias() -> (
    None
):
    # 3=(3)_4 and 11=(23)_4 have different exact normalized tails but the
    # complete incoming-carry -> outgoing-carry map of their local-shift block
    # is identical.  They therefore share ActionID while keeping exact payloads.
    engine = CollatzCausalSpacetimeEngine()
    three = engine.forcing_image(CollatzRadixField.from_value(3))
    eleven = engine.forcing_image(CollatzRadixField.from_value(11))
    three_tail = engine.forcing.tail_span(three)
    eleven_tail = engine.forcing.tail_span(eleven)
    assert three_tail is not None and eleven_tail is not None
    assert tuple(chunk.tile for chunk in three_tail.chunks) != tuple(
        chunk.tile for chunk in eleven_tail.chunks
    )
    assert three.forcing is eleven.forcing
    assert three.occurrence_key != eleven.occurrence_key

    target_three, event_three = engine.advance_event_power(
        CollatzRadixField.from_value(3),
        1,
    )
    target_eleven, event_eleven = engine.advance_event_power(
        CollatzRadixField.from_value(11),
        1,
    )
    assert target_three.value() == 5
    assert target_eleven.value() == 17
    assert event_three.effect.shift == event_eleven.effect.shift == 1
    assert engine.metrics().forcing_action_aliases >= 1

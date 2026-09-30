from typing import Never

import pytest

from devtools.verification.carry_action_quotient import CarryActionQuotientArena
from devtools.verification.reverse_action import ReverseAddMacroActionArena
from devtools.verification.reverse_spacetime import (
    ReverseAddCausalSpacetimeEngine,
    ReverseAddPairField,
)
from number_compiler.arithmetic.fields.dyadic_tile import iter_symbols, source_span


def test_carry_quotient_aliases_distinct_fields_with_complete_port_outputs() -> None:
    arena = CarryActionQuotientArena()
    left = source_span((2, 9, 0, 9), blank=0, logical_length=4)
    right = source_span((4, 9, 9, 9), blank=0, logical_length=4)
    a = arena.port_action(left.chunks[0].tile, base=10)
    b = arena.port_action(right.chunks[0].tile, base=10)
    assert a == b
    for incoming in (0, 1):
        result, final = arena.project_span(left, incoming, base=10)
        assert tuple(iter_symbols(result)) == (0, 0, 0, 0)
        assert final == 0


def test_complete_macro_action_composes_associatively_and_applies_exactly() -> None:
    engine = ReverseAddCausalSpacetimeEngine(base=10)
    arena = ReverseAddMacroActionArena(10)
    source = ReverseAddPairField.from_value(196)
    current = source
    ids = []
    for _ in range(3):
        occurrence = engine.forcing_image(current)
        ids.append(arena.primitive(occurrence.action))
        current = engine.advance(current).target
    left = arena.compose(arena.compose(ids[0], ids[1]), ids[2])
    right = arena.compose(ids[0], arena.compose(ids[1], ids[2]))
    assert left == right
    assert arena.apply(left, source.span).tile_ids == current.span.tile_ids


def test_macro_power_retains_only_requested_occurrences_and_counts_branch_work() -> (
    None
):
    engine = ReverseAddCausalSpacetimeEngine(base=10)
    state = engine.forcing_image(ReverseAddPairField.from_value(196))
    target, weight = engine.advance_forcing_power(state, 64)
    metrics = engine.metrics()
    assert weight == 64
    assert metrics.forcing_occurrences == 2
    assert metrics.exact_endpoint_entries == 1
    assert metrics.macro_compositions > 0
    assert metrics.macro_applications == 1
    assert metrics.nonlinear_branch_evaluations == 64
    again, _ = engine.advance_forcing_power(state, 64)
    assert again is target
    assert engine.metrics().nonlinear_branch_evaluations == 64


def test_reset_alias_is_not_used_as_future_branch_state() -> None:
    engine = ReverseAddCausalSpacetimeEngine(base=10)
    a = engine.forcing_image(ReverseAddPairField.from_pair((2,)))
    b = engine.forcing_image(ReverseAddPairField.from_pair((4,)))
    assert a.action is b.action
    aa, _ = engine.advance_forcing_power(a, 3)
    bb, _ = engine.advance_forcing_power(b, 3)
    assert engine.forcing.pair_values(aa) == (16,)
    assert engine.forcing.pair_values(bb) == (7, 7)


def test_cold_action_power_never_applies_intermediate_pair_fields(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    engine = ReverseAddCausalSpacetimeEngine(base=10)
    state = engine.forcing_image(ReverseAddPairField.from_value(196))

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("intermediate pair materialization")

    monkeypatch.setattr(type(engine.forcing_actions), "apply", forbidden)
    engine.advance_forcing_power(state, 64)
    assert engine.metrics().macro_applications == 1


def test_macro_actions_match_exhaustive_small_symmetric_fields() -> None:
    from itertools import product

    from number_compiler.arithmetic.carry.event_memory import pair_step

    for base in (2, 3, 4, 5):
        for width in (1, 2, 3):
            for half in product(range(2 * base - 1), repeat=(width + 1) // 2):
                pair = half + half[: width // 2][::-1]
                expected = pair
                for _ in range(5):
                    expected, _ = pair_step(expected, base)
                engine = ReverseAddCausalSpacetimeEngine(base=base)
                state = engine.forcing_image(
                    ReverseAddPairField.from_pair(pair, base=base)
                )
                target, _ = engine.advance_forcing_power(state, 5)
                assert engine.forcing.pair_values(target) == expected


def test_slab_bootstrap_and_forcing_never_expand_digit_or_carry_vectors(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import devtools.verification.forcing_morphism as forcing_module
    import devtools.verification.reverse_spacetime as reverse_module
    import devtools.verification.temporal_quotient as temporal_module

    engine = ReverseAddCausalSpacetimeEngine(base=10)
    source = ReverseAddPairField.from_value(196)

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("eager vector reconstruction")

    for module in (forcing_module, reverse_module, temporal_module):
        monkeypatch.setattr(module, "iter_symbols", forbidden)
    result = engine.advance_pair_steps(source, 64)
    assert result.span.length > source.span.length


def test_slab_request_powers_actions_then_builds_only_final_bounded_certificate() -> (
    None
):
    engine = ReverseAddCausalSpacetimeEngine(base=10)
    slab, initial = engine.bootstrap_slab(ReverseAddPairField.from_value(196))
    target, weight = engine.advance_slab_power(slab, 64)
    expected_engine = ReverseAddCausalSpacetimeEngine(base=10)
    expected, _ = expected_engine.advance_power(initial, 64)
    assert weight == 64
    assert target.current_pair().span.tile_ids == expected.span.tile_ids
    assert engine.metrics().primitive_slab_steps == 20
    assert engine.metrics().nonlinear_branch_evaluations == 44
    assert engine.metrics().slab_jump_entries == 1
    assert not hasattr(engine, "_slab_lift")
    again, _ = engine.advance_slab_power(slab, 64)
    assert again is target
    assert engine.metrics().primitive_slab_steps == 20


def test_requested_endpoint_memos_honor_configured_capacity() -> None:
    for capacity in (0, 1):
        engine = ReverseAddCausalSpacetimeEngine(base=10, max_jump_entries=capacity)
        slab, _ = engine.bootstrap_slab(ReverseAddPairField.from_value(196))
        state = engine.forcing_image(slab)
        engine.advance_forcing_power(state, 3)
        engine.advance_forcing_power(state, 4)
        engine.advance_slab_power(slab, 3)
        engine.advance_slab_power(slab, 4)
        assert engine.metrics().exact_endpoint_entries == capacity
        assert engine.metrics().slab_jump_entries == capacity

from __future__ import annotations

from typing import Never

import pytest

from devtools.verification.collatz_spacetime import (
    CollatzCausalSpacetimeEngine,
    CollatzPhysicalField,
    CollatzRadixField,
)
from number_compiler.arithmetic.fields.causal_domain import (
    CanonicalDomainArena,
    CarryDirection,
    DomainCell,
    reverse_pair_codec,
)
from number_compiler.arithmetic.fields.dyadic_tile import (
    mirror_span,
    prefix_domain_span,
    source_span,
    tile_metrics,
)
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def _accelerated(value: int) -> tuple[int, int]:
    numerator = 3 * int(value) + 1
    valuation = (numerator & -numerator).bit_length() - 1
    return numerator >> valuation, valuation


def test_domain_extent_is_geometry_not_a_length_bearing_cell_identity() -> None:
    huge = (1 << 40) + 12345
    frame = prefix_domain_span(huge - 7, huge)
    leaf_symbols: set[int] = set()
    seen: set[int] = set()
    stack = [chunk.tile for chunk in frame.chunks]
    while stack:
        tile = stack.pop()
        if tile.node_id in seen:
            continue
        seen.add(tile.node_id)
        if tile.level == 0:
            assert tile.symbol is not None
            leaf_symbols.add(tile.symbol)
        else:
            assert tile.left is not None and tile.right is not None
            stack.extend((tile.left, tile.right))
    assert leaf_symbols == {0, 1}
    metrics = tile_metrics(frame)
    assert metrics["forest_chunks"] <= 4 * huge.bit_length()

    codec = reverse_pair_codec(10)
    assert codec.alphabet_size == 20  # 19 active pair sums + one inactive exterior
    assert codec.cell(0) == DomainCell(codec.family, True, 0)
    assert codec.cell(18) == DomainCell(codec.family, True, 18)
    assert codec.cell(19).active is False


def test_domain_canonicalization_uses_causal_mirror_conjugacy_without_reversing_carry() -> (
    None
):
    codec = reverse_pair_codec(10)
    arena = CanonicalDomainArena(codec)
    source = source_span((2, 5, 11, 17, 8, 1), blank=0, logical_length=6)
    mirrored = mirror_span(source, rebase_to_zero=True)
    left = tuple(
        arena.canonical_ref(chunk.tile).tile.node_id for chunk in source.chunks
    )
    # Canonical representatives need not have the same forest partition after a
    # non-power-of-two reflection.  What must remain fixed is causal direction.
    for chunk in mirrored.chunks:
        arena.canonical_ref(chunk.tile)
    assert arena.carry_direction is CarryDirection.TOWARD_MSD
    assert arena.metrics()["carry_direction"] == "lsd-to-msd"
    assert left


@pytest.mark.validation  # N=64 endpoint-coordinate matrix with lowering poisoned.
def test_reverse_powered_point_normalizes_only_the_target_digit(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # A point query may build the exact temporal pair field, but terminal radix
    # normalization must remain a dyadic prefix/action query rather than
    # materializing the complete terminal digit span.
    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("full terminal digit projection used for point query")

    monkeypatch.setattr(ReverseAddPoweredTerm, "digits", forbidden)
    monkeypatch.setattr(ReverseAddPoweredTerm, "materialize", forbidden)
    term = ReverseAddPoweredTerm(196, 64)
    scalar = 196
    for _ in range(64):
        scalar += int(str(scalar)[::-1])
    expected = tuple(map(int, str(scalar)[::-1]))
    for position in (0, len(expected) // 2, len(expected) - 1):
        assert term.digit(position) == expected[position]
    assert term.width() == len(expected)
    assert term.metrics().spacetime_carry_direction == "lsd-to-msd"
    assert term.metrics().spacetime_terminal_projection_entries == 0


def test_collatz_spacetime_one_event_is_canonical_field_arithmetic_without_scalar_materialization(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # value() is an explicit materialization boundary.  One causal event must not
    # use it internally.
    def forbidden_value(_self: CollatzRadixField) -> int:
        raise AssertionError("materialized scalar inside causal event")

    monkeypatch.setattr(CollatzRadixField, "value", forbidden_value)
    for value in (3, 5, 7, 9, 27, 31, 127, 255, 341, 999, 65535):
        engine = CollatzCausalSpacetimeEngine()
        field = CollatzRadixField.from_value(value)
        step = engine.advance(field)
        expected, valuation = _accelerated(value)
        assert step.valuation == valuation
        # Compare through digits without calling the monkeypatched value().
        got = sum(digit * (4**i) for i, digit in enumerate(step.target.digits()))
        assert got == expected
        metrics = engine.metrics()
        assert metrics.carry_direction == "lsd-to-msd"
        assert metrics.finite_cell_alphabet == 5


def test_collatz_event_dag_is_built_from_canonical_field_steps_not_whole_germs(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.sequences.collatz.germ_cache as old_germs

    def forbidden_advance(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("whole-germ advance used")

    monkeypatch.setattr(
        old_germs.CollatzGermTransitionCache, "advance", forbidden_advance
    )
    engine = CollatzCausalSpacetimeEngine()
    field = CollatzRadixField.from_value(27)
    target, event = engine.advance_event_power(field, 64)
    value = 27
    valuation_sum = 0
    for _ in range(64):
        value, valuation = _accelerated(value)
        valuation_sum += valuation
    assert target.value() == value
    assert event.effect.events == 64
    assert event.effect.shift == valuation_sum
    metrics = engine.metrics()
    # The branch observer still discovers 41 valuations, but no intermediate
    # exact tail is projected or used as a temporal power-cache identity.
    assert metrics.primitive_field_steps == 0
    assert metrics.primitive_forcing_steps == 0
    assert metrics.nonlinear_branch_evaluations == 41
    assert metrics.binary_lift.step_evaluations == 41
    assert metrics.exact_endpoint_entries == 1
    assert metrics.macro_actions > metrics.forcing_classes
    assert metrics.forcing_occurrences == 0
    assert metrics.event_nodes < 128


def test_collatz_fixed_field_power_is_logarithmic_after_canonical_repetition() -> None:
    engine = CollatzCausalSpacetimeEngine()
    target, event = engine.advance_event_power(CollatzRadixField.from_value(1), 1 << 30)
    assert target.value() == 1
    assert event.effect.events == 1 << 30
    metrics = engine.metrics()
    assert metrics.primitive_field_steps == 0
    assert metrics.primitive_forcing_steps == 0
    assert metrics.nonlinear_branch_evaluations == 0
    assert metrics.binary_lift.jump_entries <= 31


def test_collatz_physical_time_field_matches_scalar_and_weights_odd_events() -> None:
    for seed in (1, 2, 3, 7, 27, 31, 100, 999):
        field = CollatzPhysicalField.from_value(seed)
        scalar = seed
        for steps in (1, 2, 5, 17):
            local = CollatzCausalSpacetimeEngine()
            target, weight = local.advance_physical_power(field, steps)
            value = scalar
            odd = 0
            for _ in range(steps):
                odd += value & 1
                value = 3 * value + 1 if value & 1 else value // 2
            assert target.value() == value
            assert weight == (steps, odd)
            assert local.metrics().primitive_field_steps == 0
            assert local.metrics().primitive_physical_steps <= steps

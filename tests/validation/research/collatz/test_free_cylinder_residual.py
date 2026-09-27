from __future__ import annotations

import pytest

from devtools.experiments.collatz.free_cylinder_consumers import _ConsumerAction
from devtools.experiments.collatz.free_cylinder_residual import (
    FreeCylinderResidualArena,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.sequences.collatz.hensel_cylinders import HenselAffineBlock


def _advance(source: int, events: int) -> tuple[int, int]:
    value = source
    ticks = 0
    for _ in range(events):
        numerator = 3 * value + 1
        valuation = (numerator & -numerator).bit_length() - 1
        value = numerator >> valuation
        ticks += 1 + valuation
    return value, ticks


def _advance_physical(source: int, ticks: int) -> tuple[int, int]:
    value = source
    events = 0
    for _ in range(ticks):
        if value & 1:
            value = 3 * value + 1
            events += 1
        else:
            value //= 2
    return value, events


def test_primitive_predicate_derives_every_bounded_source_valuation() -> None:
    arena = FreeCylinderResidualArena(max_precision=32)
    primitive = arena.primitive(12)
    assert arena.metrics(primitive)["max_source_bits"] == 10
    for source in range(1, 1 << 10, 2):
        expected, ticks = _advance(source, 1)
        bound = arena.bind(primitive, source)
        assert (bound.target, bound.accelerated_events, bound.physical_ticks) == (
            expected,
            1,
            ticks,
        )


def test_composition_pulls_predicate_back_without_applying_a_midpoint(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena = FreeCylinderResidualArena(max_precision=32)
    primitive = arena.primitive(12)
    with monkeypatch.context() as poison:

        def forbidden(*_args: object, **_kwargs: object) -> None:
            raise AssertionError("cylinder composition applied a concrete midpoint")

        poison.setattr(HenselAffineBlock, "apply_exact", forbidden)
        two_events = arena.compose(primitive, primitive)
        selected = arena.select(
            two_events,
            source_bits=8,
            source_bit=lambda bit: (129 >> bit) & 1,
        )
    assert selected.accelerated_events == 2
    for source in range(1, 1 << 9, 2):
        expected, ticks = _advance(source, 2)
        bound = arena.bind(two_events, source)
        assert (bound.target, bound.physical_ticks) == (expected, ticks)


def test_temporal_parenthesization_has_one_canonical_residual_id() -> None:
    arena = FreeCylinderResidualArena(max_precision=32)
    primitive = arena.primitive(10)
    two_events = arena.compose(primitive, primitive)
    left = arena.compose(two_events, primitive)
    right = arena.compose(primitive, two_events)
    assert left is right
    assert arena.intern_hits >= 1
    for source in range(1, 1 << 6, 2):
        expected, ticks = _advance(source, 3)
        bound = arena.bind(left, source)
        assert (bound.target, bound.physical_ticks) == (expected, ticks)


def test_dyadic_temporal_power_uses_one_primitive_and_source_binding(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena = FreeCylinderResidualArena(max_precision=64)
    action = arena.primitive(12)
    with monkeypatch.context() as poison:

        def forbidden(*_args: object, **_kwargs: object) -> None:
            raise AssertionError(
                "temporal squaring reconstructed a primitive or midpoint"
            )

        poison.setattr(FreeCylinderResidualArena, "primitive", forbidden)
        poison.setattr(HenselAffineBlock, "apply_exact", forbidden)
        for _ in range(3):
            action = arena.compose(action, action)
    metrics = arena.metrics(action)
    assert metrics["accelerated_events"] == 8
    assert metrics["max_source_bits"] == 3
    # The bounded endpoint function is tiny.  The guard trie avoids the old
    # 4,739 Cartesian checks, but its visited-prefix work is still measured so
    # endpoint reduction cannot be mistaken for a cold logarithmic bound.
    assert metrics["branches"] <= 4
    assert metrics["predicate_bits"] <= 3
    assert metrics["decision_internal_nodes"] <= 4
    assert metrics["branch_pair_checks"] <= 98
    assert metrics["guard_node_visits"] <= 368
    assert metrics["cartesian_pair_upper_bound"] <= 1132
    assert arena.primitive_constructions == 1
    assert arena.temporal_compositions == 3
    for source in range(1, 1 << 3, 2):
        expected, ticks = _advance(source, 8)
        bound = arena.bind(action, source)
        assert (bound.target, bound.physical_ticks) == (expected, ticks)


def test_source_bit_callback_is_lazy_and_memoized() -> None:
    arena = FreeCylinderResidualArena(max_precision=32)
    action = arena.compose(arena.primitive(10), arena.primitive(10))
    calls: list[int] = []

    def source_bit(bit: int) -> int:
        calls.append(bit)
        return (27 >> bit) & 1

    selected = arena.select(action, source_bits=5, source_bit=source_bit)
    assert calls
    assert len(calls) == len(set(calls))
    assert all(0 <= bit < 5 for bit in calls)
    assert len(calls) <= arena.metrics(action)["predicate_bits"]
    assert selected.apply_exact(27) == _advance(27, 2)[0]


def test_source_conditioned_physical_power_has_exact_ticks_and_event_weight(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena = FreeCylinderResidualArena(max_precision=64)
    with monkeypatch.context() as poison:

        def forbidden(*_args: object, **_kwargs: object) -> None:
            raise AssertionError("physical constructor evaluated a midpoint")

        poison.setattr(HenselAffineBlock, "apply_exact", forbidden)
        action = arena.power_physical(8, 5)
    metrics = arena.metrics(action)
    assert metrics["physical_ticks"] == 8
    assert metrics["max_source_bits"] == 5
    for source in range(1, 1 << 5):
        expected, events = _advance_physical(source, 8)
        bound = arena.bind(action, source)
        assert (bound.target, bound.physical_ticks, bound.accelerated_events) == (
            expected,
            8,
            events,
        )


def test_guard_consumption_preserves_output_and_clock_projection_aliases() -> None:
    arena = FreeCylinderResidualArena(max_precision=64)
    action = arena.power_physical(16, 5)
    metrics = arena.metrics(action)
    assert metrics["consumer_output_ids"] == 8
    assert metrics["weighted_consumer_ids"] == 10
    assert metrics["weighted_consumer_ids"] < (1 << 5) - 1
    # These aliases are output/clock projections, not support-program identity.
    assert metrics["support_consumer_ids"] == 31


def test_consumer_relative_moore_projection_removes_support_only_distinctions() -> None:
    arena = FreeCylinderResidualArena(max_precision=64)
    action = arena.power_physical(16, 5)
    support = arena.moore_projection(action, "support")
    weighted = arena.moore_projection(action, "endpoint-clock")
    endpoint = arena.moore_projection(action, "endpoint")

    assert endpoint.dag_nodes < weighted.dag_nodes < support.dag_nodes
    assert endpoint.metrics.terminals == 8
    assert weighted.metrics.terminals == 10
    assert support.metrics.terminals == 31
    assert endpoint.certificate().classes < weighted.certificate().classes
    assert weighted.certificate().classes < support.certificate().classes

    for source in range(1, 1 << 5):
        full = support.evaluate(source)
        assert type(full) is _ConsumerAction
        assert endpoint.evaluate(source) == full.output
        assert weighted.evaluate(source) == (
            full.output,
            full.event_weight,
            full.physical_ticks,
        )


def test_spatial_moore_projection_is_already_derivative_minimal() -> None:
    arena = FreeCylinderResidualArena(max_precision=64)
    action = arena.power_physical(16, 5)
    for observation in ("endpoint", "endpoint-clock", "support"):
        projection = arena.moore_projection(action, observation)
        certificate = projection.certificate()
        assert certificate.classes == certificate.reachable_states
        assert projection.derivative(0b101, 3)[0] == 3


def test_sparse_constant_image_powers_without_rebuilding_the_primitive(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena = FreeCylinderResidualArena(max_precision=2048)
    arena.power_physical(16, 5)
    with monkeypatch.context() as poison:

        def forbidden(*_args: object, **_kwargs: object) -> None:
            raise AssertionError("sparse continuation rebuilt the spatial primitive")

        poison.setattr(FreeCylinderResidualArena, "physical_primitive", forbidden)
        action = arena.power_physical(1024, 5)
    metrics = arena.metrics(action)
    assert metrics["consumer_output_ids"] == 3
    assert metrics["weighted_consumer_ids"] == 7
    assert metrics["support_consumer_ids"] == 31
    assert metrics["support_arena_nodes"] < 512
    assert metrics["max_transport_offset_bits"] == 0
    assert metrics["future_endpoint_consumptions"] == 471
    assert metrics["original_source_bit_probes"] == 0
    for source in range(1, 1 << 5):
        expected, events = _advance_physical(source, 1024)
        bound = arena.bind(action, source)
        assert (bound.target, bound.accelerated_events) == (expected, events)


def test_moore_certificate_limits_and_failed_publication() -> None:
    arena = FreeCylinderResidualArena(max_precision=64)
    action = arena.power_physical(16, 5)
    projection = arena.moore_projection(action, "endpoint")
    assert projection is arena.moore_projection(action, "endpoint")
    with pytest.raises(BlockContextBudgetExceeded, match="state budget"):
        projection.certificate(max_states=1)
    assert projection.dag_nodes == 29
    assert projection.certificate().classes == 32
    retained = arena._moore_retained_nodes
    arena.max_branches = retained
    with pytest.raises(BlockContextBudgetExceeded, match="retention budget"):
        arena.moore_projection(action, "endpoint-clock")
    assert arena._moore_retained_nodes == retained
    assert len(arena._moore_projections) == 1


def test_moore_derivative_respects_declared_coordinate_order() -> None:
    from devtools.experiments.collatz.free_cylinder_moore import (
        CollatzSpatialMooreProjection,
    )
    from number_compiler.arithmetic.functions.decision import MultiTerminalDecisionArena

    arena = MultiTerminalDecisionArena((2, 2), order=(1, 0))
    root = arena.build(lambda values: 2 * values[0] + values[1])
    projection = CollatzSpatialMooreProjection("endpoint", arena, root)
    depth, derivative = projection.derivative(1, 1)
    assert depth == 1
    assert arena.evaluate(derivative, (0, 0)) == 1
    assert arena.evaluate(derivative, (1, 0)) == 3
    assert projection.certificate().classes == 7

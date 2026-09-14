"""Arbitrary future-prefix observers cannot become a retained bit tape."""

from __future__ import annotations

from devtools.proofs.lazy_collatz import CollatzLazyView, LazyCollatzApplication


def application() -> tuple[LazyCollatzApplication, CollatzLazyView, int]:
    seed = (1 << 95) + 0x123456789ABCDEF12345
    source = tuple((seed >> position) & 1 for position in range(seed.bit_length()))
    engine = LazyCollatzApplication(2, 1, source)
    view = engine.advance_physical(1).view
    return engine, view, 3 * seed + 1


def test_adaptive_last_one_prefix_queries_do_not_retain_general_future_inverse() -> (
    None
):
    engine, view, expected = application()
    for width in range(1, view.width + 1):
        prefix = CollatzLazyView(view.source, view.program, width, False)
        summary = engine.range_summary(prefix)
        assert (summary.last_one == width - 1) == bool((expected >> (width - 1)) & 1)
    rows = {
        key.width: value
        for key, value in engine._summaries.items()
        if key.program == view.program
    }
    assert not rows
    # Reusable aligned dyadic carry effects remain; removing them would hide
    # the distinct arbitrary-prefix problem by discarding the permitted image.
    assert any(key.program == view.program for key in engine._range_evaluator._ranges)
    assert all(
        key.start % key.length == 0 and key.length >= 8
        for key in engine._range_evaluator._ranges
    )


def test_future_mul3_prefix_observations_are_transient_but_source_can_reuse() -> None:
    engine, view, _ = application()
    for width in range(1, 17):
        prefix = CollatzLazyView(view.source, view.program, width, False)
        engine.mul3_summary(prefix)
    assert not any(key.program == view.program for key in engine._mul3_summaries)
    source_summary = engine.range_summary(engine.initial)
    source_transfer = engine.mul3_summary(engine.initial)
    assert engine.range_summary(engine.initial) is source_summary
    assert engine.mul3_summary(engine.initial) == source_transfer
    assert all(key.program == engine.initial.program for key in engine._summaries)
    assert all(key.program == engine.initial.program for key in engine._mul3_summaries)


def test_arbitrary_future_event_prefixes_are_not_retained() -> None:
    engine, view, _ = application()
    evaluator = engine._range_evaluator
    for width in range(1, 17):
        result = evaluator.event_summary(view.program, width)
        assert result.length == width + 2
    assert not any(key.program == view.program for key in evaluator._events)
    result = evaluator.event_summary(engine.initial.program, engine.initial.width)
    assert (
        evaluator.event_summary(engine.initial.program, engine.initial.width) is result
    )


def test_event_extension_reuses_program_endpoint_and_exact_cocycle() -> None:
    engine, _, _ = application()
    first = engine.advance_events(3)
    before = engine.branch_evaluations
    second = engine.advance_events(4)
    assert engine.branch_evaluations == before + 1
    assert second.valuations[:3] == first.valuations
    independent, _, _ = application()
    full = independent.advance_events(4)
    assert second.valuations == full.valuations
    assert second.view.width == full.view.width
    for position in range(second.view.width):
        assert engine.view_point(second.view, position) == independent.view_point(
            full.view, position
        )


def test_event_extension_preserves_compressed_fixed_cycle_weights() -> None:
    engine = LazyCollatzApplication(2, 0, (1,))
    first = engine.advance_events(7)
    second = engine.advance_events(10)
    assert first.repeated_twos == 7
    assert second.repeated_twos == 10
    assert second.valuations == ()
    assert second.view.program == first.view.program
